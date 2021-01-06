type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp                 (* sequence *)
  | IF of exp * exp * exp            (* if-then-else *)
  | WHILE of exp * exp               (* while loop *)
  | LETV of id * exp * exp           (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list           (* call by value *)
  | CALLR of id * id list            (* call by referenece *)
  | RECORD of (id * exp) list        (* record construction *)
  | FIELD of exp * id                (* access record field *)
  | ASSIGN of id * exp               (* assgin to variable *)
  | ASSIGNF of exp * id * exp        (* assign to record field *)
  | WRITE of exp
and id = string

type loc = int
type value =
| Num of int
| Bool of bool
| Unit
| Record of record
and record = (id * loc) list
type memory = (loc * value) list
type env = binding list
and binding = LocBind of id * loc | ProcBind of id * proc
and proc = id list * exp * env

(********************************)
(*     Handling environment     *)
(********************************)

let rec lookup_loc_env : id -> env -> loc
= fun x env ->
  match env with
  | [] -> raise (Failure ("Variable " ^ x ^ " is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind (id, l) -> if x = id then l else lookup_loc_env x tl
    | ProcBind _ -> lookup_loc_env x tl
    end

let rec lookup_proc_env : id -> env -> proc
= fun x env ->
  match env with
  | [] -> raise (Failure ("Variable " ^ x ^ " is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind _ -> lookup_proc_env x tl
    | ProcBind (id, binding) -> if x = id then binding else lookup_proc_env x tl
    end

let extend_env : binding -> env -> env
= fun e env -> e::env

let empty_env = []

(***************************)
(*     Handling memory     *)
(***************************)

let rec lookup_mem : loc -> memory -> value
= fun l mem ->
  match mem with
  | [] -> raise (Failure ("location " ^ (string_of_int l) ^ " is not included in memory"))
  | (loc, v)::tl -> if l = loc then v else lookup_mem l tl

let extend_mem : (loc * value) -> memory -> memory
= fun (l, v) mem -> (l, v)::mem

let empty_mem = []

(***************************)
(*     Handling record     *)
(***************************)

let rec lookup_record : id -> record -> loc
= fun id record ->
  match record with
    | [] -> raise (Failure ("field " ^ id ^ " is not included in record"))
    | (x, l)::tl -> if id = x then l else lookup_record id tl

let extend_record : (id * loc) -> record -> record
= fun (x, l) record -> (x, l)::record

let empty_record = []

(***************************)

let counter = ref 0
let new_location () = counter := !counter + 1; !counter

exception NotImplemented
exception UndefinedSemantics

let rec list_fold2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
= fun func l1 l2 acc ->
  match (l1, l2) with
  | ([], []) -> acc
  | (hd1::tl1, hd2::tl2) -> list_fold2 func tl1 tl2 (func hd1 hd2 acc)
  | _ -> raise (Failure "two lists have different length")

let rec list_fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
= fun func l acc ->
  match l with
  | [] -> acc
  | hd::tl -> list_fold func tl (func hd acc)

let value2str : value -> string
= fun v ->
  match v with
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "unit"
  | Record _ -> "record"

let rec eval_aop : env -> memory -> exp -> exp -> (int -> int -> int) -> (value * memory)
= fun env mem e1 e2 op ->
  let (v1, mem1) = eval env mem e1 in
  let (v2, mem2) = eval env mem1 e2 in
  match (v1, v2) with
  | (Num n1, Num n2) -> (Num (op n1 n2), mem2)
  | _ -> raise (Failure "arithmetic operation type error")

and eval : env -> memory -> exp -> (value * memory)
= fun env mem e ->
  match e with
  | NUM a -> (Num a, mem)
  | TRUE -> (Bool true, mem)
  | FALSE -> (Bool false, mem)
  | UNIT -> (Unit, mem)
  | VAR a -> ((lookup_mem (lookup_loc_env a env) mem), mem)
  | ADD (a, b) -> eval_aop env mem a b (fun a b -> a + b)
  | SUB (a, b) -> eval_aop env mem a b (fun a b -> a - b)
  | MUL (a, b) -> eval_aop env mem a b (fun a b -> a * b)
  | DIV (a, b) ->
    let (v, b_mem) = eval env mem b in
    begin match v with
    | Num 0 -> raise UndefinedSemantics
    | _ -> eval_aop env mem a b (fun a b -> a / b) end
  | EQUAL (a, b) ->
    let (u, a_mem) = eval env mem a in
    let (v, b_a_mem) = eval env a_mem b in
    begin match u, v with
    | Num n, Num m -> (Bool (n = m), b_a_mem)
    | Bool x, Bool y -> (Bool (x = y), b_a_mem)
    | Unit, Unit -> (Bool true, b_a_mem)
    | _ -> (Bool false, b_a_mem) end
  | LESS (a, b) ->
    let (u, a_mem) = eval env mem a in
    let (v, b_a_mem) = eval env a_mem b in
    begin match u, v with
    | Num n, Num m -> (Bool (n < m), b_a_mem)
    | _ -> raise UndefinedSemantics end
  | NOT a ->
    let (u, a_mem) = eval env mem a in
    begin match u with
    | Bool x -> (Bool (not x), a_mem)
    | _ -> raise UndefinedSemantics end
  | SEQ (a, b) ->
    let (u, a_mem) = eval env mem a in
    let (v, b_a_mem) = eval env a_mem b in
    (v, b_a_mem)
  | IF (a, b, c) ->
    let (u, a_mem) = eval env mem a in
    begin match u with
    | Bool true -> eval env a_mem b
    | Bool false -> eval env a_mem c
    | _ -> raise UndefinedSemantics end
  | WHILE (a, b) ->
    let (u, a_mem) = eval env mem a in
    begin match u with
    | Bool true ->
      let (v, b_a_mem) = eval env a_mem b in
      eval env b_a_mem (WHILE (a, b))
    | Bool false -> (Unit, a_mem)
    | _ -> raise UndefinedSemantics end
  | LETV (a, b, c) ->
    let (v, b_mem) = eval env mem b in
    let l = new_location () in
    eval (extend_env (LocBind (a, l)) env) (extend_mem (l, v) b_mem) c
  | LETF (a, b, c, d) -> eval (extend_env (ProcBind (a, (b, c, env))) env) mem d
  | CALLV (a, b) ->
    let (u, v, w) = lookup_proc_env a env in
    let (f_b, f_mem) =
      let f = fun x (y, mem) ->
        let (eval_x, x_mem) = eval env mem x in
        (y @ [eval_x], x_mem) in
      list_fold f b ([], mem) in
    let (g_env, g_f_mem) =
      let g = fun x y (env, mem) ->
        let l = new_location () in
        (extend_env (LocBind (x, l)) env, extend_mem (l, y) mem) in
      list_fold2 g u f_b (w, f_mem) in
    eval (extend_env (ProcBind (a, (u, v, w))) g_env) g_f_mem v
  | CALLR (a, b) ->
    let (u, v, w) = lookup_proc_env a env in
    let f_b =
      let f = fun x y -> y @ [lookup_loc_env x env] in
      list_fold f b [] in
    let g_env =
      let g = fun x y env -> extend_env (LocBind (x, y)) env in
      list_fold2 g u f_b w in
    eval (extend_env (ProcBind (a, (u, v, w))) g_env) mem v
  | RECORD a ->
    if a = [] then (Unit, mem)
    else
      let f = fun (x, y) (Record r, mem) ->
        let (v, y_mem) = eval env mem y in
        let l = new_location () in
        (Record (extend_record (x, l) r), extend_mem (l, v) y_mem) in
      list_fold f a (Record [], mem)
  | FIELD (a, b) ->
    let (u, a_mem) = eval env mem a in
    begin match u with
    | Record r -> (lookup_mem (lookup_record b r) a_mem, a_mem)
    | _ -> raise UndefinedSemantics end
  | ASSIGN (a, b) ->
    let (v, b_mem) = eval env mem b in
    (v, (extend_mem ((lookup_loc_env a env), v) b_mem))
  | ASSIGNF (a, b, c) ->
    let (u, a_mem) = eval env mem a in
    begin match u with
    | Record r ->
      let (w, c_a_mem) = eval env a_mem c in
      (w, (extend_mem (lookup_record b r, w) c_a_mem))
    | _ -> raise UndefinedSemantics end
  | WRITE a ->
    let (u, a_mem) = eval env mem a in
    let _ = print_endline(value2str u) in
    (u, a_mem)

let runb : exp -> value
= fun exp -> let (v, _) = eval empty_env empty_mem exp in v;;
