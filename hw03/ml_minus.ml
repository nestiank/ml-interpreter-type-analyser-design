type program = exp
and exp = 
  | UNIT
  | TRUE
  | FALSE
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | NIL
  | CONS of exp * exp
  | APPEND of exp * exp
  | HEAD of exp
  | TAIL of exp
  | ISNIL of exp
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | LETMREC of (var * var * exp) * (var * var * exp) * exp
  | PROC of var * exp
  | CALL of exp * exp
  | PRINT of exp
  | SEQ of exp * exp
and var = string

type value = 
  | Unit
  | Int of int
  | Bool of bool
  | List of value list
  | Procedure of var * exp * env
  | RecProcedure of var * var * exp * env
  | MRecProcedure of (var * var * exp) * (var * var * exp) * env
and env = (var * value) list

let rec fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
= fun f accu lst ->
  match lst with
  | [] -> accu
  | hd::tl -> fold_left f (f accu hd) tl

let rec map : ('a -> 'b) -> 'a list -> 'b list
= fun f lst ->
  match lst with
  | [] -> []
  | hd::tl -> (f hd)::(map f tl)

let rec string_of_value v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | List lst -> "[" ^ fold_left (fun s x -> s ^ ", " ^ x) "" (map string_of_value lst) ^ "]"
  | _ -> "(functional value)"

exception UndefinedSemantics

let empty_env = []
let extend_env (x,v) e = (x,v)::e
let rec lookup_env x e = 
  match e with
  | [] -> raise (Failure ("variable " ^ x ^ " is not bound in env"))
  | (y, v)::tl -> if x = y then v else lookup_env x tl

let rec eval : exp -> env -> value
= fun exp env ->
  match exp with
  | UNIT -> Unit
  | TRUE -> Bool true
  | FALSE -> Bool false
  | CONST a -> Int a
  | VAR a -> lookup_env a env
  | ADD (a, b) ->
    (match (eval a env), (eval b env) with
    | Int n, Int m -> Int (n + m)
    | _ -> raise UndefinedSemantics)
  | SUB (a, b) ->
    (match (eval a env), (eval b env) with
    | Int n, Int m -> Int (n - m)
    | _ -> raise UndefinedSemantics)
  | MUL (a, b) ->
    (match (eval a env), (eval b env) with
    | Int n, Int m -> Int (n * m)
    | _ -> raise UndefinedSemantics)
  | DIV (a, b) ->
    (match (eval a env), (eval b env) with
    | Int n, Int 0 -> raise UndefinedSemantics
    | Int n, Int m -> Int (n / m)
    | _ -> raise UndefinedSemantics)
  | EQUAL (a, b) ->
    (match (eval a env), (eval b env) with
    | Int n, Int m -> Bool (n = m)
    | Bool x, Bool y -> Bool (x = y)
    | _ -> raise UndefinedSemantics)
  | LESS (a, b) ->
    (match (eval a env), (eval b env) with
    | Int n, Int m -> Bool (n < m)
    | _ -> raise UndefinedSemantics)
  | NOT a ->
    (match eval a env with
    | Bool x -> Bool (not x)
    | _ -> raise UndefinedSemantics)
  | NIL -> List []
  | CONS (a, b) ->
    (match (eval a env), (eval b env) with
    | x, List y -> List (x::y)
    | _ -> raise UndefinedSemantics)
  | APPEND (a, b) ->
    (match (eval a env), (eval b env) with
    | List x, List y -> List (x @ y)
    | _ -> raise UndefinedSemantics)
  | HEAD a ->
    (match eval a env with
    | List (hd::tl) -> hd
    | _ -> raise UndefinedSemantics)
  | TAIL a ->
    (match eval a env with
    | List (hd::tl) -> List tl
    | _ -> raise UndefinedSemantics)
  | ISNIL a ->
    (match eval a env with
    | List [] -> Bool true
    | List _ -> Bool false
    | _ -> raise UndefinedSemantics)
  | IF (a, b, c) ->
    (match eval a env with
    | Bool true -> eval b env
    | Bool false -> eval c env
    | _ -> raise UndefinedSemantics)
  | LET (a, b, c) -> eval c (extend_env (a, (eval b env)) env)
  | LETREC (a, b, c, d) -> eval d (extend_env (a, RecProcedure(a, b, c, env)) env)
  | LETMREC ((a, b, c), (d, e, f), g) ->
    let d_env = (extend_env (d, MRecProcedure((d, e, f), (a, b, c), env)) env) in
    let a_d_env = (extend_env (a, MRecProcedure((a, b, c), (d, e, f), env)) d_env) in
    eval g a_d_env
  | PROC (a, b) -> Procedure (a, b, env)
  | CALL (a, b) ->
    (match eval a env with
    | Procedure (x, y, e) -> eval y (extend_env (x, (eval b env)) e)
    | RecProcedure (f, x, y, e) ->
      let f_e = (extend_env (f, (RecProcedure(f, x, y, e))) e) in
      let x_f_e = (extend_env (x, eval b env) f_e) in
      eval y x_f_e
    | MRecProcedure ((f, x, y), (g, p, q), e) ->
      let g_e = (extend_env (g, MRecProcedure((g, p, q), (f, x, y), e)) e) in
      let f_g_e = (extend_env (f, MRecProcedure((f, x, y), (g, p, q), e)) g_e) in
      let x_f_g_e = (extend_env (x, eval b env) f_g_e) in
      eval y x_f_g_e
    | _ -> raise UndefinedSemantics)
  | PRINT a -> (print_endline (string_of_value (eval a env)); Unit)
  | SEQ (a, b) -> eval a env; eval b env

let runml : program -> value
= fun pgm -> eval pgm empty_env;;
