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

exception TypeError

type typ =
  | TyUnit
  | TyInt
  | TyBool
  | TyIntBool of tyvar
  | TyFun of typ * typ
  | TyList of typ
  | TyVar of tyvar
and tyvar = string

let tyvar_num = ref 0
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))
let fresh_ibvar () = (tyvar_num := !tyvar_num + 1; (TyIntBool ("t" ^ string_of_int !tyvar_num)))

(********************
Type equation, type environment, type substitution, program identifier
********************)

type tyeqn = (typ * typ) list
type tyenv = (var * typ) list
type subst = (tyvar * typ) list
type ibenv = (tyvar * typ) list

let empty_tyenv = []
let rec lookup_tyenv : var -> tyenv -> typ
= fun x e ->
  match e with
  | [] -> raise TypeError
  | (y, t)::tl -> if x = y then t else lookup_tyenv x tl

let empty_subst = []
let rec lookup_subst : tyvar -> subst -> typ
= fun t subst ->
  match subst with
  | [] -> TyVar t
  | (x, y)::tl -> if x = t then y else lookup_subst t tl

let empty_ibenv = []
let rec lookup_ibenv : tyvar -> ibenv -> typ
= fun t ibenv ->
  match ibenv with
  | [] -> TyIntBool t
  | (x, y)::tl -> if x = t then y else lookup_ibenv t tl

let identifier = "program"

(********************
Functions
********************)

let rec funcV : tyenv -> exp -> typ -> tyeqn
= fun type_env exp type_est ->
  match exp with
  | UNIT -> [(type_est, TyUnit)]
  | TRUE | FALSE -> [(type_est, TyBool)]
  | CONST a -> [(type_est, TyInt)]
  | VAR a -> [(type_est, lookup_tyenv a type_env)]
  | ADD (a, b) | SUB (a, b) | MUL (a, b) | DIV (a, b) ->
    [(type_est, TyInt)] @ (funcV type_env a TyInt) @ (funcV type_env b TyInt)
  | EQUAL (a, b) ->
    let typeof_a_b = fresh_ibvar () in
    [(type_est, TyBool)] @ (funcV type_env a typeof_a_b) @ (funcV type_env b typeof_a_b)
  | LESS (a, b) -> [(type_est, TyBool)] @ (funcV type_env a TyInt) @ (funcV type_env b TyInt)
  | NOT a -> [(type_est, TyBool)] @ (funcV type_env a TyBool)
  | NIL -> [(type_est, TyList (fresh_tyvar ()))]
  | CONS (a, b) ->
    let typeof_exp_inside = fresh_tyvar () in
    [(type_est, TyList typeof_exp_inside)] @ (funcV type_env a typeof_exp_inside) @ (funcV type_env b (TyList typeof_exp_inside))
  | APPEND (a, b) ->
    let typeof_exp = TyList (fresh_tyvar ()) in
    [(type_est, typeof_exp)] @ (funcV type_env a typeof_exp) @ (funcV type_env b typeof_exp)
  | HEAD a ->
    let typeof_exp = fresh_tyvar () in
    [(type_est, typeof_exp)] @ (funcV type_env a (TyList typeof_exp))
  | TAIL a ->
    let typeof_exp = TyList (fresh_tyvar ()) in
    [(type_est, typeof_exp)] @ (funcV type_env a typeof_exp)
  | ISNIL a -> [(type_est, TyBool)] @ (funcV type_env a (TyList (fresh_tyvar ())))
  | IF (c, x, y) ->
    let typeof_exp = fresh_tyvar () in
    [(type_est, typeof_exp)] @ (funcV type_env c TyBool) @ (funcV type_env x typeof_exp) @ (funcV type_env y typeof_exp)
  | LET (x, xe, e) ->
    let typeof_xe = fresh_tyvar () in
    let typeof_exp = fresh_tyvar () in
    let type_env_ext_e = (x, typeof_xe)::type_env in
    [(type_est, typeof_exp)] @ (funcV type_env xe typeof_xe) @ (funcV type_env_ext_e e typeof_exp)
  | LETREC (f, x, xe, e) ->
    let typeof_x = fresh_tyvar () in
    let typeof_f_result = fresh_tyvar () in
    let typeof_exp = fresh_tyvar () in
    let type_env_ext_e = (f, TyFun (typeof_x, typeof_f_result))::type_env in
    let type_env_ext_xe = (x, typeof_x)::type_env_ext_e in
    [(type_est, typeof_exp)] @ (funcV type_env_ext_xe xe typeof_f_result) @ (funcV type_env_ext_e e typeof_exp)
  | LETMREC ((f, x, xe), (g, y, ye), e) ->
    let typeof_x = fresh_tyvar () in
    let typeof_y = fresh_tyvar () in
    let typeof_f_result = fresh_tyvar () in
    let typeof_g_result = fresh_tyvar () in
    let typeof_exp = fresh_tyvar () in
    let type_env_ext_e_g = (g, TyFun (typeof_y, typeof_g_result))::type_env in
    let type_env_ext_e_f_g = (f, TyFun (typeof_x, typeof_f_result))::type_env_ext_e_g in
    let type_env_ext_ye = (y, typeof_y)::type_env_ext_e_f_g in
    let type_env_ext_xe_ye = (x, typeof_x)::type_env_ext_ye in
    [(type_est, typeof_exp)] @ (funcV type_env_ext_xe_ye xe typeof_f_result) @ (funcV type_env_ext_xe_ye ye typeof_g_result) @ (funcV type_env_ext_e_f_g e typeof_exp)
  | PROC (x, xe) ->
    let typeof_x = fresh_tyvar () in
    let typeof_xe = fresh_tyvar () in
    let type_env_ext_x = (x, typeof_x)::type_env in
    [(type_est, TyFun (typeof_x, typeof_xe))] @ (funcV type_env_ext_x xe typeof_xe)
  | CALL (f, e) ->
    let typeof_e = fresh_tyvar () in
    let typeof_f_result = fresh_tyvar () in
    [(type_est, typeof_f_result)] @ (funcV type_env f (TyFun (typeof_e, typeof_f_result))) @ (funcV type_env e typeof_e)
  | PRINT a -> [(type_est, TyUnit)] @ (funcV type_env a (fresh_tyvar ()))
  | SEQ (a, b) ->
    let typeof_b = fresh_tyvar () in
    [(type_est, typeof_b)] @ (funcV type_env a (fresh_tyvar ())) @ (funcV type_env b typeof_b)

let rec funcS : subst -> ibenv -> typ -> typ
= fun subst ibenv a ->
  match a with
  | TyUnit -> TyUnit
  | TyInt -> TyInt
  | TyBool -> TyBool
  | TyIntBool x ->
    let s_a = lookup_ibenv x ibenv in
    if s_a = a then a else funcS subst ibenv s_a
  | TyFun (x, y) -> TyFun (funcS subst ibenv x, funcS subst ibenv y)
  | TyList x -> TyList (funcS subst ibenv x)
  | TyVar x ->
    let s_a = lookup_subst x subst in
    if s_a = a then a else funcS subst ibenv s_a

let rec occurence_check : tyvar -> typ -> subst -> ibenv -> bool
= fun a t subst ibenv ->
  match t with
  | TyUnit | TyInt | TyBool -> false
  | TyIntBool x -> false
  | TyFun (x, y) -> (occurence_check a x subst ibenv) || (occurence_check a y subst ibenv)
  | TyList x -> occurence_check a x subst ibenv
  | TyVar x ->
    let s_x = funcS subst ibenv t in
    if s_x = TyVar a then true else if s_x = t then false else occurence_check a s_x subst ibenv

let rec unify : typ -> typ -> (subst * ibenv) -> (subst * ibenv)
= fun a b (subst, ibenv) ->
  match a, b with
  (* Polymorphic types *)
  | TyIntBool x, TyVar y | TyVar y, TyIntBool x -> ((y, TyIntBool x)::subst, ibenv)
  | TyIntBool x, t | t, TyIntBool x ->
    begin match t with
    | TyInt -> (subst, (x, TyInt)::ibenv)
    | TyBool -> (subst, (x, TyBool)::ibenv)
    | TyIntBool y -> (subst, (x, TyIntBool y)::ibenv)
    | _ -> raise TypeError end
  (* Static types *)
  | TyUnit, TyUnit | TyInt, TyInt | TyBool, TyBool -> (subst, ibenv)
  | TyVar x, TyVar y -> if x = y then (subst, ibenv) else ((x, b)::subst, ibenv)
  | TyVar x, t | t, TyVar x -> if occurence_check x t subst ibenv then raise TypeError else ((x, t)::subst, ibenv)
  | TyFun (x, y), TyFun (z, w) ->
    if x = z && y = w then (subst, ibenv)
    else let (subst_first, ibenv_first) = unify (funcS subst ibenv x) (funcS subst ibenv z) (subst, ibenv) in
      unify (funcS subst_first ibenv_first y) (funcS subst_first ibenv_first w) (subst_first, ibenv_first)
  | TyList x, TyList y -> if x = y then (subst, ibenv) else unify x y (subst, ibenv)
  | _, _ -> raise TypeError

let rec funcU : tyeqn -> (subst * ibenv) -> (subst * ibenv)
= fun type_eqn (subst, ibenv) ->
  match type_eqn with
  | [] -> (subst, ibenv)
  | (a, b)::tl -> funcU tl (unify (funcS subst ibenv a) (funcS subst ibenv b) (subst, ibenv))

let typeof : exp -> typ
= fun exp ->
  let program_id = TyVar identifier in
  let tyeqn = funcV empty_tyenv exp program_id in
  let (subst, ibenv) = funcU tyeqn (empty_subst, empty_ibenv) in
  let type_candidate = funcS subst ibenv program_id in
  match type_candidate with
  | TyIntBool x -> fresh_tyvar ()
  | _ -> type_candidate;;
