(*
 *  This implementation follows the type inference rules given at
 *  https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system#Algorithm_J 
 *
 *  The algorithm itself uses most of the names from the above link, with
 *  a few changed for ease of typing:
 *       Γ (gamma) => env
 *       ⊢ⱼ (perpendicular symbol with j subscript, a.k.a. algorithm J) => infer
 *       Γ¯ (gamma bar) => copy_with_new_typevars
 *
 *  And some expr constructors changed to match their more colloquial names
 *  to hopefully make this somewhat more approachable:
 *       Var => Identifier
 *       App => FnCall
 *       Abs => Lambda
 *
 *  Note that a let-binding (or Declaration here) can be of either
 *  a variable or a function
 *)

type typevar = int

type typ = TUnit
         | TVar of typevar
         | Fn of typ * typ
         | PolyType of typevar * typ

let curTV = ref 0

let newvar () =
    curTV := !curTV + 1;
    !curTV

(* 
 * Working with a simple language with unit, variables,
 * type annotations, lambdas, and function application
 *)
type expr = Unit
          | Identifier of string
          | Lambda of string * expr
          | FnCall of expr * expr
          | Let of string * expr * expr


(*
 * The type environment contains our current assumptions
 * of variable types
 *)
module SMap = Map.Make(String)

module HashableInt = struct
    include Int
    let hash = Hashtbl.hash
end

module ITbl = Hashtbl.Make(HashableInt)

type tenv = typ SMap.t

exception TypeError

(* specializes the polytype s by copying the term and replacing the
 * bound type variables consistently by new monotype variables *)
let rec inst s = ()

let rec unify t1 t2 = ()

(* copy the type introducing new variables for the quantification
 * to avoid unwanted captures *)
let copy_with_new_typevars t =
    let rec copy_wnt' map = function
        | TUnit -> TUnit
        | TVar(n) ->
            begin match ITbl.find_opt map n with
            | Some(n') -> TVar(n')
            | None ->
                let n' = newvar () in
                ITbl.add map n n';
                TVar(n')
            end
        | Fn(a, b) -> Fn(copy_wnt' map a, copy_wnt' map b)
        | PolyType(typevar, typ) ->
            let n' = newvar () in
            ITbl.add map typevar n';
            let ret = PolyType(n', copy_wnt' map typ) in
            ITbl.remove map typevar;
            ret
    (* In most programs, most types will have relatively few typevars,
     * so the initial size of emptyTbl should be somewhere near 0 *)
    in let emptyTbl = ITbl.create 0
    in copy_wnt' emptyTbl t


(* The main entry point to type inference *)
(* All branches (except for the trivial Unit) of the first match in this function
   are translated directly from the rules for algorithm J, given in comments *)
(* infer : Env -> Expr -> Type *)
let rec infer env = function
    | Unit -> ()

    (* Var
     *   x : s ∊ env
     *   t = inst s
     *   -----------
     *   infer env x = t
     *)
    | Identifier x -> ()

    (* App
     *   infer env f = t0
     *   infer env x = t1
     *   t' = newvar ()
     *   unify t0 (t1 -> t')
     *   ---------------
     *   infer env (f x) = t'
     *)
    | FnCall(f, x) -> ()

    (* Abs
     *   t = newvar ()
     *   infer (SMap.add x t env) e = t'
     *   -------------
     *   infer env (fun x => e) = t -> t'
     *)
    | Lambda(x, e) -> ()

    (* Let
     *   infer env e0 = t
     *   infer (SMap.add x (copy_with_new_typevars t) env) e1 = t'
     *   -----------------
     *   infer env (let x = e0 in e1) = t'
     *)
    | Let(x, e0, e1) -> ()
