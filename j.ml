(*
 *  This implementation follows the type inference rules given at
 *  https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system#Algorithm_J 
 *
 *  The algorithm itself uses most of the names from the above link, with
 *  a few changed for ease of typing:
 *       Γ (gamma) => env
 *       ⊢ⱼ (perpendicular symbol with j subscript, a.k.a. algorithm J) => infer
 *       Γ¯ (gamma bar) => create_polytype
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
         | PolyType of typevar list * typ

let curTV = ref 0

let newvar () =
    curTV := !curTV + 1;
    !curTV

let newvar_t () = TVar (newvar ())

(* 
 * Working with a simple language with unit, variables,
 * type annotations, lambdas, and function application
 *)
open Expr
(* in expr.mli:
type expr = Unit
          | Identifier of string
          | Lambda of string * expr
          | FnCall of expr * expr
          | Let of string * expr * expr
*)

(* pretty printing types *)
let rec string_of_type : typ -> string = function
    | TUnit -> "unit"
    | TVar(n) -> "'" ^ string_of_int n
    | Fn(a, b) ->
        begin match a with
        | Fn(_, _) | PolyType(_, _) ->
                "(" ^ string_of_type a ^ ") -> " ^ string_of_type b
        | _ -> string_of_type a ^ " -> " ^ string_of_type b
        end
    | PolyType(tvs, t) ->
        let tvs_str = match tvs with
            | [] -> ""
            | first::rest ->
                List.fold_left (fun s tv -> s ^ " '" ^ string_of_int tv)
                               ("'" ^ string_of_int first)
                               rest
        in "forall " ^ tvs_str ^ ". " ^ string_of_type t

let print_type (t: typ) : unit =
    print_string (string_of_type t)


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
 * bound type variables consistently by new monotype variables
 * E.g.   inst (forall a b. a -> b -> a) = c -> d -> c     *)
let inst (s: typ) : typ =
    (* Replace any typevars found in the Hashtbl with the
     * associated value in the same table, leave them otherwise *)
    let rec replace_tvs tbl = function
        | TUnit -> TUnit
        | TVar(n) ->
            begin match ITbl.find_opt tbl n with
            | Some(t') -> t'
            | None -> TVar(n)
            end
        | Fn(a, b) -> Fn(replace_tvs tbl a, replace_tvs tbl b)
        | PolyType(tvs, typ) ->
            let tbl_cpy = ITbl.copy tbl in
            List.iter (ITbl.remove tbl_cpy) tvs;
            PolyType(tvs, replace_tvs tbl_cpy typ)

    in match s with
    (* Note that the returned type is no longer a PolyType,
     * this means it is now monomorphic and not forall-quantified *)
    | PolyType(typevars, typ) ->
        let tvs_to_replace = ITbl.create 1 in
        List.iter (fun tv -> ITbl.add tvs_to_replace tv (newvar_t ())) typevars;
        replace_tvs tvs_to_replace typ
    | other -> other


(* The find for our union-find like algorithm *)
(* Go through the given type, replacing all typevars with their bound types when possible *)

(* This is the main part where this reference impl diverges
 * from the word-for-word algorithm but the union-find algorithm
 * also isn't the core of algorithm-j anyway and this works as well *)
let rec find tbl = function
    | TUnit -> TUnit
    | TVar(a) ->
        begin match ITbl.find_opt tbl a with
        | Some t' -> find tbl t'
        | None -> TVar(a)
        end
    | Fn(a, b) -> Fn(find tbl a, find tbl b)
    | PolyType(tvs, t) ->
        let tbl_cpy = ITbl.copy tbl in
        List.iter (ITbl.remove tbl_cpy) tvs;
        PolyType(tvs, find tbl_cpy t)

(* Can a monomorphic TVar(a) be found inside this type? *)
let rec occurs a (* in *) = function
    | TUnit -> false
    | TVar(b) -> a = b
    | Fn(b, c) -> occurs a b || occurs a c
    | PolyType(tvs, t) ->
        if List.exists (fun tv -> a = tv) tvs then false
        else occurs a t

let rec unify (t1: typ) (t2: typ) =
    let rec unify' t1 t2 (tbl : typ ITbl.t) =
        let t1 = find tbl t1 in
        let t2 = find tbl t2 in
        match (t1, t2) with
        | (TUnit, TUnit) -> TUnit

        | (TVar(a), b) ->
            begin match ITbl.find_opt tbl a with
            | Some t -> unify' t b tbl
            | None ->
                (* Need this check to block recursive types, this catches, e.g., \x.x x *)
                if occurs a b then raise TypeError
                else
                ITbl.add tbl a b;
                b
            end
        | (a, TVar(b)) ->
            begin match ITbl.find_opt tbl b with
            | Some t -> unify' a t tbl
            | None ->
                if occurs b a then raise TypeError
                else
                ITbl.add tbl b a;
                a
            end

        | (Fn(a, b), Fn(c, d)) ->
            let a' = unify' a c tbl in
            let b' = unify' b d tbl in
            Fn(a', b')

        | (PolyType(a, t), PolyType(b, u)) ->
            (* TODO: unimplemented! *)
            unify' t u tbl

        | (a, b) -> raise TypeError

    in let emptyTbl = ITbl.create 1
    in unify' t1 t2 emptyTbl


(* Find all typevars and wrap the type in a PolyType *)
(* e.g.  create_polytype (a -> b -> b) = forall a b. a -> b -> b  *)
let create_polytype (t: typ) : typ =
    (* collect all the monomorphic typevars *)
    let rec find_all_tvs = function
        | TUnit -> []
        | TVar(n) -> [n]
        | Fn(a, b) -> find_all_tvs a @ find_all_tvs b
        | PolyType(tvs, typ) ->
            (* Remove all of tvs from find_all_tvs typ, this could be faster *)
            List.filter (fun tv -> not (List.mem tv tvs)) (find_all_tvs typ)

    in find_all_tvs t
    |> List.sort_uniq compare
    |> fun l -> PolyType(l, t)


(* The main entry point to type inference *)
(* All branches (except for the trivial Unit) of the first match in this function
   are translated directly from the rules for algorithm J, given in comments *)
(* infer : Env -> Expr -> Type *)
let rec infer env : expr -> typ = function
    | Unit -> TUnit

    (* Var
     *   x : s ∊ env
     *   t = inst s
     *   -----------
     *   infer env x = t
     *)
    | Identifier x ->
        let s = SMap.find x env in
        let t = inst s in
        t

    (* App
     *   infer env f = t0
     *   infer env x = t1
     *   t' = newvar ()
     *   unify t0 (t1 -> t')
     *   ---------------
     *   infer env (f x) = t'
     *)
    | FnCall(f, x) ->
        let t0 = infer env f in
        let t1 = infer env x in
        let t' = newvar_t () in
        let t0' = unify t0 (Fn(t1, t')) in
        (* t' *)
        begin match t0' with
        | Fn(_, unified_t') -> unified_t'
        | _ -> raise TypeError (* unreachable *)
        end

    (* Abs
     *   t = newvar ()
     *   infer (SMap.add x t env) e = t'
     *   -------------
     *   infer env (fun x -> e) = t -> t'
     *)
    | Lambda(x, e) ->
        let t = newvar_t () in
        let t' = infer (SMap.add x t env) e in
        Fn(t, t')

    (* Let
     *   infer env e0 = t
     *   infer (SMap.add x (create_polytype t) env) e1 = t'
     *   -----------------
     *   infer env (let x = e0 in e1) = t'
     *)
    | Let(x, e0, e1) ->
        let t = infer env e0 in
        let t' = infer (SMap.add x (create_polytype t) env) e1 in
        t'


(******************************************************************************
                       front-end for parsing exprs on
                        the command line and showing
                             their computed types
******************************************************************************)

    
(* The classic read-eval-printline-loop *)
let rec main () =
    (try
        print_string "> ";
        read_line ()
        |> Lexer.parse
        |> infer SMap.empty
        |> print_type;
        print_string "\n"
    with
       | TypeError -> print_endline "type error"
       | Failure(s) -> print_endline "lexing failure, invalid symbol");
    curTV := 0;
    main ()

let () = main ()
