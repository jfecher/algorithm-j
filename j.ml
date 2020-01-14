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

type typ =
    (* unit type *)
    TUnit

    (* 'a, 'b, etc. *)
    (* Note that this includes an optional binding, set during unification;
     * this is unique to algorithm J where mutation is needed to remember
     * some substitutions *)
    | TVar of typevar * typ option ref

    (* 'a -> 'b, all functions are single-argument only *)
    (* e.g. \a b c.c  is automatically translated to \a.\b.\c.c  *)
    (* Currying is also automatic *)
    | Fn of typ * typ

    (* Polytypes in the form  forall 'a 'b ... 'y . 'z  *)
    (* The typevar list will be a list of all monomorphic typevars in 'z *)
    (* Used only in let-bindings to make the declaration polymorphic *)
    | PolyType of typevar list * typ

let curTV = ref 0

let newvar () =
    curTV := !curTV + 1;
    !curTV

let newvar_t () = TVar (newvar (), ref None)

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

(* Setup for our Hashtbl of int -> 't *)
module HashableInt = struct
    include Int
    let hash = Hashtbl.hash
end

(* Provides 'a Itbl.t and member functions *)
module ITbl = Hashtbl.Make(HashableInt)

(* Return the next unique lowercase-letter string after the given one, e.g: *)
(*   next_letter "'a" = "'b"
 *   next_letter "'b" = "'c"
 *   next_letter "'z" = "'{"   This can be fixed but most examples shouldn't have > 26 typevars anyway
 *
 *)
let next_letter (s: bytes) =
    let c = Bytes.get s 1 in
    Bytes.set s 1 (Char.chr (Char.code c + 1))


(* If this type is the a in a -> b, should it be parenthesized? *)
(* Note this is recursive in case bound typevars are used *)
let rec should_parenthesize = function
    | TVar(_, { contents = Some t' }) -> should_parenthesize t'
    | Fn(_, _) | PolyType(_, _) -> true
    | _ -> false


(* pretty printing types *)
let string_of_type (t : typ) : string =
    (* Keep track of number to character bindings for typevars
     * e.g. '2 => 'a, '5 => 'b, etc.
     * Letters are assigned to typevars by the order in which the typevars
     * appear in the type, left to right *)
    let rec string_of_type' cur_typevar_name typevar_name_tbl = function
    | TUnit -> "unit"
    | TVar(_, { contents = Some t' }) -> string_of_type' cur_typevar_name typevar_name_tbl t'
    | TVar(n, { contents = None }) ->
        begin match ITbl.find_opt typevar_name_tbl n with
        | Some s -> s
        | None ->
            let s = Bytes.to_string cur_typevar_name in
            ITbl.add typevar_name_tbl n s;
            next_letter cur_typevar_name;
            s
        end
    | Fn(a, b) ->
        let a_str = string_of_type' cur_typevar_name typevar_name_tbl a in
        let b_str = string_of_type' cur_typevar_name typevar_name_tbl b in
        if should_parenthesize a then "(" ^ a_str ^ ") -> " ^ b_str
        else a_str ^ " -> " ^ b_str
    | PolyType(tvs, t) ->
        let curried_fn t = string_of_type' cur_typevar_name typevar_name_tbl (TVar(t, ref None)) in
        let tvs_str = List.fold_left (fun s tv -> s ^ " '" ^ curried_fn tv) "" tvs in
        "forall" ^ tvs_str ^ " . " ^ string_of_type' cur_typevar_name typevar_name_tbl t

    in string_of_type' (Bytes.of_string "'a") (ITbl.create 1) t

let print_type (t: typ) : unit =
    print_string (string_of_type t)


(*
 * The type environment contains our current assumptions
 * of variable types
 *)
module SMap = Map.Make(String)

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
        | TVar(_, { contents = Some t }) -> replace_tvs tbl t
        | TVar(n, { contents = None }) ->
            begin match ITbl.find_opt tbl n with
            | Some(t') -> t'
            | None -> TVar(n, ref None)
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

(* Can a monomorphic TVar(a) be found inside this type? *)
let rec occurs a (* in *) = function
    | TUnit -> false
    | TVar(_, { contents = Some t }) -> occurs a t
    | TVar(b, { contents = None }) -> a = b
    | Fn(b, c) -> occurs a b || occurs a c
    | PolyType(tvs, t) ->
        if List.exists (fun tv -> a = tv) tvs then false
        else occurs a t

let rec unify (t1: typ) (t2: typ) : unit =
    match (t1, t2) with
    | (TUnit, TUnit) -> ()

    | (TVar(a, boundTy), b) ->
        begin match !boundTy with
        | Some a' -> unify a' b
        | None -> (* create binding *)
            if occurs a b then raise TypeError else
            boundTy := Some b
        end

    | (a, TVar(b, boundTy)) ->
        begin match !boundTy with
        | Some b' -> unify a b'
        | None -> (* create binding *)
            if occurs b a then raise TypeError else
            boundTy := Some a
        end

    | (Fn(a, b), Fn(c, d)) ->
        unify a c;
        unify b d

    | (PolyType(a, t), PolyType(b, u)) ->
        (* NOTE: Unneeded rule, never used due to [Var] and inst *)
        unify t u

    | (a, b) -> raise TypeError


(* Find all typevars and wrap the type in a PolyType *)
(* e.g.  create_polytype (a -> b -> b) = forall a b. a -> b -> b  *)
let create_polytype (t: typ) : typ =
    (* collect all the monomorphic typevars *)
    let rec find_all_tvs = function
        | TUnit -> []
        | TVar(_, { contents = Some t }) -> find_all_tvs t
        | TVar(n, { contents = None }) -> [n]
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
(* infer : typ SMap.t -> Expr -> Type *)
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
        unify t0 (Fn(t1, t'));
        t'

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
       | Not_found -> print_endline "variable not found"
       | Failure(s) -> print_endline "lexing failure, invalid symbol");
    curTV := 0;
    main ()

let () = main ()


(* Tests *)

(* 1:    \f.\x. f x  :  (a -> b) -> a -> b  *)
(* 2:    \f.\x. f (f x) : (a -> a) -> a -> a  *)
(* (+):  \m.\n.\f.\x. m f (n f x)  :  (a -> b -> c) -> (a -> d -> b) -> a -> d -> c  *)
(* succ: \n.\f.\x. f (n f x)  :  ((a -> b) -> c -> a) -> (a -> b) -> c -> b  *)
(* mult: \m.\n.\f.\x. m (n f) x  :  (a -> b -> c) -> (d -> a) -> d -> b -> c  *)
(* pred: \n.\f.\x. n (\g.\h. h (g f)) (\u.x) (\u.u)  :  (((a -> b) -> (b -> c) -> c) -> (d -> e) -> (f -> f) -> g) -> a -> e -> g  *)
