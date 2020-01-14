%token Tok_LParen
%token Tok_RParen
%token Tok_Backslash
%token Tok_Dot
%token Tok_Unit
%token Tok_Let
%token Tok_Eq
%token Tok_In
%token Tok_EOF
%token <string> Tok_Ident

%start <Expr.expr> parse_expr
%%

parse_expr: e=term; Tok_EOF   { e }

term: t=app_term                                              { t }
    | Tok_Backslash; l=lambda                                 { l }
    | Tok_Let; x=Tok_Ident; Tok_Eq; e1=term; Tok_In; e2=term  { Expr.Let(x, e1, e2) }
    ;

app_term: t=atomic_term              { t }
        | f=app_term; x=atomic_term  { Expr.FnCall(f, x) }
        ;

atomic_term: Tok_LParen; t=term; Tok_RParen  { t }
           | s=Tok_Ident                     { Expr.Identifier(s) }
           | Tok_Unit                        { Expr.Unit }
           ;

(* Support \a b c. shorthand *)
lambda: x=Tok_Ident; Tok_Dot; t=term    { Expr.Lambda(x, t) }
      | x=Tok_Ident; l=lambda           { Expr.Lambda(x, l) }
      ;
