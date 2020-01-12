# algorithm-j

A small implementation of [Algorithm J](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system#Algorithm_J)
as described by J. Roger Hindley and Robin Milner. This is more efficient
compared to the more popular algorithm W though it requires mutability in its
implementation.

j.ml contains an implementation of algorithm j on a small
lambda calculus along with a REPL.

A list of features are below, along with the rule they use in Algorithm J, and
the syntax used for them in the REPL.

- Lambdas [Abs] in the form: \x.x

- Function Application [App] in the form: f x y

- Variables [Var] in the form: x

- Let-bindings [Let] in the form: let x = a in b
    - A variable's type is "generalized" in a let binding and subsequently becomes
      forall-quantified (a polytype), this makes things like the following valid: `let id = \x.x in id id`

- Unit values in the form ()
    - There is no rule associated with unit literals, this is just an example of
how to handle literals where you already know the type.

Note: I was lazy with the lexer! Since integers are not in the language,
typing one will throw an exception, beware!

---

## Running

Make sure `menhir` and `ocamllex` are installed either via `opam install menhir ocamllex`
or via your system's package manager. Afterwards, just `make`.

Run `$ ./j` to start the REPL, type in any expression and get the type as a result, e.g:

```
> \x.\y.x
'a -> 'b -> 'a
> \x.x x
type error
> let id = \x.x in id id
'c -> 'c
```
