{
    open Lexing
    open Parser

    exception SyntaxError of string

    let next_line lexbuf =
        let pos = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <-
            { pos with pos_bol = lexbuf.lex_curr_pos;
                       pos_lnum = pos.pos_lnum + 1
            }
}

let unitt = "()"
let ident = ['a'-'z' 'A'-'Z' '_']+
let whitespace = [' ' '\t']+
let newline = 'r' | '\n' | "\r\n"

rule read =
    parse
    | whitespace    { read lexbuf }
    | newline       { next_line lexbuf; read lexbuf }
    | unitt         { Tok_Unit }
    | '('           { Tok_LParen }
    | ')'           { Tok_RParen }
    | "let"         { Tok_Let }
    | "in"          { Tok_In }
    | '='           { Tok_Eq }
    | '.'           { Tok_Dot }
    | '\\'          { Tok_Backslash }
    | ident         { Tok_Ident (Lexing.lexeme lexbuf) }
    | eof           { Tok_EOF }


{
    let print_position lexbuf =
        let pos = lexbuf.lex_curr_p in
        Printf.printf "%s:%d:%d" pos.pos_fname
            pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

    let parse_with_error lexbuf =
        try Some (Parser.parse_expr read lexbuf) with
        | SyntaxError msg ->
            print_position lexbuf;
            Printf.printf ": %s\n" msg;
            None
        | Parser.Error ->
            print_position lexbuf;
            print_endline ": syntax error";
            exit (-1)

    let rec parse str =
        let lexbuf = Lexing.from_string str in
        match parse_with_error lexbuf with
        | Some value -> value
        | None -> Unit
}
