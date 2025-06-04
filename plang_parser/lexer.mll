    {
      open Parser

      exception LexError of string

      let[@inline] failwith msg = raise (LexError msg)

      let[@inline] illegal c =
        failwith (Printf.sprintf "[lexer] unexpected character: '%c'" c)

      open Lexing
      let next_line lexbuf =
        let pos = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <-
          { pos with pos_bol = lexbuf.lex_curr_pos;
                     pos_lnum = pos.pos_lnum + 1
          }
    }

(* regular expressions *)
let whitespace = ' ' | '\t'
let newline = "\r\n" | '\r' | '\n'
let lowercase = ['a'-'z' '_']
let uppercase = ['A'-'Z']
let identchar = ['A'-'Z' 'a'-'z' '_' '\'' '0'-'9' '!']

let ident = (lowercase | uppercase) identchar*
let number = ['0'-'9'] ['0'-'9' '_']*

rule next_token = parse
  | eof { EOF }
  | whitespace+
    { next_token lexbuf }
  | newline
      { next_line lexbuf; next_token lexbuf }
  | "(*"
      { comment 0 lexbuf; next_token lexbuf }
  | "/*" { comment 0 lexbuf; next_token lexbuf }
  | "//" { comment_line 0 lexbuf; next_token lexbuf }

  (* YOUR TOKENS HERE... *)
  (* keywords... *)
  | "event" {EVENT}
  | "visible" {VISIBLE}
  | "type" {TYPE}
  | "prop" {PROP}
  | "machine" {MACHINE}
  | "var" {VAR}
  | "syn" {SYN}
  | "param" {PARAM}
  | "enum" {ENUM}
  | "state" {STATE}
  | "hot" {HOT}
  | "cold" {COLD}
  | "start" {START}
  | "plain" {PLAIN}
  | "entry" {ENTRY}
  | "exit" {EXIT}
  | "listen" {LISTEN}
  | "on" {ON}
  | "if" {IF}
  | "do" {DO}
  | "this" {THIS}
  | "halt" {HALT}
  | "local" {LOCAL}
  | "fun" {FUN}
  | "null" {NULL}
  | '$' {RANDOMBOOL}
  | "goto" {GOTO}
  | "return" {RETURN}
  | "with" {WITH}
  (* logic operators *)
  | "not" {NOT}
  | "&&" {AND}
  | "||" {OR}
  | "==>" {IMPL}
  | "<==>" {IFF}
  | "forall" {FORALL}
  | "exists" {EXISTS}
  | "pi" {PI}
  | "true" {TRUE}
  | "false" {FALSE}
  (* splitter *)
  | "," {COMMA}
  | ":" {COLON}
  | ";" {SEMICOLON}
  | "->" {ARROW}
  | "|" {BAR}
  | "." {DOT}
  | ":=" {COLONEQ}
  | "=" {ASSIGN}
  (* arithmetic operators *)
  | "-" {MINUS}
  | "+" {PLUS}
  | "!" {NEG}
  | "==" {EQ}
  | "!=" {NEQ}
  | "<=" {LE}
  | ">=" {GE}
  | '<' {LT}
  | '>' {GT}
  | "*" {STAR}
  | '\\' {DIV}
  (* paranthesis *)
  | '(' { LPAR }
  | ')' { RPAR }
  | "<[" {LEPAR}
  | "]>" {REPAR}
  | "[" {LSQPRAN}
  | "]" {RSQPRAN}
  | "{" {LBRACKET}
  | "}" {RBRACKET}
  (* regex *)
  | "emp" {EMP}
  | "eps" {EPSILON}
  | "ctx" {CTX}
  | "rep" {REPEAT}
  | '~' {CONCAT}
  (* type *)
  | "int" {INT}
  | "bool" {BOOL}
  | "unit" {UNIT}
  | '\'' {PRIME}
  | "<:" {SUBTYPING}
  (* lex identifiers last, so keywords are not lexed as identifiers *)
  | number as number { NUMBER (int_of_string number) }
  | ident as ident { IDENT ident }
  | '"' {read_string (Buffer.create 10) lexbuf}
  (* no match? raise exception *)
  | _ as c { illegal c }
and read_string buf =
  parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (Failure ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (Failure ("String is not terminated")) }

(* allow nested comments, like OCaml *)
and comment nesting = parse
  | "(*" | "/*"
    { comment (nesting+1) lexbuf }
  | "*)" | "*/"
    { if nesting > 0 then comment (nesting - 1) lexbuf }
  | eof
    { failwith "[lexer] unterminated comment (* *) or /* */ at EOF" }
  | _
    { comment nesting lexbuf }

and comment_line nesting = parse
  | newline { if nesting > 0 then comment (nesting - 1) lexbuf }
  | eof { if nesting > 0 then comment (nesting - 1) lexbuf }
  | _ { comment_line nesting lexbuf }
