module Lexer = struct

module P = Printf
exception End_of_system
type token = CID of string | VID of string | NUM of string | TO | IS | QUIT | OPEN | EOF | ONE of char

let print_token tk = 
    match tk with
        (CID i) -> P.printf "CID(%s)" i
        | (VID i) -> P.printf "VID(%s)" i
        | (NUM i) -> P.printf "NUM(%s)" i
        | (TO) -> P.printf ":-"
        | (IS) -> P.printf "is"
        | (QUIT) -> P.printf "quit"
        | (OPEN) -> P.printf "open"
        | (EOF) -> P.printf "eof"
        | (ONE c) -> P.printf "ONE(%c)" c 

let _ISTREAM = ref stdin
let ch = ref []
let low_number = ref 1
let plus_one_low_number () = low_number := !low_number + 1
let read () = match !ch with
    [] -> input_char !_ISTREAM
    | h::rest -> (ch := rest; h)
let unread c = ch := c::!ch
let lookahead () = try let c = read() in unread c; c with End_of_file -> '$'

let rec integer i = 
    let c = lookahead () in
        if (c >= '1' && c <= '9') then integer (i^(Char.escaped(read ())))
        else i 
and identifier id = 
    let c = lookahead () in
        if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '1' && c <= '9') || c = '_') 
        then identifier (id^(Char.escaped(read ())))
        else id
and native_token () = 
    let c = lookahead () in
        if (c >= 'a' && c <= 'z') then let id = identifier "" in
            match id with
                "quit" -> QUIT
                | "open" -> OPEN
                | "is" -> IS
                | _ -> CID id
        else if (c >= 'A' && c <= 'Z') then let id = identifier "" in VID id
        else if (c >= '0' && c <= '9') then NUM (integer "")
        else if (c = ':') then let c1 = read () in let d = lookahead () in if (d = '-') then let _ = read () in TO else ONE (c1)
        else ONE (read ())

and gettoken () = 
    try
        let token = native_token () in
            match token with
                ONE ' ' -> gettoken ()
                | ONE '\t' -> gettoken ()
                | ONE '\n' -> let _ = plus_one_low_number () in (print_string (string_of_int !low_number); gettoken())
                | _ -> token
    with End_of_file -> EOF

let rec run () =
    flush stdout;
    let rlt = gettoken () in 
        match rlt with
            (ONE '$') -> raise End_of_system
            | _ -> (print_token rlt; P.printf "\n"; run())

end

module Parser = struct

    module L = Lexer
    
    let tok = ref (L.ONE ' ')
    let getToken () = L.gettoken ()
    let advance () = (tok := getToken(); L.print_token (!tok))
    
    exception Syntax_error
    let error () = raise Syntax_error
    let check t = match !tok with
            L.CID _ -> if (t = (L.CID "")) then () else error ()
            | L.VID _ -> if (t = (L.VID "")) then () else error ()
            | L.NUM _ -> if (t = (L.NUM "")) then () else error ()
            | tk      -> if (tk = t) then () else error ()
    
    let eat t = (check t; advance())
    
    let rec clauses() = match !tok with
            L.EOF -> ()
            | _ -> (clause(); clauses())
    and clause() = match !tok with
            L.ONE '(' -> (term(); eat(L.ONE '.'))
            | _ -> (predicate(); to_opt(); eat(L.ONE '.'))
    and to_opt() = match !tok with
           L.TO -> (eat(L.TO); terms())
           | _ -> ()
    and command() = match !tok with
            L.QUIT -> exit 0
            |L.OPEN -> (eat(L.OPEN);
                match !tok with
                    L.CID s -> (eat(L.CID ""); check (L.ONE '.');
                        L._ISTREAM := open_in (s^".pl");
                        advance(); clauses(); close_in (!L._ISTREAM))
                    | _ -> error())
            | _ -> (term ();
                    match !tok with
                        L.ONE ',' -> (eat(L.ONE ','); predicate ())
                        | L.ONE '.' -> check (L.ONE '.')
                        | _ -> try error() with 
                                 Syntax_error -> print_string (string_of_int !L.low_number ^ "Syntax_error!!"); print_newline ())
    and term () = match !tok with
            L.ONE '(' -> (eat(L.ONE '('); term(); eat(L.ONE ')'))
            | L.VID s -> (eat(L.VID ""); eat(L.IS); arithmexp())
            | _ -> predicate()
    and terms () = (term (); terms'())
    and terms' () = match !tok with
            L.ONE ',' -> (eat(L.ONE ','); term (); terms'())
            | _ -> ()
    and predicate () = match !tok with
            L.CID s -> (eat(L.CID ""); eat(L.ONE '('); args (); eat(L.ONE ')'))
            | _ -> try error() with 
                                 Syntax_error -> print_string (string_of_int !L.low_number ^ "Syntax_error!!"); print_newline ()
    and args () = (expr(); args'())
    and args'() = match !tok with
            L.ONE ',' -> (eat(L.ONE ','); expr(); args'())
            | _ -> ()
    and expr () = arithmexp()
    and tail_opt () = match !tok with
            L.ONE '(' -> (eat(L.ONE '('); args(); eat(L.ONE ')'))
            | _ -> ()
    and list () = match !tok with
            L.ONE ']' -> ()
            | _ -> (expr(); list_opt())
    and list_opt () = match !tok with
            L.ONE '|' -> (eat(L.ONE '|'); id())
            | L.ONE ',' -> (eat(L.ONE ','); list())
            | _ -> ()
    and id () = match !tok with
            L.CID s -> (eat(L.CID ""))
            | L.VID s -> (eat(L.VID ""))
            | L.NUM n -> (eat(L.NUM ""))
            | _ -> error()
    and arithmexp () = (arithmterm(); arithmexp'())
    and arithmexp' () = match !tok with
            L.ONE '+' -> (eat(L.ONE '+'); arithmterm(); arithmexp'())
            | L.ONE '-' -> (eat(L.ONE '-'); arithmterm(); arithmexp'())
            | _ -> ()
    and arithmterm () = (arithmfactor(); arithmterm'())
    and arithmterm' () = match !tok with
            L.ONE '*' -> (eat(L.ONE '*'); arithmfactor(); arithmterm'())
            | L.ONE '/' -> (eat(L.ONE '/'); arithmfactor(); arithmterm'())
            | _ -> ()
    and arithmfactor () = match !tok with
            L.ONE '(' -> (eat(L.ONE '('); arithmexp(); eat(L.ONE ')'))
            | L.ONE '-' -> (eat(L.ONE '-'); arithmexp())
            | L.ONE '[' -> (eat(L.ONE '['); list(); eat(L.ONE ']'))
            | L.CID s -> (eat(L.CID ""); tail_opt())
            | L.VID s -> (eat(L.VID ""))
            | L.NUM n -> (eat(L.NUM ""))
            | _ -> error ()
    end
    
    let rec run () = 
        print_string "?- ";
        while true do
            flush stdout; Lexer._ISTREAM := stdin;
            Parser.advance(); Parser.command(); print_string "\n?- "
        done
