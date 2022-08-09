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
                | ONE '\n' -> gettoken()
                | _ -> token
    with End_of_file -> EOF

let rec run () =
    flush stdout;
    let rlt = gettoken () in 
        match rlt with
            (ONE '$') -> raise End_of_system
            | _ -> (print_token rlt; P.printf "\n"; run())

end

module Evaluator = struct

module P = Printf
type ast = Atom of string | Var of string | App of string * ast list
let numberOfSucceed = ref 0
let numberOfQuestion = ref 1
let vid = ref ""

let rec reverse xs =
        if xs = [] then []
        else reverse (List.tl xs) @ [List.hd xs]

let rec print_ast ast = match ast with
    (App(s, hd::t1)) -> (P.printf "App(\"%s\", [" s; print_ast hd; List.iter (fun x -> (print_string ";"; print_ast x)) t1; print_string "])")
    | (App(s, [])) -> P.printf "App(\"%s\", [])" s 
    | (Atom s) -> P.printf "Atom \"%s\"" s 
    | (Var s) -> P.printf "Var \"%s\"" s

let rec print_sprolog ast valList = match ast with
    (App(s, lst)) -> let rec valPrint valList resultList = 
                        match (valList, resultList) with
                            (first1::rest1, first2::rest2) -> (
                                P.printf("%s = ") first1;
                                print_sprolog first2 [];
                                P.printf("\n");
                                valPrint rest1 rest2
                            )
                            | ([], _) -> ()
                            | (_, []) -> P.printf "%s()" s
                        in valPrint (reverse valList) lst
    | (Atom s) -> P.printf "%s" s 
    | (Var s) -> P.printf "%s" s 

let print_ast_list lst = match lst with
    (hd::t1) -> (print_string "["; print_ast hd; List.iter (fun x -> (print_string ";"; print_ast x)) t1; print_string "]")
    | [] -> print_string "[]"

let sub name term = 
    let rec mapVar ast = match ast with
        (Atom x) -> Atom(x)
        | (Var n) -> if n = name then term else Var n
        | (App(n, terms)) -> App(n, List.map mapVar terms)
    in mapVar

let mgu (a, b) = 
    let rec ut (one, another, unifier) = match (one, another) with
        ([], []) -> (true, unifier)
        | (term::t1, Var(name)::t2) -> 
            let r = fun x -> sub name term (unifier x) in 
                ut(List.map r t1, List.map r t2, r)
        | (Var(name)::t1, term::t2) -> 
            let r = fun x -> sub name term (unifier x) in 
                ut(List.map r t1, List.map r t2, r)
        | (Atom(n)::t1, Atom(m)::t2) -> 
            if n = m then ut(t1, t2, unifier) else (false, unifier)
        | (App(n1, xt1)::t1, App(n2, xt2)::t2) -> 
            if n1 = n2 && List.length xt1 = List.length xt2 then ut(xt1@t1, xt2@t2, unifier)
            else (false, unifier)
        | (_, _) -> (false, unifier)
        in ut([a], [b], (fun x -> x))

let succeed query = (numberOfSucceed := (!numberOfSucceed + 1); print_sprolog query [!vid]; true)
let rename ver term = 
    let rec mapVar ast = match ast with
        (Atom x) -> Atom(x)
        | (Var n) -> Var (n^"#"^ver)
        | (App(n, terms)) -> App(n, List.map mapVar terms)
    in mapVar term

exception Compiler_error

let rec solve (program, question, result, depth) = match question with
    [] -> succeed result
    | goal::goals -> 
        let onestep _ clause =
            match List.map (rename (string_of_int depth)) clause with
                [] -> raise Compiler_error
                | head::conds -> 
                    let (unifiable, unifier) = mgu (head, goal) in
                        if unifiable then 
                            solve (program, List.map unifier (conds@goals), unifier result, depth + 1)
                        else true
        in List.fold_left onestep true program

let eval (program, question) = solve (program, [question], question, 1) 

end

module Parser = struct

module L = Lexer
module E = Evaluator
        
let tok = ref (L.ONE ' ')
let getToken () = L.gettoken ()
let advance () = (tok := getToken())
        
exception Syntax_error
let error () = raise Syntax_error
let check t = match !tok with
        L.CID _ -> if (t = (L.CID "")) then () else error ()
        | L.VID _ -> if (t = (L.VID "")) then () else error ()
        | L.NUM _ -> if (t = (L.NUM "")) then () else error ()
        | tk      -> if (tk = t) then () else error ()
        
let eat t = (check t; advance())
let prog = ref [[E.Var ""]]
        
let rec clauses () = match !tok with
        L.EOF -> []
        | _ -> let clu1 = clause() in let clu2 = clauses() in clu1::clu2
and clause () = match !tok with
        L.ONE '(' -> let t1 = term() in let _ = eat(L.ONE '.') in [t1]
        | _ -> let pre1 = predicate() in let to1 = to_opt() in let _ = eat(L.ONE '.') in pre1::to1
and to_opt () = match !tok with
         L.TO -> let _ = eat(L.TO) in let t2 = terms() in t2
        | _ -> []
and command () = match !tok with
        L.QUIT -> exit 0
        | L.OPEN -> (eat(L.OPEN);
            match !tok with
                L.CID s -> (eat(L.CID ""); check(L.ONE '.');
                    L._ISTREAM := open_in(s^".pl");
                    advance(); prog := clauses(); close_in(!L._ISTREAM))
                | _ -> error())
        | _ -> let t = term() in match !tok with
                L.ONE ',' -> (eat(L.ONE ','); let _ = E.eval(!prog, t) in E.numberOfQuestion := (!E.numberOfQuestion + 1); command())
                | L.ONE '.' -> (check(L.ONE '.'); let _ = E.eval(!prog, t) in if !E.numberOfQuestion = !E.numberOfSucceed then (Printf.printf "Yes"; E.numberOfQuestion := 1; E.numberOfSucceed := 0) else (Printf.printf "No"; E.numberOfQuestion := 1; E.numberOfSucceed := 0))
                | _ -> error()
and term () = match !tok with
        L.ONE '(' -> let _ = eat(L.ONE '(') in let t3 = term() in let _ = eat(L.ONE ')') in t3
        | _ -> let pre2 = predicate() in pre2
and terms () = let t4 = term() in terms' [t4]
and terms' _t = match !tok with
        L.ONE ',' -> let _ = eat(L.ONE ',') in let t5 = term() in let _ = terms' (_t@[t5]) in _t@[t5]
        | _ -> _t
and predicate () = match !tok with
        L.CID s -> let cid = s in let _ = eat(L.CID "") in let _ = eat(L.ONE '(') in let ar1 = args() in let _ = eat(L.ONE ')') in E.App(cid, ar1)
        | _ -> error()
and args () = let exp1 = expr() in args' [exp1]
and args' _a = match !tok with
         L.ONE ',' -> let _ = eat(L.ONE ',') in let exp2 = expr() in let _ = args' (_a@[exp2]) in _a@[exp2]
        | _ -> _a
and expr () = match !tok with
        L.ONE '(' -> let _ = eat(L.ONE '(') in let e = expr() in let _ = eat(L.ONE ')') in e
        | L.ONE '[' -> let _ = eat(L.ONE '[') in let l = list() in let _ = eat(L.ONE ']') in l 
        | L.CID s -> let _ = eat(L.CID "") in let t = tail_opt s in t 
        | L.VID s -> let _ = eat(L.VID "") in E.vid := s; E.Var s 
        | L.NUM n -> let _ = eat(L.NUM "") in E.Atom n 
        | _ -> error()
and tail_opt _to = match !tok with
        L.ONE '(' -> let _ = eat(L.ONE '(') in let ags2 = args() in let _ = eat(L.ONE ')') in E.App (_to, ags2)
        | _ -> E.Atom _to
and list () = match !tok with
        L.ONE ']' -> E.Atom "nil"
        | _ -> let exp3 = expr() in let lso1 = list_opt() in E.App("cons", [exp3; lso1])
and list_opt () = match !tok with
        L.ONE '|' -> let _ = eat(L.ONE '|') in let id = id() in id
        | L.ONE ',' -> let _ = eat(L.ONE ',') in let lst2 = list() in lst2
        | _ -> E.Atom "nil"
and id () = match !tok with
        L.CID s -> let cid = s in let _ = eat(L.CID "") in E.Atom cid
        | L.VID s -> let vid = s in let _ = eat(L.VID "") in E.Var vid
        | L.NUM n -> let num = n in let _ = eat(L.NUM "") in E.Atom num
        | _ -> error()
        
end
        
let rec run () = 
        print_string "?- ";
        while true do
            flush stdout; Lexer._ISTREAM := stdin;
            Parser.advance(); Parser.command(); print_string "\n?- "
        done
