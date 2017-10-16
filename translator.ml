open List;;
(* The List library includes a large collection of useful functions.
   In the provided code, I've used assoc, exists, filter, find,
   fold_left, hd, length, map, and rev
*)

open Str;;      (* for split *)
(* The Str library provides a few extra string-processing routines.
   In particular, it provides "split", which I use to break program
   input into whitespace-separated words.  Note, however, that this
   library is not automatically available.  If you are using the
   top-level interpreter, you have to say
        #load "str.cma";;
   If you are generating an executable fron the shell, you have to say
        ocamlc str.cma interpreter.ml
*)

(* CSC 254 Assignment 3 Translation*)
(* Po-Chun Chiu & Yujie Liu *)

(* Surprisingly, compose isn't built in.  It's included in various
   widely used commercial packages, but not in the core libraries. *)
let compose f g x = f (g x);;

type symbol_productions = (string * string list list);;
type grammar = symbol_productions list;;
type parse_table = (string * (string list * string list) list) list;;
(*                  nt        predict_set   rhs *)

let calc_gram : grammar =
  [ ("P",  [["SL"; "$$"]])
  ; ("SL", [["S"; "SL"]; []])
  ; ("S",  [ ["id"; ":="; "E"]; ["read"; "id"]; ["write"; "E"]])
  ; ("E",  [["T"; "TT"]])
  ; ("T",  [["F"; "FT"]])
  ; ("TT", [["ao"; "T"; "TT"]; []])
  ; ("FT", [["mo"; "F"; "FT"]; []])
  ; ("ao", [["+"]; ["-"]])
  ; ("mo", [["*"]; ["/"]])
  ; ("F",  [["id"]; ["num"]; ["("; "E"; ")"]])
  ];;

let ecg : grammar =
  [ ("P",  [["SL"; "$$"]])
  ; ("SL", [["S"; "SL"]; []])
  ; ("S",  [ ["id"; ":="; "E"]; ["read"; "id"]; ["write"; "E"]
           ; ["if"; "R"; "SL"; "fi"]; ["do"; "SL"; "od"]; ["check"; "R"]
           ])
  ; ("R",  [["E"; "ET"]])
  ; ("E",  [["T"; "TT"]])
  ; ("T",  [["F"; "FT"]])
  ; ("F",  [["id"]; ["num"]; ["("; "E"; ")"]])
  ; ("ET", [["ro"; "E"]; []])
  ; ("TT", [["ao"; "T"; "TT"]; []])
  ; ("FT", [["mo"; "F"; "FT"]; []])
  ; ("ro", [["=="]; ["<>"]; ["<"]; [">"]; ["<="]; [">="]])
  ; ("ao", [["+"]; ["-"]])
  ; ("mo", [["*"]; ["/"]])
  ];;

(* is e a member of list l? *)
let member e l = exists ((=) e) l;;

(* OCaml has a built-in quicksort; this was just an exercise. *)
let rec sort l =
  let rec partition pivot l left right =
    match l with
    | []        -> (left, right)
    | c :: rest -> if (compare c pivot) < 0
                   then partition pivot rest (c :: left) right
                   else partition pivot rest left (c :: right) in
  match l with
  | []        -> l
  | h :: []   -> l
  | h :: rest -> let (left, right) = partition h rest [] [] in
                 (sort left) @ [h] @ (sort right);;

(* leave only one of any consecutive identical elements in list *)
let rec unique l =
  match l with
  | []             -> l
  | h :: []        -> l
  | a :: b :: rest -> if a = b (* structural equivalence *)
                      then unique (b :: rest)
                      else a :: unique (b :: rest);;

let unique_sort l = unique (sort l);;

(* Return all individual productions in grammar. *)
let productions gram : (string * string list) list =
  let prods (lhs, rhss) = map (fun rhs -> (lhs, rhs)) rhss in
  fold_left (@) [] (map prods gram);;

(* Return all symbols in grammar. *)
let gsymbols gram : string list =
  unique_sort
    (fold_left (@) [] (map (compose (fold_left (@) []) snd) gram));;

(* Return all elements of l that are not in excluded.
   Assume that both lists are sorted *)
let list_minus l excluded =
  let rec helper rest te rtn =
    match rest with
    | []     -> rtn
    | h :: t -> match te with
                | []       -> (rev rest) @ rtn
                | h2 :: t2 -> match compare h h2 with
                              | -1 -> helper t te (h :: rtn)
                              |  0 -> helper t t2 rtn
                              |  _ -> helper rest t2 rtn in
  rev (helper l excluded []);;

(* Return just the nonterminals. *)
let nonterminals gram : string list = map fst gram;;

(* Return just the terminals. *)
let terminals gram : string list =
    list_minus (gsymbols gram) (unique_sort (nonterminals gram));;

(* Return the start symbol.  Throw exception if grammar is empty. *)
let start_symbol gram : string = fst (hd gram);;

let is_nonterminal e gram = member e (nonterminals gram);;

let is_terminal e gram = member e (terminals gram);;

let union s1 s2 = unique_sort (s1 @ s2);;

(* return suffix of lst that begins with first occurrence of sym
   (or [] if there is no such occurrence) *)
let rec suffix sym lst = 
  match lst with
  | [] -> []
  | h :: t -> if h = sym (* structural equivalence *)
              then lst else suffix sym t;;

(* Return a list of pairs.
   Each pair consists of a symbol A and a list of symbols beta
   such that for some alpha, A -> alpha B beta. *)
type right_context = (string * string list) list;;
let get_right_context (b:string) gram : right_context =
  fold_left (@) []
            (map (fun prod ->
                    let a = fst prod in
                    let rec helper accum rhs =
                      let b_beta = suffix b rhs in
                      match b_beta with
                      | [] -> accum
                      | x :: beta  -> (* assert x = b *)
                                      helper ((a, beta) :: accum) beta in
                    helper [] (snd prod))
                 (productions gram));;

(* parser generator starts here *)

type symbol_knowledge = string * bool * string list * string list;;
type knowledge = symbol_knowledge list;;
let symbol_field (s, e, fi, fo) = s;;
let eps_field (s, e, fi, fo) = e;;
let first_field (s, e, fi, fo) = fi;;
let follow_field (s, e, fi, fo) = fo;;

let initial_knowledge gram : knowledge =
  map (fun a -> (a, false, [], [])) (nonterminals gram);;

let get_symbol_knowledge (a:string) (kdg:knowledge) : symbol_knowledge =
  find (fun (s, e, fi, fo) -> s = a) kdg;;

(* Can word list w generate epsilon based on current estimates?
   if w is an empty list, yes
   if w is a single terminal, no
   if w is a single nonterminal, look it up
   if w is a non-empty list, "iterate" over elements *)
let rec generates_epsilon (w:string list) (kdg:knowledge) gram : bool =
  match w with
  | [] -> true
  | h :: t -> if is_terminal h gram then false
              else eps_field (get_symbol_knowledge h kdg)
                   && generates_epsilon t kdg gram;;

(* Return FIRST(w), based on current estimates.
   if w is an empty list, return []  [empty set]
   if w is a single terminal, return [w]
   if w is a single nonterminal, look it up
   if w is a non-empty list, "iterate" over elements *)
let rec first (w:string list) (kdg:knowledge) gram : (string list) =
  match w with
  | [] -> []
  | x :: _ when is_terminal x gram -> [x]
  | x :: rest -> let s = first_field (get_symbol_knowledge x kdg) in
                 if generates_epsilon [x] kdg gram
                 then union s (first rest kdg gram)
                 else s;;

let follow (a:string) (kdg:knowledge) : string list =
  follow_field (get_symbol_knowledge a kdg);;

let rec map3 f l1 l2 l3 =
  match (l1, l2, l3) with
  | ([], [], []) -> []
  | (h1 :: t1, h2 :: t2, h3 :: t3) -> (f h1 h2 h3) :: map3 f t1 t2 t3
  | _ -> raise (Failure "mismatched_lists");;

(* Return knowledge structure for grammar.
   Start with (initial_knowledge grammar) and "iterate",
   until the structure doesn't change.
   Uses (get_right_context B gram), for all nonterminals B,
   to help compute follow sets. *)
let get_knowledge gram : knowledge =
  let nts : string list = nonterminals gram in
  let right_contexts : right_context list
     = map (fun s -> get_right_context s gram) nts in
  let rec helper kdg =
    let update : symbol_knowledge -> symbol_productions
                   -> right_context -> symbol_knowledge
          = fun old_sym_kdg sym_prods sym_right_context ->
      let my_first s = first s kdg gram in
      let my_eps s = generates_epsilon s kdg gram in
      let filtered_follow p = if my_eps (snd p)
                              then (follow (fst p) kdg)
                              else [] in
      (
        symbol_field old_sym_kdg,       (* nonterminal itself *)
        (eps_field old_sym_kdg)         (* previous estimate *)
            || (fold_left (||) false (map my_eps (snd sym_prods))),
        union (first_field old_sym_kdg) (* previous estimate *)
            (fold_left union [] (map my_first (snd sym_prods))),
        union (union
                (follow_field old_sym_kdg)  (* previous estimate *)
                (fold_left union [] (map my_first
                                      (map (fun p ->
                                              match snd p with
                                              | [] -> []
                                              | h :: t -> [h])
                                           sym_right_context))))
              (fold_left union [] (map filtered_follow sym_right_context))
      ) in    (* end of update *)
    let new_kdg = map3 update kdg gram right_contexts in
    (* body of helper: *)
    if new_kdg = kdg then kdg else helper new_kdg in
  (* body of get_knowledge: *)
  helper (initial_knowledge gram);;

let get_parse_table (gram:grammar) : parse_table =
  let kdg = get_knowledge gram in
  map (fun (lhs, rhss) ->
        (lhs, (map (fun rhs ->
                      (union (first rhs kdg gram)
                             (if (generates_epsilon rhs kdg gram)
                              then (follow lhs kdg) else []),
                      rhs))
                   rhss)))
      gram;;

(* convert string to list of char *)
let explode (s:string) : char list =
  let rec exp i l = if i < 0 then l else exp (i-1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

(* convert list of char to string
   (This uses imperative features.  It used to be a built-in.) *)
let implode (l:char list) : string =
  let res = Bytes.create (length l) in
  let rec imp i l =
    match l with
    | [] -> Bytes.to_string res
    | c :: l -> Bytes.set res i c; imp (i + 1) l in
  imp 0 l;;

(*******************************************************************
   scanner:
 *******************************************************************)

type token = string * string;;
(*         category * name *)

let tokenize (program:string) : token list =
  let get_id prog =
    let rec gi tok p =
        match p with
        | c :: rest when (('a' <= c && c <= 'z')
                       || ('A' <= c && c <= 'Z')
                       || ('0' <= c && c <= '9') || (c = '_'))
            -> gi (c :: tok) rest
        | _ -> (implode (rev tok), p) in
    gi [] prog in
  let get_int prog =
    let rec gi tok p =
        match p with
        | c :: rest when ('0' <= c && c <= '9')
            -> gi (c :: tok) rest
        | _ -> (implode (rev tok), p) in
    gi [] prog in
  let get_num prog =
    let (tok, rest) = get_int prog in
    match rest with
    | '.' :: c :: r when ('0' <= c && c <= '9')
        -> let (tok2, rest2) = get_int (c :: r) in
           ((tok ^ "." ^ tok2), rest2)
    | _ -> (tok, rest) in
  let rec get_error tok prog =
    match prog with
    | [] -> (implode (rev tok), prog)
    | c :: rest ->
        match c with
        | ':' | '+' | '-' | '*' | '/' | '(' | ')' | '_'
        | '<' | '>' | '=' | 'a'..'z' | 'A'..'Z' | '0'..'9'
            -> (implode (rev tok), prog)
        | _ -> get_error (c :: tok) rest in
  let rec skip_space prog =
    match prog with
    | [] -> []
    | c :: rest -> if (c = ' ' || c = '\n' || c = '\r' || c = '\t')
                      then skip_space rest else prog in
  let rec tkize toks prog =
    match prog with
    | []                 -> (("$$" :: toks), [])
    | '\n' :: rest
    | '\r' :: rest
    | '\t' :: rest
    | ' ' :: rest        -> tkize toks (skip_space prog)
    | ':' :: '=' :: rest -> tkize (":=" :: toks) rest
    | '-' :: rest        -> tkize ("-"  :: toks) rest
    | '+' :: rest        -> tkize ("+"  :: toks) rest
    | '/' :: rest        -> tkize ("/"  :: toks) rest
    | '*' :: rest        -> tkize ("*"  :: toks) rest
    | '(' :: rest        -> tkize ("("  :: toks) rest
    | ')' :: rest        -> tkize (")"  :: toks) rest
    | '<' :: '>' :: rest -> tkize ("<>" :: toks) rest
    | '<' :: '=' :: rest -> tkize ("<=" :: toks) rest
    | '<' :: rest        -> tkize ("<"  :: toks) rest
    | '>' :: '=' :: rest -> tkize (">=" :: toks) rest
    | '>' :: rest        -> tkize (">"  :: toks) rest
    | '=' :: '=' :: rest -> tkize ("==" :: toks) rest
    | h :: t -> match h with
           | '0'..'9' -> let (t, rest) = get_num prog in
                         tkize (t :: toks) rest
           | 'a'..'z'
           | 'A'..'Z'
           | '_'      -> let (t, rest) = get_id prog in
                         tkize (t :: toks) rest
           | c        -> let (t, rest) = get_error [c] t in
                         tkize (t :: toks) rest in
  let (toks, _) = (tkize [] (explode program)) in
  let categorize tok =
    match tok with
    | "check" | "do" | "fi"
    | "if"    | "od" | "read" | "write"
    | ":=" | "+"  | "-"  | "*"  | "/"  | "("  | ")"
    | "<"  | "<=" | ">"  | ">=" | "==" | "<>" | "$$"
        -> (tok, tok)
    | _ -> match tok.[0] with
           | '0'..'9' -> ("num", tok)
           | 'a'..'z'
           | 'A'..'Z' | '_' -> ("id", tok)
           | _ -> ("error", tok) in
  map categorize (rev toks);;

(*******************************************************************
   The main parse routine below returns a parse tree (or PT_error if
   the input program is syntactically invalid).  To build that tree it
   employs a simplified version of the "attribute stack" described in
   Section 4.5.2 (pages 50-55) on the PLP companion site.
  
   When it predicts A -> B C D, the parser pops A from the parse stack
   and then, before pushing D, C, and B (in that order), it pushes a
   number (in this case 3) indicating the length of the right hand side.
   It also pushes A into the attribute stack.
  
   When it matches a token, the parser pushes this into the attribute
   stack as well.
  
   Finally, when it encounters a number (say k) in the stack (as opposed
   to a character string), the parser pops k+1 symbols from the
   attribute stack, joins them together into a list, and pushes the list
   back into the attribute stack.
  
   These rules suffice to accumulate a complete parse tree into the
   attribute stack at the end of the parse.
  
   Note that everything is done functionally.  We don't really modify
   the stacks; we pass new versions to a tail recursive routine.
 *******************************************************************)

(* Extract grammar from parse-tab, so we can invoke the various routines
   that expect a grammar as argument. *)
let grammar_of (parse_tab:parse_table) : grammar =
    map (fun p -> (fst p, (fold_left (@) [] (map (fun (a, b) -> [b])
                                                 (snd p))))) parse_tab;;

type parse_tree =   (* among other things, parse_trees are *)
| PT_error          (* the elements of the attribute stack *)
| PT_id of string
| PT_num of string
| PT_term of string
| PT_nt of (string * parse_tree list);;
    
(* Pop rhs-len + 1 symbols off the attribute stack,
   assemble into a production, and push back onto the stack. *)
let reduce_1_prod (astack:parse_tree list) (rhs_len:int) : parse_tree list =
  let rec helper atk k prod =
    match (k, atk) with
    | (0, PT_nt(nt, []) :: rest) -> PT_nt(nt, prod) :: rest
    | (n, h :: rest) when n <> 0 -> helper rest (k - 1) (h :: prod)
    | _ -> raise (Failure "expected nonterminal at top of astack") in
   helper astack rhs_len [];;

let sum_ave_prog = "read a read b sum := a + b write sum write sum / 2";;
let primes_prog = "
     read n
     cp := 2
     do check n > 0
         found := 0
         cf1 := 2
         cf1s := cf1 * cf1
         do check cf1s <= cp
             cf2 := 2
             pr := cf1 * cf2
             do check pr <= cp
                 if pr == cp
                     found := 1
                 fi
                 cf2 := cf2 + 1
                 pr := cf1 * cf2
             od
             cf1 := cf1 + 1
             cf1s := cf1 * cf1
         od
         if found == 0
             write cp
             n := n - 1
         fi
         cp := cp + 1
     od";;

 

type parse_action = PA_error | PA_prediction of string list;;
(* Double-index to find prediction (list of RHS symbols) for
   nonterminal nt and terminal t.
   Return PA_error if not found. *)
let get_parse_action (nt:string) (t:string) (parse_tab:parse_table) : parse_action =
    let rec helper l =
        match l with
        | [] -> PA_error
        | (fs, rhs) :: rest -> if member t fs then PA_prediction(rhs)
                               else helper rest in
    helper (assoc nt parse_tab);;

type ps_item =
| PS_end of int
| PS_sym of string;;

(* Parse program according to grammar.
   [Commented-out code would
       print predictions and matches (imperatively) along the way.]
   Return parse tree if the program is in the language; PT_error if it's not. *)
let parse (parse_tab:parse_table) (program:string) : parse_tree =
  let die msg = begin
                  print_string ("syntax error: " ^ msg);
                  print_newline ();
                  PT_error 
                end in
  let gram = grammar_of parse_tab in
  let rec helper pstack tokens astack =
    match pstack with
    | [] ->
        if tokens = [] then
          (* assert: astack is nonempty *)
          hd astack
        else die "extra input beyond end of program"
    | PS_end(n) :: ps_tail ->
        helper ps_tail tokens (reduce_1_prod astack n)
    | PS_sym(tos) :: ps_tail ->
        match tokens with
        | [] -> die "unexpected end of program"
        | (term, tok) :: more_tokens ->
           (* if tok is an individual identifier or number,
              term will be a generic "id" or "num" *)
          if is_terminal tos gram then
            if tos = term then
              begin
                (*
                print_string ("   match " ^ tos);
                print_string
                    (if tos <> term      (* value comparison *)
                         then (" (" ^ tok ^ ")") else "");
                print_newline ();
                *)
                helper ps_tail more_tokens
                       (( match term with
                          | "id"  -> PT_id tok
                          | "num" -> PT_num tok
                          | _     -> PT_term tok ) :: astack)
              end
                       (* note push of tok into astack *)
            else die ("expected " ^ tos ^ " ; saw " ^ tok)
          else (* nonterminal *)
            match get_parse_action tos term parse_tab with
            | PA_error -> die ("no prediction for " ^ tos
                               ^ " when seeing " ^ tok)
            | PA_prediction(rhs) ->
                begin
                  (*
                  print_string ("   predict " ^ tos ^ " ->");
                  print_string (fold_left (fun a b -> a ^ " " ^ b) "" rhs);
                  print_newline ();
                  *)
                  helper ((fold_left (@) [] 
                                    (map (fun s -> [PS_sym(s)]) rhs))
                              @ [PS_end(length rhs)] @ ps_tail)
                         tokens (PT_nt(tos, []) :: astack)
                end in
  helper [PS_sym(start_symbol gram)] (tokenize program) [];;

let cg_parse_table = get_parse_table calc_gram;;

let ecg_parse_table = get_parse_table ecg;;

(* print_string (snd (translate (ast_ize_P (parse ecg_parse_table primes_prog))));; *)

(*******************************************************************
  Everything above this point in the file is complete and (I think)
  usable as-is.  The rest of the file, from here down, is a skeleton
  for the extra code you need to write.  It has been excised from my
  working solution to the assignment.  You are welcome, of course, to
  use a different organization if you prefer.  This is provided in the
  hope you may find it useful.
 *******************************************************************)

type ast_sl = ast_s list
and ast_s =
| AST_error
| AST_assign of (string * ast_e)
| AST_read of string
| AST_write of ast_e
| AST_if of (ast_e * ast_sl)
| AST_do of ast_sl
| AST_check of ast_e
and ast_e =
| AST_binop of (string * ast_e * ast_e)
| AST_id of string
| AST_num of string;;

let rec ast_ize_P (p:parse_tree) : ast_sl =
  (* your code should replace the following line *)
  match p with
  | PT_nt ("P", [statement_list; PT_term "$$"]) 
        -> (ast_ize_SL statement_list)
  | _ -> raise (Failure "malformed parse tree in ast_ize_P")

and ast_ize_SL (sl:parse_tree) : ast_sl =
  match sl with
  | PT_nt ("SL", []) -> []
  (*
     your code here ...
  *)
  | PT_nt ("SL", [statement; statement_list])
        -> (ast_ize_S statement)::(ast_ize_SL statement_list) 
  (*Concatanating two AST together*)
  | _ -> raise (Failure "malformed parse tree in ast_ize_SL")

and ast_ize_S (s:parse_tree) : ast_s =
  match s with
  | PT_nt ("S", [PT_id lhs; PT_term ":="; expr])
        -> AST_assign (lhs, (ast_ize_expr expr))
  (*
     your code here ...
  *)
  | PT_nt ("S", [PT_term "read"; PT_id rhs]) 
        -> AST_read (rhs)
  | PT_nt ("S", [PT_term "write"; expr]) 
        -> AST_write (ast_ize_expr expr)
  | PT_nt ("S", [PT_term "if"; relation ; statement_list; PT_term "fi"]) 
        -> AST_if (ast_ize_expr relation, ast_ize_SL statement_list)
  | PT_nt ("S", [PT_term "do"; statement_list ; PT_term "od"]) 
        -> AST_do (ast_ize_SL statement_list)
  | PT_nt ("S", [PT_term "check"; relation]) 
        -> AST_check (ast_ize_expr relation)
  | _ -> raise (Failure "malformed parse tree in ast_ize_S")

and ast_ize_expr (e:parse_tree) : ast_e =
  (* e is an R, E, T, or F parse tree node *)
  match e with
  (*
     your code here ...
  *)
  | PT_nt ("R", [expr; expr_tail]) 
        -> ast_ize_reln_tail (ast_ize_expr(expr)) (expr_tail)
  | PT_nt ("E", [term; term_tail]) 
        -> ast_ize_expr_tail (ast_ize_expr(term)) (term_tail)
  | PT_nt ("T", [factor; factor_tail]) 
        -> ast_ize_expr_tail (ast_ize_expr(factor)) (factor_tail)
  | PT_nt ("F", [PT_id id]) 
        -> AST_id (id)
  | PT_nt ("F", [PT_num num]) 
        -> AST_num (num)
  | PT_nt ("F", [PT_term "("; expr ; PT_term ")"]) 
        -> ast_ize_expr (expr)
  | _ -> raise (Failure "malformed parse tree in ast_ize_expr")

and ast_ize_reln_tail (lhs:ast_e) (tail:parse_tree) : ast_e =
  (* lhs in an inheritec attribute.
     tail is an ET parse tree node *)
  match tail with
  | PT_nt ("ET", []) -> lhs
  | PT_nt ("ET", [PT_nt (ro, [PT_term operator]); expr]) -> AST_binop (operator, lhs, ast_ize_expr(expr))
  | _ -> raise (Failure "malformed parse tree in ast_ize_reln_tail")

and ast_ize_expr_tail (lhs:ast_e) (tail:parse_tree) : ast_e =
  (* lhs in an inherited attribute.
     tail is a TT or FT parse tree node *)
  match tail with
  (*
     your code here ...
  *)
  | PT_nt ("TT", []) -> lhs
  | PT_nt ("FT", []) -> lhs
  | PT_nt ("TT", [PT_nt (ao, [PT_term operator]); term; term_tail]) 
        -> AST_binop (operator, lhs, (ast_ize_expr_tail(ast_ize_expr(term)) term_tail) )
  | PT_nt ("FT", [PT_nt (mo, [PT_term operator]); factor; factor_tail]) 
        -> AST_binop (operator, lhs, (ast_ize_expr_tail(ast_ize_expr(factor)) factor_tail) )
  | _ -> raise (Failure "malformed parse tree in ast_ize_expr_tail")
;;

(*
#use "translator.ml";;
*)

let p = "
          read a
          read b
          read c
          sum := ((a*b)+(b*c)+(c*a))/3
          write sum";; 

(* let p = "
          read a b
          read c
          sum := ((a*b)+(b*c)+(c*a))/3
          write sum";;  *) 
(*
  let p = "
          read n
      m := n
      sum := 0
      do check m > 0
      read token
      sum := sum + token
      m := m - 1
      od
      sum := sum / n
      write sum";; *)
       
(*
  let p = "
      read n
      k := 0
      sum := 0
      do 
      check k < n
      read token
      k := k + 1
      sum := sum + token
      fi 
      od
      sum := sum / n
      write sum ";;
*)

let tree = parse ecg_parse_table primes_prog;;
ast_ize_P tree;; 
(* let tree2 = parse ecg_parse_table sum_ave_prog;;
ast_ize_P tree2;; *)

(*******************************************************************
    Translate to C
 *******************************************************************)

(* The code below is (obviously) a bare stub.  The intent is that when
   you run translate on a full, correct AST, you'll get back code for an
   equivalent C program.  If there are any variables that are written in
   the program but never read, you'll also get a warning message
   indicating their names and the lines on which the writes occur.  Your
   C program should contain code to check for dynamic semantic errors. *)

(*  commented out so this code will complile *)

    (* warnings  output_program *) 
    

let rec translate (ast:ast_sl) (helper:string) :  string *  string = ("", helper^snd(translate_sl (ast))^"}\n")

and translate_sl (ast:ast_sl)  :  string *  string = 
  match ast with 
  | h :: t
    -> (fst (translate_s h)) ^ fst (translate_sl t), snd(translate_s h) ^ snd (translate_sl t)
  | _ -> ("","")
and translate_s (ast:ast_s)  :  string *  string = 
  match ast with
  | AST_assign id_e-> translate_assign ast
  | AST_read id -> translate_read ast
  | AST_write e -> translate_write ast
  | AST_if e_sl-> translate_if ast
  | AST_do sl -> translate_do ast
  | AST_check e -> translate_check ast
  | _ -> raise (Failure "Translate s ")

and translate_assign (ast:ast_s)  :  string *  string = 
  match ast with
  | AST_assign (id, e) -> ("", "setvar(" ^ "\"" ^id ^ "\", " ^ snd(translate_expr e) ^ ");\n")
  | _ -> raise (Failure "Translate assign ")

and translate_read (ast:ast_s)  :  string *  string = 
  match ast with
  | AST_read id-> ("", "setvar(" ^ "\"" ^id ^ "\", getint()); \n")
  | _ -> raise (Failure "Translate read ")

and translate_write (ast:ast_s)  :  string *  string = 
  match ast with
  | AST_write e -> ("",  "putint(" ^ snd (translate_expr e) ^ ");\n")
  | _ -> raise (Failure "Translate write ")

and translate_if (ast:ast_s)  :  string *  string = 
  match ast with
  | AST_if (e, sl) -> ( "","if (" ^ snd( translate_expr e) ^ ")\n {\n" ^ snd( translate_sl sl) ^ "}\n")
  | _ -> raise (Failure "Translate if ")

and translate_do (ast:ast_s)  :  string *  string = 
  match ast with
  | AST_do sl -> ("", "while (1) {" ^ snd( translate_sl sl) ^ "}\n")
  | _ -> raise (Failure "Translate do ")

and translate_check (ast:ast_s)  :  string *  string = 
  match ast with
  | AST_check e -> ("", "if(!(" ^ snd( translate_expr e) ^ ")) break;\n")
  | _ -> raise (Failure "Translate check ")

and translate_expr (ast:ast_e)  :  string *  string = 
  match ast with
  | AST_binop ("/", e1, e2) -> ("", "divide (" ^ snd( translate_expr e1) ^ ", " ^ snd( translate_expr e2) ^ ") ")
  | AST_binop (op, e1, e2 )-> ("", snd( translate_expr e1) ^ op ^ snd( translate_expr e2))
  | AST_id id -> ("", "getvar( \"" ^ id ^ "\"" ^ ")")
  | AST_num num -> ("", num);;

(*
#use "translator.ml";;
*)
(*print_string (snd translate( ast_ize_P tree)) ;;*)
let  helper = "
    #include <stdio.h>
    #include <stdlib.h>
    #include <string.h>

    int array[100];
    char* string[100];

    int getint1() {
      int num;
      if(scanf(\"%d\", &num) == 1){
        return num;
      }else{
        printf(\"wrong in getint!!\");
        return -1;
        exit(1);
      }
    }

    int getint() {
      char str[100];
      if(scanf(\"%s\", &str) != 1){
        printf(\"Unexpected end of input!\\n\");
        exit(1);
      }else{
        for(int k = 0; str[k]!='\\0' ; k++){
          if(str[k] >'9' || str[k] <'0'){
            printf(\"non numeric input!\\n\");
            exit(1);
          }
        }
        return atoi(str);
      }
    }

    void putint(int n) {
      printf(\"%d\\n\", n);
    }

    int divisionE(){
      printf(\"A division by zero erro here!\\n\");
      exit(1);
      return 1;
    }
    
    int divide (int a, int b){
      if(b == 0){
        divisionE();
      }
      return a/b ;
    }
    

    int getvar(char* a){
      for(int i = 0; string [i] != '\\0';i++){
        if(!strcmp(string[i],a)){
          return array[i];
        }
      }
      printf(\"Use of uninitialized variable %s\\n\", a);
      exit (1);
    }

    int setvar(char* a, int n){
      int i;
      for(i = 0; string [i] != '\\0';i++){
        if(!strcmp(string[i],a)){
          array[i] = n;
          return 1;
        }
      }
      string[i] = a;
      array[i] = n; 
      return 0;
    }
    
    
    
    int main(int argc, char* argv[]) {


    ";;


let prog = "read a
        read b
        write a / b";;    


print_string (snd (translate (ast_ize_P (parse ecg_parse_table primes_prog)) helper));;


print_string (snd (translate (ast_ize_P (parse ecg_parse_table prog)) helper));; 

