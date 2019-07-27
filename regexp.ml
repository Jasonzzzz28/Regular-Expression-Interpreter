open List
open Nfa

(*********)
(* Types *)
(*********)

type regexp_t =
  | Empty_String
  | Char of char
  | Union of regexp_t * regexp_t
  | Concat of regexp_t * regexp_t
  | Star of regexp_t

(***********)
(* Utility *)
(***********)

let fresh =
  let cntr = ref 0 in
  fun () ->
    cntr := !cntr + 1 ;
    !cntr

(*******************************)
(* Part 3: Regular Expressions *)
(*******************************)
let rec srl x a = match a with  
| [] -> false   
| s::t -> if s= x then true else srl x t;;

let rec remtwo s record =
List.fold_right (fun x a-> if srl x record=true then a else x::a) s [];;


let rec regexp_to_nfa (regexp: regexp_t) : (int, char) nfa_t =
match regexp with 
| Empty_String->
let startstate = fresh() in
let endstate = fresh() in
{qs=[startstate;endstate]; sigma=[];q0=startstate; fs=[endstate]; delta=[(startstate,None,endstate)]}

| Char (char)-> 
let st = fresh() in
let ends = fresh() in
{qs=[st; ends]; sigma=[char];q0=st; fs=[ends]; delta=[(st,Some char,ends)]}

| Union (reg1, reg2)->
let {qs=qs1; sigma=s1; q0=q01; fs=fs1; delta=de1} = regexp_to_nfa reg1 in
let {qs=qs2; sigma=s2; q0=q02; fs=fs2; delta=de2} = regexp_to_nfa reg2 in
let start =fresh() in
let final =fresh() in
let newdel =[(start,None,q01);(start,None,q02)]@
( (List.fold_right (fun x a-> (x,None,final)::a) fs1 []) @ (List.fold_right (fun x b-> (x,None,final)::b) fs2 []) ) in
{qs= (start::final::(remtwo qs1 qs2))@ qs2; sigma= (remtwo s1 s2)@ s2;q0=start;fs=[final]; delta=newdel @(de1 @ de2) }

| Concat (reg1, reg2)->
let {qs=qs1; sigma=s1; q0=q01; fs=fs1; delta=de1} = regexp_to_nfa reg1 in
let {qs=qs2; sigma=s2; q0=q02; fs=fs2; delta=de2} = regexp_to_nfa reg2 in 
let newde = (List.fold_right (fun x a-> (x,None,q02)::a) fs1 []) in 
{qs= (remtwo qs1 qs2)@ qs2; sigma= (remtwo s1 s2)@ s2;q0=q01;fs=fs2; 
delta=(newde @ de1) @ de2} 

| Star (reg)->
let {qs=qs1; sigma=s1; q0=q01; fs=fs1; delta=de1} = regexp_to_nfa reg in
let starts =fresh() in
let finals =fresh() in
let newdelta =[(starts,None,finals);(finals,None,starts);(starts,None,q01)]
@ (List.fold_right (fun x a-> (x,None,finals)::a) fs1 [])in
{qs= starts::finals::qs1; sigma= s1;q0=starts;fs=[finals]; delta=newdelta @ de1 }

(*****************************************************************)
(* Below this point is parser code that YOU DO NOT NEED TO TOUCH *)
(*****************************************************************)

exception IllegalExpression of string

(* Scanner *)
type token =
  | Tok_Char of char
  | Tok_Epsilon
  | Tok_Union
  | Tok_Star
  | Tok_LParen
  | Tok_RParen
  | Tok_END

let tokenize str =
  let re_var = Str.regexp "[a-z]" in
  let re_epsilon = Str.regexp "E" in
  let re_union = Str.regexp "|" in
  let re_star = Str.regexp "*" in
  let re_lparen = Str.regexp "(" in
  let re_rparen = Str.regexp ")" in
  let rec tok pos s =
    if pos >= String.length s then [Tok_END]
    else if Str.string_match re_var s pos then
      let token = Str.matched_string s in
      Tok_Char token.[0] :: tok (pos + 1) s
    else if Str.string_match re_epsilon s pos then
      Tok_Epsilon :: tok (pos + 1) s
    else if Str.string_match re_union s pos then Tok_Union :: tok (pos + 1) s
    else if Str.string_match re_star s pos then Tok_Star :: tok (pos + 1) s
    else if Str.string_match re_lparen s pos then Tok_LParen :: tok (pos + 1) s
    else if Str.string_match re_rparen s pos then Tok_RParen :: tok (pos + 1) s
    else raise (IllegalExpression ("tokenize: " ^ s))
  in
  tok 0 str

let tok_to_str t =
  match t with
  | Tok_Char v -> Char.escaped v
  | Tok_Epsilon -> "E"
  | Tok_Union -> "|"
  | Tok_Star -> "*"
  | Tok_LParen -> "("
  | Tok_RParen -> ")"
  | Tok_END -> "END"

(*
   S -> A Tok_Union S | A
   A -> B A | B
   B -> C Tok_Star | C
   C -> Tok_Char | Tok_Epsilon | Tok_LParen S Tok_RParen

   FIRST(S) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(A) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(B) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(C) = Tok_Char | Tok_Epsilon | Tok_LParen
 *)

let parse_regexp (l : token list) =
  let lookahead tok_list =
    match tok_list with
    | [] -> raise (IllegalExpression "lookahead")
    | h :: t -> (h, t)
  in
  let rec parse_S l =
    let a1, l1 = parse_A l in
    let t, n = lookahead l1 in
    match t with
    | Tok_Union ->
        let a2, l2 = parse_S n in
        (Union (a1, a2), l2)
    | _ -> (a1, l1)
  and parse_A l =
    let a1, l1 = parse_B l in
    let t, n = lookahead l1 in
    match t with
    | Tok_Char c ->
        let a2, l2 = parse_A l1 in
        (Concat (a1, a2), l2)
    | Tok_Epsilon ->
        let a2, l2 = parse_A l1 in
        (Concat (a1, a2), l2)
    | Tok_LParen ->
        let a2, l2 = parse_A l1 in
        (Concat (a1, a2), l2)
    | _ -> (a1, l1)
  and parse_B l =
    let a1, l1 = parse_C l in
    let t, n = lookahead l1 in
    match t with Tok_Star -> (Star a1, n) | _ -> (a1, l1)
  and parse_C l =
    let t, n = lookahead l in
    match t with
    | Tok_Char c -> (Char c, n)
    | Tok_Epsilon -> (Empty_String, n)
    | Tok_LParen ->
        let a1, l1 = parse_S n in
        let t2, n2 = lookahead l1 in
        if t2 = Tok_RParen then (a1, n2)
        else raise (IllegalExpression "parse_C 1")
    | _ -> raise (IllegalExpression "parse_C 2")
  in
  let rxp, toks = parse_S l in
  match toks with
  | [Tok_END] -> rxp
  | _ -> raise (IllegalExpression "parse didn't consume all tokens")


let string_to_regexp str = parse_regexp @@ tokenize str

let string_to_nfa str = regexp_to_nfa @@ string_to_regexp str
