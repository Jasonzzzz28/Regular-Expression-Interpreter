open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)
let rec srl x a = match a with  
| [] -> false   
| s::t -> if s= x then true else srl x t;;

let rec remsame l resu =
match l with
| []-> resu
| h::t -> if List.mem h resu =true then remsame t resu else remsame t (h::resu);;

let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list = 
(*if s = None then
match nfa with
{sigma=_;qs=_;q0=_;fs=_;delta = de}-> List.fold_right (fun h a ->
match h with
| (x, None, y) ->
if srl x qs=true then y::a else a
| _ -> a)
de []

else*) let Some k =s in
match nfa with
{sigma=_;qs=_;q0=_;fs=_;delta = de}-> let result = (List.fold_right (fun h a ->
match h with
| (x,Some op, y)->
if List.mem x qs =true && op= k then y::a else a
| (x, None, y) -> a)
de []) in
remsame result [];;


let rec helpremtwo s record = 
List.fold_right (fun x a-> if List.mem x record=true then a else x::a) s [];;


let rec echelper nfa qll visited res=
let ql = helpremtwo qll visited in
if ql=[] then res
else match nfa with 
{sigma=_;qs=_;q0=_;fs=_;delta=d} ->
let omg = (List.fold_right (fun h a ->match h with
| (x,None,y)->
if (List.mem x ql =true && List.mem x res =false && List.mem y res =false  && List.mem y ql =false) then y::a else a
| _ -> a) d []) in
echelper nfa omg (ql@visited) (ql@res);;

let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
echelper nfa qs [] [];;

let rec sameele l ls =
match l with
| []-> false
| h::t -> if (List.mem h ls) = true then true else (sameele t ls);;

let rec acchelp nfa st slst =
let {sigma=_;qs=_;q0=_;fs= final;delta=de} = nfa in
match slst with
| []-> if sameele st final =false then false else true 
| h::t -> let newst = e_closure nfa (move nfa (e_closure nfa st) (Some h)) in
                      if newst = [] then false
                      else acchelp nfa newst t;;


let accept (nfa: ('q,char) nfa_t) (s: string) : bool =
match nfa with {sigma=_;qs=_;q0= start;fs=fss;delta=_}->
if not (s = "") then
acchelp nfa [start] (explode s)
else sameele (e_closure nfa [start]) fss;;  


(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
let el = e_closure nfa qs in
match nfa with
{sigma=k; qs=_;q0=_;fs=_;delta=de} ->List.map (fun si ->
		     e_closure nfa (List.fold_right (fun h b-> match h with
					  | (x,Some op, y) -> if srl x el =true && op =si then y::b else b
                                          | _ -> b) de [] )) k;;

let rec remdup lst a =
match lst with
| []-> a
| h::t -> if srl h a = true then remdup t a
else remdup t (h::a);;

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
let ls = e_closure nfa qs in
match nfa with
{sigma=k ;qs=_;q0=_;fs=_;delta=de} -> List.map (fun si ->
                                     (qs, Some si, e_closure nfa (remdup (List.fold_right (fun h b-> match h with
					  | (x,Some op, y) -> if srl x ls =true && op =si then y::b else b
                                          | _ -> b) de []) []) )
) k;;

let tranhelper nfa qs =
let ls = e_closure nfa qs in
match nfa with
{sigma=k ;qs=_;q0=_;fs=_;delta=de} -> List.map (fun si ->
                                    e_closure nfa (remdup (List.fold_right (fun h b-> match h with
					  | (x,Some op, y) -> if srl x ls =true && op =si then y::b else b
                                          | _ -> b) de []) []) 
) k;; 


let rec sll x a =
match x with
| []-> false 
| h::t -> if srl h a =true then true else sll t a;;

let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
match nfa with
{sigma=_;qs=_;q0=_;fs=k;delta=_} ->
if (sll k qs) =true then [qs]
else [];;

let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t)
    (work: 'q list list) : ('q list, 's) nfa_t =
  failwith "unimplemented"

(* many many small helpers*)

let rec eqlst ls lt =
let es = List.sort compare ls in
let rcv = List.sort compare lt in
if es = rcv then true else false;;

let rec searchls x a=
match a with  
| [] -> false   
| h::t -> if eqlst h x then true else searchls x t;;

let rec remls lst a =
match lst with
| []-> a
| h::t -> if searchls h a = true then remls t a
else remls t (h::a);;

let rec remempty ls result=
match ls with
| [] ->result
| h::t -> if h= [] then remempty t result else remempty t (h::result);;

let rec removetwo s record =
List.fold_right (fun x a-> if searchls x record=true then a else x::a) s [];;

(* end of small helpers*)


(* some big helpers *)

let rec getstates nfa states res =
let afrem = removetwo states res in
if afrem =[] then res
else 
getstates nfa (List.fold_right (fun x a-> (remempty (tranhelper nfa x) [])@ a ) afrem []) (afrem @ res);;

let getfinal nfa ls =
List.fold_right (fun x a -> (new_finals nfa x) @ a) ls [];;

let getdelta nfa ls=
List.fold_right (fun x a-> (new_trans nfa x) @ a) ls [];; 

(*end of big helpers*)

let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t =
match nfa with
{sigma=h ;qs=_;q0= k ;fs=_;delta=de}->
let start = (e_closure nfa [k]) in
let t = remempty (tranhelper nfa start) [] in
let newqs = getstates nfa t [start] in
{sigma=h; qs= newqs; q0= start; fs= getfinal nfa newqs; delta= getdelta nfa newqs};; 








