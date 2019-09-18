# Regular-Expression-Interpreter

This project is an Ocaml program which interprets regular expression. 
The project has three parts: algorithms on NFAs; converting an NFA to a DFA; and converting/working with Regular Expressions. 
NFAs and DFAs are implemented in src/nfa.ml, and regexes in src/regex.ml.

## NFAs

This first part of the project includes some functions for working with NFAs. In particular,it implements the *move* and *epsilon closure* functions and`accept` function to determine whether a string is matched by a given NFA.

### NFA Types

The type `nfa_t` is the type representing NFAs. It is modeled after the formal definition of an NFA, a 5-tuple (Σ, Q, q0, F, δ) where:

1. Σ is a finite alphabet,
2. Q is a finite set of states,
3. q0 ∈ Q is the start state,
5. F ⊆ Q is the set of accept states, and
4. δ : Q × (Σ ∪ {ε}) → P(Q) is the transition function.

We translate this definition into OCaml in a straightforward way using record syntax:

```
type ('q, 's) transition = 'q * 's option * 'q
type ('q, 's) nfa_t = {
    sigma : 's list;
    qs : 'q list;
    q0 : 'q;
    fs : 'q list;
    delta : ('q, 's) transition list;
}
```

### Functions

**move nfa l c**

* **Type:** `('q, 's) nfa_t -> 'q list -> 's option -> 'q list`
* **Description:** This function takes as input an NFA, a list of initial states, and a symbol option. The output will be a list of states (in any order, with no duplicates) that the NFA might be in after making one transition on the symbol (or epsilon if None), starting from one of the initial states given as an argument to move. If `c` is not in the alphabet (`sigma`), then return the empty list.
* **Examples:**
```
move nfa_ex [0] (Some 'a') = [1] (* nfa_ex is the NFA defined above *)
move nfa_ex [1] (Some 'a') = []
move nfa_ex [2] (Some 'a') = []
move nfa_ex [0;1] (Some 'a')  = [1]
move nfa_ex [1] None = [2]
```

**e_closure nfa l**

* **Type:** `('q, 's) nfa_t -> 'q list -> 'q list`
* **Description:** This function takes as input an NFA and a list of states. The output will be a list of states (in any order, with no duplicates) that the NFA might be in making zero or more epsilon transitions, starting from the list of initial states given as an argument to `e_closure`. You can assume you will always be passed in a state that is in `nfa`'s states list.
* **Examples:**
```
e_closure nfa_ex [0] = [0]
e_closure nfa_ex [1] = [1;2]
e_closure nfa_ex [2]  = [2]
e_closure nfa_ex [0;1] = [0;1;2]
```

**accept nfa s**

* **Type:** `('q, char) nfa_t -> string -> bool`
* **Description:** This function takes an NFA and a string, and returns true if the NFA accepts the string, and false otherwise. You will find the functions in the [`String` module][string doc] to be helpful. (You might find it useful to use `nfa_to_dfa`, implemented in Part 2 below, as part of your `accept` implementation, but this is not required.)
* **Examples:**
```
accept dfa_ex "" = false  (* dfa_ex is the NFA defined above *)
accept dfa_ex "ac" = true
accept dfa_ex "abc" = false
accept dfa_ex "abac" = true
```

## DFAs

In this part, our goal is to implement the `nfa_to_dfa` function. It uses the subset construction to convert an NFA to a DFA. 

### Functions
**new_states nfa qs**
* **Type:** `('q, 's) nfa_t -> 'q list -> 'q list list`
* **Description:** Given an NFA and a list of states from that NFA (a single state in the DFA) computes all the DFA states that you can get to from a transition out of `qs` (including the dead state).
* **Examples:**
```
new_states dfa_ex [0] = [[1]; []; []]
new_states dfa_ex [0; 1] = [[1]; [0]; [2]]
```

**new_trans nfa qs**
* **Type:** `('q, 's) nfa_t -> 'q list -> ('q list, 's) transition list`
* **Description:** Given an NFA and a list of states from that NFA (a single state in the DFA) computes all the transitions coming from `qs` (including the dead state) in the DFA.
* **Examples:**
```
new_trans dfa_ex [0; 1] = [([0; 1], Some 'a', [1]); ([0; 1], Some 'b', [0]); ([0; 1], Some 'c', [2])]
```

**new_finals nfa qs**
* **Type:** `('q, 's) nfa_t -> 'q list -> 'q list list`
* **Description:** Given an NFA and a list of states from that NFA (a single state in the DFA) returns `[qs]` if `qs` is final in the DFA and `[]` otherwise.
* **Examples:**
```
new_finals dfa_ex [0; 1; 2] = [[0; 1; 2]]
new_finals dfa_ex [0; 1] = []
```

**nfa_to_dfa nfa**
* **Type:** `('q, 's) nfa_t -> ('q list, 's) nfa_t`
* **Description:** This function takes as input an NFA and converts it to an equivalent DFA. The language recognized by an NFA is invariant under `nfa_to_dfa`. In other words, for all NFAs `nfa` and for all strings `s`, `accept nfa s = accept (nfa_to_dfa nfa) s`. 

## Regular Expressions

For the last part of the project, it implements code to convert a regular expression (in the format given below) to an NFA. The `Regexp` module represents a regular expression with the type `regexp_t`:
```
type regexp_t =
  | Empty_String
  | Char of char
  | Union of regexp * regexp
  | Concat of regexp * regexp
  | Star of regexp
```
This datatype represents regular expressions as follows:
* `Empty_String` represents the regular expression recognizing the empty string (not the empty set!). Written as a formal regular expression, this would be `epsilon`.
* `Char c` represents the regular expression that accepts the single character c. Written as a formal regular expression, this would be `c`.
* `Union (r1, r2)` represents the regular expression that is the union of r1 and r2. For example, `Union(Char 'a', Char'b')` is the same as the formal regular expression `a|b`.
* `Concat (r1, r2)` represents the concatenation of r1 followed by r2. For example, `Concat(Char 'a', Char 'b')` is the same as the formal regular expresion `ab`.
* `Star r` represents the Kleene closure of regular expression r. For example, `Star (Union (Char 'a', Char 'b'))` is the same as the formal regular expression `(a|b)*`.


### Functions 
**regexp_to_nfa regexp**

* **Type:** `regexp_t -> nfa_t`
* **Description:** This function takes a regexp and returns an NFA that accepts the same language as the regular expression. 

**explode s**
* **Type:** `string -> char list`
* **Description:** This function takes a string and converts it into a character list. The following function may be helpful when writing `accept` in Part 1.

**fresh**
* **Type:** `unit -> int`
* **Description:** This function takes in type `unit` as an argument (similar to Null). This function uses imperative OCaml to return an `int` value that has not been used before by using a reference to a counter. 
* **Examples:**
```
fresh() = 1
fresh() = 2
fresh() = 3
... 
```

**string_to_nfa s**
* **Type:** `string -> nfa`
* **Description:** This function takes a string for a regular expression, parses the string, converts it into a regexp, and transforms it to an nfa.

**string_to_regexp s** 
* **Type:** `string -> regexp`
* **Description:** This function takes a string for a regular expression, parses the string, and outputs its equivalent regexp. If the parser determines that the regular expression has illegal syntax, it will raise an IllegalExpression exception.
* **Examples:**
```
string_to_regexp "a" = Char 'a'
string_to_regexp "(a|b)" = Union (Char 'a', Char 'b')
string_to_regexp "ab" = Concat(Char 'a',Char 'b')
string_to_regexp "aab" = Concat(Char 'a',Concat(Char 'a',Char 'b'))
string_to_regexp "(a|E)*" = Star(Union(Char 'a',Empty_String))
string_to_regexp "(a|E)*(a|b)" = Concat(Star(Union(Char 'a',Empty_String)),Union(Char 'a',Char 'b'))
```
