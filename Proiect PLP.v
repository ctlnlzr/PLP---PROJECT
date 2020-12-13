(*Variabile*)
Inductive Var := a | b | c | d | e | i | n | m | sum | x | y | z.
Scheme Equality for Var.

Require Import String.
(*Integer*)
Inductive int :=
| pozitiv : nat -> int
| negativ : nat -> int.

(*Tipuri de date pentru declarare*)
Inductive Value :=
| undef : Value
| nat_val : nat -> Value
| bool_val : bool -> Value
| int_val : int -> Value
| string_val :string -> Value.

Scheme Equality for Value.

Definition Env := Var -> Value.

(*Expresii pentru nat, int, string, bool.*)
Inductive Exp :=
| anum : nat -> Exp
| aint : int -> Exp
| str : string -> Exp
| avar : Var -> Exp
| secv_val : Exp -> Exp -> Exp
| nplus : Exp -> Exp -> Exp
| nmul : Exp -> Exp -> Exp
| iplus : Exp -> Exp -> Exp
| imul : Exp -> Exp -> Exp
| concat : Exp -> Exp -> Exp
| eq_str : Exp -> Exp -> Exp
| btrue : Exp
| bfalse : Exp
| blessthan : Exp -> Exp -> Exp
| bnot : Exp -> Exp
| band : Exp -> Exp -> Exp.
Coercion anum : nat >-> Exp.
Coercion aint : int >-> Exp.
Coercion avar : Var >-> Exp.

Notation "A +' B" := (nplus A B) (at level 50, left associativity).
Notation "A *' B" := (nmul A B) (at level 49, left associativity).
Notation "A ++' B" := (iplus A B) (at level 50, left associativity).
Notation "A **' B" := (imul A B) (at level 49, left associativity).
Notation " A '/+/' B" :=(concat A B) (at level 50, left associativity).
Notation " A '=*' B" := (eq_str A B) (at level 60).
Notation "A <* B" := (blessthan A B) (at level 60).
Notation "!* A" := (bnot A) (at level 70).
Notation "A &* B" := (band A B) (at level 68).

(*Tipuri de date pe care le pot contine stiva, coada si array-ul.*)
Inductive Tip :=
| natural : nat -> Tip
| integer : int -> Tip
| boolean : bool -> Tip.

Coercion natural : nat >-> Tip.
Coercion integer : int >-> Tip.
Coercion boolean : bool >-> Tip.

Inductive Queue :=
 | nulq : Queue
 | elemq : Tip -> Queue -> Queue
 | addq : Queue -> Queue -> Queue
 | elimq : Queue -> Queue.
Notation "A 'q'+ B" := (addq A B) (at level 70).
Notation "A 'q'- B" := (elimq A B) (at level 71).
Notation "[]" := (nulq) (at level 100).
Notation "[ x ]" := (elemq x nulq) (at level 100).
Notation "[ x ; y ; .. ; z ]" := (elemq x (elemq y .. (elemq z nulq) ..)) (at level 100).

Inductive Stack :=
 | nuls : Stack
 | elems : Tip -> Stack -> Stack
 | adds : Stack -> Stack -> Stack
 | elims : Stack -> Stack.

Notation "A 's'+ B" := (adds A B) (at level 70).
Notation "A 's'- B" := (elims A B) (at level 71).
Notation "<>" := (nuls) (at level 100).
Notation "< x >" := (elems x nuls) (at level 100).
Notation "< x , y , .. , z >" := (elems x (elems y .. (elems z nuls) ..)) (at level 100).

Inductive Array :=
 | nula : Array
 | elema : Tip -> nat -> Array
 | sir : Array -> Array -> Array
 | adda : Array -> Tip -> nat -> Array
 | assig_new_val : Array -> nat -> Tip -> Array.
Notation " A1 \\ A2 " := (sir A1 A2) (at level 100).
Notation "\\" := (nuls) (at level 100).

Inductive Enum :=
 | nule : Enum
 | eleme : string -> Enum
 | adde : string -> Enum
 | elim : string -> Enum
 | sir_e: Enum -> Enum -> Enum.
Notation "//" := (nule) (at level 100).
Notation "E1 // E2" := (sir_e E1 E2) (at level 100).

Inductive Stmt :=
| skip : Stmt
| decl : Var -> Stmt
| decl_S : Stack -> Stmt
| decl_Q : Queue -> Stmt
| decl_A : Array -> Stmt
| decl_E : Enum -> Stmt
| assignment : Var -> Exp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| while : Exp -> Stmt -> Stmt
| ifthen : Exp -> Stmt -> Stmt.

Notation "A :=: B" :=(assignment A B) (at level 45).
Notation "S1 ;; S2" :=(seq S1 S2) (at level 57).
Notation "'iff' A 'thenn' S 'endd'" := (ifthen A S) (at level 60).

Inductive rez :=
| base : Tip -> rez
| show_a : Array -> nat -> rez
| show_e : Enum -> string -> rez
| func : string -> Exp -> Stmt -> rez.

Notation " A - N - " := (show_a A N) (at level 90).
Notation " E ~ S ~ ":= (show_e E S) (at level 90).
Notation " S1 'parametri:' E 'corp:' S2 'Final_f'" := (func S1 E S2) (at level 50). 

Inductive Typ : Type := Bool | Nat | Int | String .