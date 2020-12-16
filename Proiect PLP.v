(*Variabile*)
Require Import Strings.String.
Local Open Scope list_scope.
Local Open Scope string_scope.
Scheme Equality for string.

(*Integer*)
Inductive int :=
| pozitiv : nat -> int
| negativ : nat -> int.
Notation "(+ N )" := (pozitiv N) (at level 10).
Notation "(- N )" := (negativ N) (at level 10).
Check (+ 5).
Check (- 5).

(*Expresii pentru nat, int, string, bool.*)
Inductive AExp :=
| anum : nat -> AExp
| avar : string -> AExp
| nplus : AExp -> AExp -> AExp
| nmul : AExp -> AExp -> AExp.
Coercion avar : string >-> AExp.
Coercion anum : nat >-> AExp.
Notation "A +' B" := (nplus A B) (at level 50, left associativity).
Notation "A *' B" := (nmul A B) (at level 49, left associativity).
Check "x" +' 5.

Inductive IExp :=
| aint : int -> IExp
| ivar : string -> IExp
| iplus : IExp -> IExp -> IExp
| imul : IExp -> IExp -> IExp.

Coercion aint : int >-> IExp.
Coercion ivar : string >-> IExp.
Notation "A ++' B" := (iplus A B) (at level 50, left associativity).
Notation "A **' B" := (imul A B) (at level 49, left associativity).
Check (- 5) **' (+ 10).

Inductive SExp :=
| str : string -> SExp
| svar : string -> SExp
| concat : SExp -> SExp -> SExp
| eq_str : SExp -> SExp -> SExp.

Coercion svar : string >-> SExp.
Notation " A '/+/' B" :=(concat A B) (at level 50, left associativity).
Notation " A '=*' B" := (eq_str A B) (at level 60).
Check "ana" /+/ "mere".

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bvar : string -> BExp
| blessthan : BExp -> BExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp.

Coercion bvar : string >-> BExp.
Notation "A <* B" := (blessthan A B) (at level 60).
Notation "!* A" := (bnot A) (at level 70).
Notation "A &* B" := (band A B) (at level 68).
Check btrue &* "a".


(*Tipuri de date pe care le pot contine stiva, coada si array-ul.*)
Inductive Tip :=
| natural : nat -> Tip
| integer : int -> Tip
| boolean : bool -> Tip.

Coercion natural : nat >-> Tip.
Coercion integer : int >-> Tip.
Coercion boolean : bool >-> Tip.

Inductive Queue :=
 | que_var : string -> Queue
 | nulq : Queue
 | addq : Queue -> Tip -> Queue
 | elimq : Queue -> Queue.

Coercion que_var : string >-> Queue.
Notation "A 'q+' B" := (addq A B) (at level 70).
Notation "A 'q-'" := (elimq A) (at level 71).
Check "que" q+ 5.

Inductive Stack :=
 | stack_var : string -> Stack
 | nuls : Stack
 | adds : Stack -> Tip -> Stack
 | elims : Stack -> Stack.

Coercion stack_var : string >-> Stack.
Notation "A 's+' B" := (adds A B) (at level 70).
Notation "A 's-'" := (elims A) (at level 71).
Check "st" s- .

Inductive Array :=
 | arr_var : string -> nat -> Array (*in momentul in care dau un nume trebuie sa stiu si cate pozitii in memorie sa ocup*)
 | assig_new_val : string -> nat -> Tip -> Array.

Notation " A [ N ] = V " := (assig_new_val A N V) (at level 100).
Notation " S 'dim:' N " := (arr_var S N) (at level 100).
Check "v" [ 10 ] = 5 .
Check "v" dim: 10 .

Inductive Enum :=
 | enum_var : string -> Enum
 | adde : Enum -> string -> Enum
 | elim : Enum -> string -> Enum.

Coercion enum_var : string >-> Enum.
Notation "E '+e' S" :=(adde E S) (at level 100).
Notation "E '-e' S" :=(elim E S) (at level 100).

Check "enum" +e "albastru".


Inductive Stmt :=
| skip : Stmt
| param_apel : Tip -> Stmt
| decl_nat : string -> Stmt
| decl_int : string -> Stmt
| decl_str : string -> Stmt
| decl_bool : string -> Stmt
| decl_S : string -> Stack -> Stmt
| decl_Q : string -> Queue -> Stmt
| decl_A : string -> Array -> Stmt
| decl_E : string -> Enum -> Stmt
| decl_func : string -> Stmt -> Stmt -> Stmt
| assignment_a : string -> AExp -> Stmt
| assignment_i : string -> IExp -> Stmt
| assignment_s : string -> SExp -> Stmt
| assignment_b : string -> BExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| apel_func : string -> Stmt -> Stmt
| ret : string -> Stmt. (*sa modifice in env anterior valoarea rezultat*)
Coercion param_apel : Tip >-> Stmt.
(*nume functie, valori, starea programului cand se apeleaza*)
Notation "'unsig' A" := (decl_nat A) (at level 30).
Notation "'integ' A" := (decl_int A) (at level 30).
Notation "'boolean' A" := (decl_bool A) (at level 30).
Notation "'str' A" := (decl_str A) (at level 30).
Notation "'que' A Q" := (decl_Q A Q) (at level 30).
Notation "'stk' A S" := (decl_S A S) (at level 30).
Notation "'arr' A AR" := (decl_A A AR) (at level 30).
Notation "'enum' A E" := (decl_E A E) (at level 30).
Notation "A ':=a:' B" :=(assignment_a A B) (at level 45).
Notation "A ':=i:' B" :=(assignment_i A B) (at level 45).
Notation "A ':=s:' B" :=(assignment_s A B) (at level 45).
Notation "A ':=b:' B" :=(assignment_b A B) (at level 45).
Notation "S1 ;; S2" :=(seq S1 S2) (at level 57).
Notation "'iff' A 'thenn' S 'endd'" := (ifthen A S) (at level 60).
Notation "'functie' S ~ P ~ { ST }" := (decl_func S P ST) (at level 50). 
Notation "'func' S1 'parametri:' E 'end_p'" := (apel_func S1 E) (at level 50). 


Definition pgm :=
unsig "a" ;;
integ "b" ;;
integ "v" ;;
"a" :=a: (5 +' 4) ;;
"b" :=i: ((+ 5) **' (- 5));;
functie "sum" ~ (unsig "x" ;; integ "y") ~ 
{ integ "i" ;; "i" :=i: (- 5) ;; 
integ "suma" ;; "suma" :=i:( "i" ++' "y") ;; ret "suma" } ;;
func "sum" parametri:( 5 ;; (+ 6) ) end_p .

Check pgm.
(*Tipuri de date pentru declarare*)
Inductive Value :=
| undecl : Value
| undef : Value
| nat_val : nat -> Value
| bool_val : bool -> Value
| int_val : int -> Value
| string_val : string -> Value
| code : Stmt -> Value.

Scheme Equality for Value.


Inductive Memory :=
  | mem_default : Memory
  | offset : nat -> Memory. (* offset which indicates the current number of memory zones *)

Scheme Equality for Memory.

(* Environment *)
Definition Env := string -> Memory.
(* Memory Layer *)
Definition MemLayer := Memory -> Value.

(* Stack *)
Definition Stack_mem := list Env.

(* Configuration *)
Inductive Config :=
  (* nat: last memory zone
     Env: environment
     MemLayer: memory layer
     Stack: stack 
  *)
  | config : nat -> Env -> MemLayer -> Stack_mem -> Config.



Inductive Typ : Type := Bool | Nat | Int | String .