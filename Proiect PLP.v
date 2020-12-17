
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
 | arr_num : string -> Array
 | arr_dim : string -> nat -> Array
 | assig_new_val : Array -> nat -> Tip -> Array.

Coercion arr_num : string >-> Array.
Notation " A [ N ] = V " := (assig_new_val A N V) (at level 100).
Notation " S 'dim:' N " := (arr_dim S N) (at level 100).
Check "v" [ 10 ] = 5 .


Inductive Enum :=
 | enum_var : string -> Enum
 | adde : Enum -> string -> Enum
 | elim : Enum -> string -> Enum.

Coercion enum_var : string >-> Enum.
Notation "E '+e' S" :=(adde E S) (at level 100).
Notation "E '-e' S" :=(elim E S) (at level 100).

Check "enum" +e "albastru".

(*Expresii pentru nat, int, string, bool.*)
Inductive AExp :=
| anum : nat -> AExp
| avar : string -> AExp
| nplus : AExp -> AExp -> AExp
| nmul : AExp -> AExp -> AExp
| atop_q : Queue -> AExp 
| atop_s : Stack -> AExp
| aelem_arr : Array -> nat -> AExp
| astr_enum : Enum -> string -> AExp.

Coercion avar : string >-> AExp.
Coercion anum : nat >-> AExp.
Notation "A +' B" := (nplus A B) (at level 50, left associativity).
Notation "A *' B" := (nmul A B) (at level 49, left associativity).
Notation "V '<' N '>a'" := (aelem_arr V N) (at level 48).
Check "x" +' 5.
Check "arr" <6>a. 

Inductive IExp :=
| aint : int -> IExp
| ivar : string -> IExp
| iplus : IExp -> IExp -> IExp
| imul : IExp -> IExp -> IExp
| itop_q : Queue -> IExp 
| itop_s : Stack -> IExp
| ielem_arr : Array -> nat -> IExp.

Coercion aint : int >-> IExp.
Coercion ivar : string >-> IExp.
Notation "A ++' B" := (iplus A B) (at level 50, left associativity).
Notation "A **' B" := (imul A B) (at level 49, left associativity).
Notation "V '<' N '>i'" := (ielem_arr V N) (at level 48).
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
| band : BExp -> BExp -> BExp
| btop_q : Queue -> BExp
| btop_s : Stack -> BExp
| belem_arr : Array -> nat -> BExp.

Coercion bvar : string >-> BExp.
Notation "A <* B" := (blessthan A B) (at level 60).
Notation "!* A" := (bnot A) (at level 70).
Notation "A &* B" := (band A B) (at level 68).
Notation "V '<' N '>b'" := (belem_arr V N) (at level 48).
Check btrue &* "a".


Inductive Stmt :=
| skip : Stmt
| param_apel : Tip -> Stmt
| decl_nat : string -> Stmt
| decl_int : string -> Stmt
| decl_str : string -> Stmt
| decl_bool : string -> Stmt
| decl_S : Stack -> Stmt
| decl_Q : Queue -> Stmt
| decl_A : Array-> Stmt
| decl_E : Enum -> Stmt
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


Notation "'unsig' A" := (decl_nat A) (at level 30).
Notation "'integ' A" := (decl_int A) (at level 30).
Notation "'boolean' A" := (decl_bool A) (at level 30).
Notation "'str' A" := (decl_str A) (at level 30).
Notation "'que' Q" := (decl_Q Q) (at level 30).
Notation "'stk' S" := (decl_S S) (at level 30).
Notation "'arr' AR" := (decl_A AR) (at level 30).
Notation "'enum' E" := (decl_E E) (at level 30).
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

Inductive Typ : Type := Bool | Nat | Int | StrinG.

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

Definition Env := string -> Memory.
Definition MemLayer := Memory -> Value.
Definition Stack_mem := list Env.

Inductive Config :=
  (* nat: last memory zone
     Env: environment
     MemLayer: memory layer
     Stack: stack 
  *)
  | config : nat -> Env -> MemLayer -> Stack_mem -> Config.

