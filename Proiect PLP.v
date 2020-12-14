(*Variabile*)
Inductive Var := a | b | c | d | e | i | n | m | sum | x | y | z.
Scheme Equality for Var.

Require Import Strings.String.
Local Open Scope list_scope.

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
Inductive AExp :=
| anum : nat -> AExp
| aint : int -> AExp
| avar : Var -> AExp
| nplus : AExp -> AExp -> AExp
| nmul : AExp -> AExp -> AExp
| iplus : AExp -> AExp -> AExp
| imul : AExp -> AExp -> AExp.
Inductive SExp :=
| str : string -> SExp
| concat : SExp -> SExp -> SExp
| eq_str : SExp -> SExp -> SExp.
Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| blessthan : BExp -> BExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp.
Coercion anum : nat >-> AExp.
Coercion aint : int >-> AExp.
Coercion avar : Var >-> AExp.

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

Inductive Mem :=
  | mem_default : Mem
  | offset : nat -> Mem. (* offset which indicates the current number of memory zones *)

Scheme Equality for Mem.

(* Environment *)
Definition Env := string -> Mem.

(* Memory Layer *)
Definition MemLayer := Mem -> Result.

(* Stack *)
Definition Stack := list Env.

(* Configuration *)
Inductive Config :=
  (* nat: last memory zone
     Env: environment
     MemLayer: memory layer
     Stack: stack 
  *)
  | config : nat -> Env -> MemLayer -> Stack -> Config.

(* Function for updating the environment *)
Definition update_env (env: Env) (x: string) (n: Mem) : Env :=
  fun y =>
      (* If the variable has assigned a default memory zone, 
         then it will be updated with the current memory offset *)
      if (andb (string_beq x y ) (Mem_beq (env y) mem_default))
      then
        n
      else
        (env y).

Definition env : Env := fun x => mem_default.

(* Initially each variable is assigned to a default memory zone *)
Compute (env "z"). (* The variable is not yet declared *)

(* Example of updating the environment, based on a specific memory offset *)
Compute (update_env env "x" (offset 9)) "x".

(* Function for updating the memory layer *)
Definition update_mem (mem : MemLayer) (env : Env) (x : string) (type : Mem) (v : Result) : MemLayer :=
  fun y =>
    (* To be implemented based on the functionalities of your own language
       This implementation should be similar to the "update" function from "Week_7.v" *)

(* Each variable/function name is initially mapped to undeclared *)
Definition mem : MemLayer := fun x => err_undecl.

(* Pay attention!!! In order to be able to monitor the state of the entire program, you need to
   implement a function "update_conf", which updates the 
   entire configuration (environment, memory layout and stack).  
   config : nat -> Env -> MemLayer -> Stack -> Config (the first value represents the last memory zone, 
   and you will need to find a way to increment it each time a new variable/function is declared)
*)

Inductive Stmt :=
| skip : Stmt
| decl : Var -> Stmt
| decl_S : Stack -> Stmt
| decl_Q : Queue -> Stmt
| decl_A : Array -> Stmt
| decl_E : Enum -> Stmt
| assignment_a : Var -> AExp -> Stmt
| assignment_s : Var -> SExp -> Stmt
| assignment_b : Var -> BExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| func : Func -> Stmt.

Notation "A :=: B" :=(assignment A B) (at level 45).
Notation "S1 ;; S2" :=(seq S1 S2) (at level 57).
Notation "'iff' A 'thenn' S 'endd'" := (ifthen A S) (at level 60).
Notation " A - N - " := (show_a A N) (at level 90).
Notation " E ~ S ~ ":= (show_e E S) (at level 90).
Notation " S1 'parametri:' E 'corp:' S2 'Final_f'" := (func S1 E S2) (at level 50). 


Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_nat : ErrorNat -> Result
  | res_bool : ErrorBool -> Result
  | code : Stmt -> Result. (* The functions' names are mapped to the code inside the function *)

Scheme Equality for Result.


Definition check_eq_over_types (t1 : Result)(t2 : Result) : bool :=
  match t1 with
  | err_assign => match t2 with 
                   | err_assign => true
                   | _ => false
                   end
  (* Fill in the implementation for the rest of the cases... *)
  end.



Inductive Typ : Type := Bool | Nat | Int | String .