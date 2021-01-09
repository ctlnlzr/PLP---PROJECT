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

(*Expresii pentru nat, int, string, bool.*)

Inductive Error_Nat :=
| error_nat
| num : nat -> Error_Nat.
Coercion num : nat >-> Error_Nat.
Inductive AExp :=
| anum : Error_Nat -> AExp
| avar : string -> AExp
| nplus : AExp -> AExp -> AExp
| nmul : AExp -> AExp -> AExp
| atop_q : string -> AExp 
| atop_s : string -> AExp
| aelem_arr : string -> nat -> AExp
| astr_enum : string -> AExp.


Coercion avar : string >-> AExp.
Coercion anum : Error_Nat >-> AExp.
Notation "A +' B" := (nplus A B) (at level 50, left associativity).
Notation "A *' B" := (nmul A B) (at level 49, left associativity).
Notation "V '<' N '>a'" := (aelem_arr V N) (at level 48).
Check "x" +' 5.
Check "arr" <6>a. 


Inductive Error_Int :=
| error_int
| iint : int -> Error_Int.
Coercion iint : int >-> Error_Int.
Inductive IExp :=
| aint : Error_Int -> IExp
| ivar : string -> IExp
| iplus : IExp -> IExp -> IExp
| imul : IExp -> IExp -> IExp
| itop_q : string -> IExp 
| itop_s : string -> IExp
| ielem_arr : string -> nat -> IExp.

Coercion aint : Error_Int >-> IExp.
Coercion ivar : string >-> IExp.
Notation "A ++' B" := (iplus A B) (at level 50, left associativity).
Notation "A **' B" := (imul A B) (at level 49, left associativity).
Notation "V '<' N '>i'" := (ielem_arr V N) (at level 48).
Check (- 5) **' (+ 10).


Inductive Error_Str :=
| error_str
| strng : string -> Error_Str.
Coercion strng : string >-> Error_Str.
Scheme Equality for Error_Str.
Inductive SExp :=
| sconst : Error_Str -> SExp
| svar : string -> SExp
| concat : SExp -> SExp -> SExp.


Coercion sconst : Error_Str >-> SExp.
Notation " A '/+/' B" :=(concat A B) (at level 50, left associativity).
Check "ana" /+/ "mere".

Inductive Error_Bol :=
| error_bol
| boll : bool -> Error_Bol.
Coercion boll : bool >-> Error_Bol.
Inductive BExp :=
| berror : BExp
| btrue : BExp
| bfalse : BExp
| bvar : string -> BExp
| blessthan_n : AExp -> AExp -> BExp
| blessthan_i : IExp -> IExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| eq_str : SExp -> SExp -> BExp
| btop_q : string -> BExp
| btop_s : string -> BExp
| belem_arr : string -> nat -> BExp.


Coercion bvar : string >-> BExp.
Notation " A '=*' B" := (eq_str A B) (at level 60).
Notation "A '<a' B" := (blessthan_n A B) (at level 60).
Notation "A '<i' B" := (blessthan_i A B) (at level 60).
Notation "!* A" := (bnot A) (at level 70).
Notation "A &* B" := (band A B) (at level 68).
Notation "V '<' N '>b'" := (belem_arr V N) (at level 48).
Check btrue &* "a".

Inductive Stmt :=
| skip : Stmt
| param_apel : Tip -> Stmt
| decl_nat : string -> Stmt (*un update mem din mem_default direct in nat_val introducand la update o valoare default*)
| decl_int : string -> Stmt
| decl_str : string -> Stmt
| decl_bool : string -> Stmt
| decl_S_a : string -> Stmt 
| decl_S_i : string -> Stmt 
| decl_S_b : string -> Stmt 
| elim_s : string -> Stmt 
| add_s_a :  string -> AExp -> Stmt  (*update doar mem, plus poz_valabil*)
| add_s_i :  string -> IExp -> Stmt (*update doar mem, plus poz_valabil*)
| add_s_b :  string -> BExp -> Stmt(*update doar mem, plus poz_valabil*)
| decl_Q_a : string -> Stmt (*update conf + dim standard*)
| decl_Q_i : string -> Stmt (*update conf + dim standard*)
| decl_Q_b : string -> Stmt (*update conf + dim standard*)
| elim_q :  string -> Stmt (*update doar mem, plus poz_valabil si in loc de val pun undecl*)
| add_q_a :  string -> AExp -> Stmt  (*update doar mem, plus poz_valabil*)
| add_q_i :  string -> IExp -> Stmt (*update doar mem, plus poz_valabil*)
| add_q_b :  string -> BExp -> Stmt (*update doar mem, plus poz_valabil*)
| decl_A_a : string -> nat -> Stmt (*update conf plus dim data*)
| decl_A_i : string -> nat -> Stmt (*update conf plus dim data*)
| decl_A_b : string -> nat -> Stmt (*update conf plus dim data*)
| assig_val_a :  string -> nat -> AExp -> Stmt (*update doar mem*)
| assig_val_i :  string -> nat -> IExp -> Stmt  (*update doar mem*)
| assig_val_b :  string -> nat -> BExp -> Stmt (*update doar mem*)
| decl_E : string -> Stmt (*update conf plus dim data*)
| add_e :  string -> string -> nat -> Stmt (*update doar mem, plus poz_valabil*)
| elim_e : string -> string -> Stmt  (*update doar mem, plus undecl*)
| assig_a : string -> AExp -> Stmt (*update doar mem, plus poz_valabil*)
| assig_i : string -> IExp -> Stmt (*update doar mem*)
| assig_s : string -> SExp -> Stmt
| assig_b : string -> BExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| decl_func : string -> Stmt -> Stmt -> Stmt (*update doar mem, pun la val code, adica param plus cod*)
| apel_func : string -> Stmt -> Stmt (*string -> list string -> Stmt -> Stmt, lista pe care sa o fac eu pt parametri*)
| ret : string -> Stmt. (*sa modifice in env anterior valoarea rezultat*)
Coercion param_apel : Tip >-> Stmt.


Notation "'unsig' A" := (decl_nat A) (at level 30).
Notation "'integ' A" := (decl_int A) (at level 30).
Notation "'boolean' A" := (decl_bool A) (at level 30).
Notation "'str' A" := (decl_str A) (at level 30).
Notation "'queu' Q" := (decl_Q_a Q) (at level 30).
Notation "'quei' Q" := (decl_Q_i Q) (at level 30).
Notation "'queb' Q" := (decl_Q_b Q) (at level 30).
Notation "'stku' S" := (decl_S_a S) (at level 30).
Notation "'stki' S" := (decl_S_i S) (at level 30).
Notation "'stkb' S" := (decl_S_b S) (at level 30).
Notation "AR 'dimu:' N " := (decl_A_a AR N) (at level 30).
Notation "AR 'dimi:' N " := (decl_A_i AR N) (at level 30).
Notation "AR 'dimb:' N " := (decl_A_b AR N) (at level 30).
Notation "'enum' E" := (decl_E E) (at level 30).
Notation "A ':=a:' B" :=(assig_a A B) (at level 45).
Notation "A ':=i:' B" :=(assig_i A B) (at level 45).
Notation "A ':=s:' B" :=(assig_s A B) (at level 45).
Notation "A ':=b:' B" :=(assig_b A B) (at level 45).
Notation "S1 ;; S2" :=(seq S1 S2) (at level 57).
Notation "'iff' A 'thenn' S 'endd'" := (ifthen A S) (at level 60).
Notation "'functie' S ~ P ~ { ST }" := (decl_func S P ST) (at level 50). 
Notation "'func' S1 'parametri:' E 'end_p'" := (apel_func S1 E) (at level 50). 
Notation "A 'qa+' B" := (add_q_a A B) (at level 70).
Notation "A 'qb+' B" := (add_q_b A B) (at level 70).
Notation "A 'qi+' B" := (add_q_i A B) (at level 70).
Notation "A 'q-'" := (elim_q A) (at level 71).
Notation "A 'sa+' B" := (add_s_a A B) (at level 70).
Notation "A 'sb+' B" := (add_s_b A B) (at level 70).
Notation "A 'si+' B" := (add_s_i A B) (at level 70).
Notation "A 's-'" := (elim_s A) (at level 71).
Notation " A '[' N ']a' '=' V " := (assig_val_a A N V) (at level 100).
Notation " A '[' N ']i' '=' V " := (assig_val_i A N V) (at level 100).
Notation " A '[' N ']b' '=' V " := (assig_val_b A N V) (at level 100).
Notation "E '+e' S '=e' N" :=(add_e E S N) (at level 100).
Notation "E '-e' S" :=(elim_e E S) (at level 100).

Check "enum" +e "albastru" =e 1.

Check "v" [ 10 ]a = 5 .

Check "st" s- .
Check "que" qa+ 5.
(*
Definition pgm :=
unsig "a" ;;
integ "b" ;;
integ "v" ;;
"a" :=a: (5 +' 4) ;;
"b" :=i: ((+ 5) **' (- 5));;
functie "sum" ~ (unsig "x" ;; integ "y")
{ integ "i" ;; "i" :=i: (- 5) ;; 
integ "suma" ;; "suma" :=i:( "i" ++' "y") ;; ret "suma" } ;;
func "sum" parametri:( 5 ;; (+ 6) ) end_p .

Check pgm.
*)
Inductive Typ : Type := Bool | Nat | Int | StrinG.

(*Tipuri de date pentru declarare*)
Inductive Value :=
| error_value : Value
| undecl : Value
| undef : Value
| nat_val : Error_Nat -> Value
| bool_val : Error_Bol -> Value
| int_val : Error_Int -> Value
| str_val : Error_Str -> Value
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
  (* nat: last memory zone | Env: environment | MemLayer: memory layer| Stack: stack  *)
  | config : nat -> Env -> MemLayer -> Stack_mem -> Config.


Definition env : Env := fun x => mem_default.
Definition mem : MemLayer := fun y => undecl.
Definition last_off : nat := 0.
Definition St : Stack_mem := nil.
Definition conf : Config := config last_off env mem St.



Fixpoint poz_valabil (q : Memory) (mem : MemLayer) (gas : nat): Memory :=
 match gas with 
 | 0 => q
 | S gas' => match q with 
             | mem_default => mem_default
             | offset a => match (mem (offset a)) with 
                           | undecl => offset (a-1)
                           | nat_val p => (poz_valabil (offset(a + 1)) mem gas')
                           | _ => mem_default
                           end
             end
end.


Fixpoint poz_next (q : Memory) (mem : MemLayer) (gas : nat): Memory :=
 match gas with 
 | 0 => q
 | S gas' => match q with 
             | mem_default => mem_default
             | offset a => match (mem (offset a)) with 
                           | undecl => (offset a)
                           | nat_val p => (poz_next (offset(a + 1)) mem gas')
                           | _ => mem_default
                           end
             end
end.

Reserved Notation "A =[ B , C ]=> N" (at level 70).

Inductive aeval : AExp -> Env -> MemLayer -> Error_Nat -> Prop :=
| a_const : forall n sigma mem, anum n =[ sigma, mem ]=> n
| a_var : forall v sigma mem, avar v =[ sigma, mem ]=> match (mem(sigma v)) with 
                                                       | nat_val q => q
                                                       | _ => error_nat
                                                       end
| a_plus : forall n1 n2 i1 i2 sigma mem n, 
       n1 =[ sigma, mem ]=> i1 ->
       n2 =[ sigma, mem ]=> i2 ->
       match i1, i2 with
       | error_nat, _ => n = error_nat
       | _, error_nat => n = error_nat 
       | num a1, num a2 => n = num (a1 + a2)
       end ->
       n1 +' n2 =[ sigma, mem ]=> n 
| a_mul :  forall n1 n2 i1 i2 sigma mem n, 
       n1 =[ sigma, mem ]=> i1 ->
       n2 =[ sigma, mem ]=> i2 ->
       match i1, i2 with
       | error_nat, _ => n = error_nat
       | _, error_nat => n = error_nat 
       | num a1, num a2 => n = num (a1 * a2)
       end ->
       n1 *' n2 =[ sigma, mem ]=> n 
| a_top_q : forall q sigma mem,
           atop_q  q =[ sigma, mem ]=> match (mem (sigma q)) with 
                                      | nat_val q => q
                                      | _ => error_nat
                                      end
| a_top_s : forall s sigma mem,
           atop_s s =[ sigma, mem ]=> match (mem (poz_valabil (sigma s) mem 20)) with
                                     | nat_val q => q
                                     | _ => error_nat
                                     end
| a_elem_arr : forall ar n sigma mem,
           ar < n >a  =[ sigma, mem ]=> match (sigma ar) with
                                       | mem_default => error_nat
                                       | offset q =>  match (mem (offset(q + n))) with
                                                      | nat_val q => q
                                                      | _ => error_nat
                                                      end
                                       end
| a_str_enum : forall e sigma mem,
          astr_enum e =[ sigma, mem ]=> match (mem (sigma e)) with
                                      | nat_val q => q
                                      | _ => error_nat
                                      end
where "A =[ B , C ]=> N" := (aeval A B C N). 


Reserved Notation "A ={ B , C }=> N" (at level 70).
Inductive ieval : IExp -> Env -> MemLayer -> Error_Int -> Prop :=
| i_int : forall n sigma mem, aint n ={ sigma, mem }=> n
| i_var : forall v sigma mem, ivar v ={ sigma, mem }=> match (mem(sigma v)) with 
                                                       | int_val q => q
                                                       | _ => error_int
                                                       end
| i_plus : forall n1 n2 i1 i2 sigma mem n, 
       n1 ={ sigma, mem }=> i1 ->
       n2 ={ sigma, mem }=> i2 ->
       match i1, i2 with
       | error_int, _ => n = error_int
       | _, error_int => n = error_int 
       | iint a1, iint a2 => match a1, a2 with 
                           | pozitiv e1, pozitiv e2 => n = pozitiv (e1 + e2)
                           | negativ e1, negativ e2 => n = negativ (e1 + e2)
                           | pozitiv e1, negativ e2 => if Nat.ltb e1 e2 then n = negativ (e2 - e1)
                                                                        else n = pozitiv (e1 - e2) 
                           | negativ e1, pozitiv e2 => if Nat.ltb e1 e2 then n = pozitiv (e2 - e1)
                                                                        else n = negativ (e1 - e2) 
                           end
       end ->
       n1 ++' n2 ={ sigma, mem }=> n 
| i_mul : forall n1 n2 i1 i2 sigma mem n, 
       n1 ={ sigma, mem }=> i1 ->
       n2 ={ sigma, mem }=> i2 ->
       match i1, i2 with
       | error_int, _ => n = error_int
       | _, error_int => n = error_int 
       | iint a1, iint a2 => match a1, a2 with 
                           | pozitiv e1, pozitiv e2 => n = pozitiv (e1 * e2)
                           | negativ e1, negativ e2 => n = negativ (e1 * e2)
                           | pozitiv e1, negativ e2 => n = negativ (e1 * e2)
                           | negativ e1, pozitiv e2 => n = negativ (e1 * e2) 
                           end
       end ->
       n1 **' n2 ={ sigma, mem }=> n 
| i_top_q : forall q sigma mem,
           itop_q  q ={ sigma, mem }=> match (mem (sigma q)) with 
                                      | int_val q => q
                                      | _ => error_int
                                      end
| i_top_s : forall s sigma mem,
           itop_s s ={ sigma, mem }=> match (mem (poz_valabil (sigma s) mem 20)) with
                                     | int_val q => q
                                     | _ => error_int
                                     end
| i_elem_arr : forall ar n sigma mem,
           ar < n >i  ={ sigma, mem }=> match (sigma ar) with
                                       | mem_default => error_int
                                       | offset q =>  match (mem (offset(q + n))) with
                                                      | int_val q => q
                                                      | _ => error_int
                                                      end
                                       end
where "A ={ B , C }=> N" := (ieval A B C N).

Reserved Notation "A =< B , C >=> N" (at level 70).
Inductive seval : SExp -> Env -> MemLayer -> Error_Str -> Prop :=
| s_const : forall n sigma mem, sconst n =< sigma, mem >=> n
| s_var : forall v sigma mem, svar v =< sigma, mem >=> match (mem(sigma v)) with 
                                                       | str_val q => q
                                                       | _ => error_str
                                                       end
| s_concat : forall s1 s2 sir1 sir2 sigma mem sir_fin,
          s1 =< sigma, mem >=> sir1 ->
          s2 =< sigma, mem >=> sir2 ->
          match sir1, sir2 with
          | error_str, _ => sir_fin = error_str
          | _, error_str => sir_fin = error_str
          | strng i1, strng i2 => sir_fin = strng (i1 ++ i2)
          end -> 
          s1 /+/ s2 =< sigma, mem >=> sir_fin
where "A =< B , C >=> N" := (seval A B C N).

Reserved Notation "A =| B , C |=> N" (at level 70).
Inductive beval : BExp -> Env -> MemLayer -> Error_Bol -> Prop :=
| b_error : forall sigma mem, berror =| sigma, mem |=> error_bol
| b_true : forall sigma mem,  btrue =| sigma, mem |=> true
| b_false : forall sigma mem, bfalse =| sigma, mem |=> false
| b_var : forall v sigma mem, bvar v =| sigma, mem |=> match (mem(sigma v)) with 
                                                       | bool_val q => q
                                                       | _ => error_bol
                                                       end
| b_lessthan_a : forall a1 a2 i1 i2 sigma mem rez,
       a1 =[ sigma, mem ]=> i1 ->
       a2 =[ sigma, mem ]=> i2 ->
       match i1, i2 with
       | error_nat, _ => rez = error_bol
       | _, error_nat => rez = error_bol
       | num a1, num a2 => rez = (Nat.ltb a1 a2)
       end ->
       a1 <a a2 =| sigma, mem |=> rez
| b_lessthan_i : forall a1 a2 i1 i2 sigma mem rez,
       a1 ={ sigma, mem }=> i1 ->
       a2 ={ sigma, mem }=> i2 ->
       match i1, i2 with
       | error_int, _ => rez = error_bol
       | _, error_int => rez = error_bol
       | iint a1, iint a2 => match a1, a2 with
                           | pozitiv e1, pozitiv e2 => rez = (Nat.ltb e1 e2)
                           | negativ e1, negativ e2 => rez = (Nat.ltb e2 e1)
                           | pozitiv e1, negativ e2 => rez = false
                           | negativ e1, pozitiv e2 => rez = true 
                           end
       end ->
       a1 <i a2 =| sigma, mem |=> rez
| b_not_true : forall b sigma mem, 
          b =| sigma, mem |=> true ->
          bnot b =| sigma, mem |=> false
| b_not_false : forall b sigma mem, 
          b =| sigma, mem |=> false ->
          bnot b =| sigma, mem |=> true
| b_and_false : forall b1 b2 sigma mem,
          b1 =| sigma, mem |=> false ->
          b1 &* b2 =| sigma, mem |=> false
| b_and_true : forall b1 b2 sigma mem rez,
          b1 =| sigma, mem |=> true ->
          b2 =| sigma, mem |=> rez ->
          b1 &* b2 =| sigma, mem|=> rez
| b_eq_str : forall s1 s2 sir1 sir2 sigma mem rez,
          s1 =< sigma, mem >=> sir1 ->
          s2 =< sigma, mem >=> sir2 ->
          match sir1, sir2 with
          | error_str, _ => rez = error_bol
          | _, error_str => rez = error_bol
          | strng i1, strng i2 => rez = (i1 =? i2)
          end ->
          s1 =* s2 =| sigma, mem |=> rez
| b_top_q : forall q sigma mem,
           btop_q  q =| sigma, mem |=> match (mem (sigma q)) with 
                                      | bool_val q => q
                                      | _ => error_bol
                                      end
| b_top_s : forall s sigma mem,
           btop_s s =| sigma, mem |=> match (mem (poz_valabil (sigma s) mem 20)) with
                                     | bool_val q => q
                                     | _ => error_bol
                                     end
| b_elem_arr : forall ar n sigma mem,
           ar < n >b  =| sigma, mem |=> match (sigma ar) with
                                       | mem_default => error_bol
                                       | offset q =>  match (mem (offset(q + n))) with
                                                      | bool_val q => q
                                                      | _ => error_bol
                                                      end
                                       end
where "A =| B , C |=> N" := (beval A B C N).


Definition update_env (env: Env) (x: string) (n: Memory) : Env :=
  fun y =>
      (* If the variable has assigned a default memory zone, 
         then it will be updated with the current memory offset *)
      if (andb (string_beq x y ) (Memory_beq (env y) mem_default))
      then
        n
      else
        (env y).
Definition update_mem (mem : MemLayer) (x : Memory) (v : Value) : MemLayer :=
  fun y =>
    (* To be implemented based on the functionalities of your own language
       This implementation should be similar to the "update" function from "Week_7.v" *)
    if (Memory_beq y x)
    then
       if (Value_beq (mem y) undecl) then v
       else 
         match ( (mem y) ) with
              | nat_val n => if (Value_beq v (nat_val n)) then v else error_value
              | bool_val b => if (Value_beq v (bool_val b)) then v else error_value
              | int_val i => if (Value_beq v (int_val i)) then v else error_value
              | str_val s => if (Value_beq v (str_val s)) then v else error_value
              | code c => if (Value_beq v (code c)) then v else error_value
              | error_val => v
              end
        (* Fill in with your own implementation... 
           Handle here each possible usecase when updating the value of a variable.
        *)
    else undecl.


Fixpoint removelast (l:list Env) : list Env :=
    match l with
      | nil => nil
      | cons a nil => nil
      | a :: l => a :: removelast l
    end.

Definition hd (default:Env) (l:list Env) : Env :=
    match l with
      | nil => default
      | x :: _ => x
    end.

(*Revelatie*)
 
Definition get_mem (c : Config) := match c with
 | config _ _ m _ => m
end.
Definition get_last_of (c : Config) := match c with
 | config l _ _ _ => l
end.
Definition get_env (c : Config) := match c with
 | config _ e _ _ => e
end.
Definition get_stack (c : Config) := match c with
 | config _ _ _ s => s
end.


Definition update_conf (conf : Config) (y : string) (type : Value ) (dim : nat): Config :=

    if ( Memory_beq ((get_env conf) y) mem_default) then (*daca este nedeclarat, il declar cu o valoare default care sa dea si tipul*) 
    config ((get_last_of conf)+dim) (update_env (get_env conf) y (offset((get_last_of conf)))) (update_mem (get_mem conf) (offset((get_last_of conf))) type) (get_stack conf) else conf
.

Definition update_conf_apel (conf : Config) : Config := 
    config (get_last_of conf) env (get_mem conf) ((get_env conf)::(get_stack conf))
.

Definition update_conf_ret (conf : Config) : Config :=
    config (get_last_of conf) (hd env (get_stack conf)) (get_mem conf) (removelast (get_stack conf))
.


Fixpoint update_elim_q (conf : Config) (y : Memory) (gas : nat): Config :=
 match gas with 
 | 0 => conf
 | S gas' => match y with 
             | mem_default => conf
             | offset a => match (mem (offset a)) with 
                           | _ => (update_elim_q (config (get_last_of conf) (get_env conf) (update_mem (get_mem conf) (offset a) ((get_mem conf) (offset (a+1)))) (get_stack conf)) (offset(a+1)) gas')
                           end
             end
end. 

Definition update_assig (conf : Config) (y : Memory) (p : nat) (n: Value): Config :=
match y with
| mem_default => conf
| offset a => (config (get_last_of conf) (get_env conf) (update_mem (get_mem conf) (offset(a+p)) n) (get_stack conf)) 
end.

Fixpoint update_elim_e (conf : Config) (y: Memory) (s1 : string) (gas : nat): Config :=
 match gas with 
 | 0 => conf
 | S gas' =>  match ((get_mem conf) y) with
             | str_val s => if (Error_Str_beq s (strng s1)) then (config (get_last_of conf) (get_env conf) (update_mem (get_mem conf) ((get_env conf) s1) undecl) (get_stack conf))
                                      else match y with 
                                           | mem_default => conf
                                           | offset a => (update_elim_e conf (offset (a+1)) s1 gas')
                                           end
  | _=>conf
  end
end.


Reserved Notation "A -{ C }> CON" (at level 70).
Inductive eval : Stmt -> Config -> Config -> Prop :=
| e_decl_nat : forall confi s, unsig s -{ confi }> (update_conf confi s (nat_val 0) 1)
| e_decl_int : forall confi s, integ s -{ confi }> (update_conf confi s (int_val (pozitiv 0)) 1)
| e_decl_str : forall confi s, str s -{ confi }> (update_conf confi s (str_val "a") 1)
| e_decl_bool : forall confi s, boolean s -{ confi }> (update_conf confi s (bool_val true) 1)
| e_decl_S_a : forall confi s, stku s -{ confi }> (update_conf confi s (nat_val 0) 20)
| e_decl_S_i : forall confi s, stki s -{ confi }> (update_conf confi s (int_val (pozitiv 0)) 20 )
| e_decl_S_b : forall confi s, stkb s -{ confi }> (update_conf confi s (bool_val true) 20 )
| e_elim_s : forall confi s, (s s- ) -{ confi }> 
(config (get_last_of confi) (get_env confi) (update_mem (get_mem confi) (poz_valabil ((get_env confi) s) (get_mem confi) 20 ) undecl) (get_stack confi)) 
| e_add_s_a : forall confi s a n, 
         a =[ (get_env confi) , (get_mem confi) ]=> n -> s sa+ a -{ confi }>
         (config (get_last_of confi) (get_env confi) (update_mem (get_mem confi) (poz_next ((get_env confi) s) (get_mem confi) 20) (nat_val n)) (get_stack confi)) 
| e_add_s_i : forall confi s a n, 
         a ={ (get_env confi) , (get_mem confi)}=> n -> s si+ a -{ confi }>
         (config (get_last_of confi) (get_env confi) (update_mem (get_mem confi) (poz_next ((get_env confi) s) (get_mem confi) 20) (int_val n)) (get_stack confi))
| e_add_s_b : forall confi s a n, 
         a =| (get_env confi) , (get_mem confi)|=> n -> s sb+ a -{ confi }>
         (config (get_last_of confi) (get_env confi) (update_mem (get_mem confi) (poz_next ((get_env confi) s) (get_mem confi) 20) (bool_val n)) (get_stack confi))
| e_decl_Q_a : forall confi s, queu s -{ confi }> (update_conf confi s (nat_val 0) 20)
| e_decl_Q_i : forall confi s, quei s -{ confi }> (update_conf confi s (int_val (pozitiv 0)) 20)
| e_decl_Q_b : forall confi s, queb s -{ confi }> (update_conf confi s (bool_val true) 20)
| e_elim_q : forall confi s, (s q-) -{ confi }> (update_elim_q confi ((get_env confi) s) 19)
| e_add_q_a : forall confi s a n, 
         a =[ (get_env confi) , (get_mem confi) ]=> n -> s qa+ a -{ confi }>
         (config (get_last_of confi) (get_env confi) (update_mem (get_mem confi) (poz_next ((get_env confi) s) (get_mem confi) 20) (nat_val n)) (get_stack confi))
| e_add_q_i : forall confi s a n, 
         a ={ (get_env confi) , (get_mem confi)}=> n -> s qi+ a -{ confi }>
         (config (get_last_of confi) (get_env confi) (update_mem (get_mem confi) (poz_next ((get_env confi) s) (get_mem confi) 20) (int_val n)) (get_stack confi))
| e_add_q_b : forall confi s a n, 
         a =| (get_env confi) , (get_mem confi)|=> n -> s qb+ a -{ confi }>
         (config (get_last_of confi) (get_env confi) (update_mem (get_mem confi) (poz_next ((get_env confi) s) (get_mem confi) 20) (bool_val n)) (get_stack confi))
| e_decl_A_a : forall confi s d, s dimu: d -{ confi }> (update_conf confi s (nat_val 0) d)
| e_decl_A_i : forall confi s d, s dimi: d -{ confi }> (update_conf confi s (int_val (pozitiv 0)) d)
| e_decl_A_b : forall confi s d, s dimb: d -{ confi }> (update_conf confi s (bool_val true) d)
| e_assig_val_a : forall confi s p v n,
             v =[ (get_env confi) , (get_mem confi) ]=> n -> (s [ p ]a = v) -{ confi }>
             (update_assig confi ((get_env confi) s) p (nat_val n)) 
| e_assig_val_i : forall confi s p v n,
             v ={ (get_env confi) , (get_mem confi) }=> n -> (s [ p ]i = v) -{ confi }>
             (update_assig confi ((get_env confi) s) p (int_val n)) 
| e_assig_val_b : forall confi s p v n,
             v =| (get_env confi) , (get_mem confi) |=> n -> (s [ p ]b = v) -{ confi }>
             (update_assig confi ((get_env confi) s) p (bool_val n))
| e_assig_a : forall confi s v n,
             v =[ (get_env confi) , (get_mem confi) ]=> n -> s :=a: v -{ confi }>
             (config (get_last_of confi) (get_env confi) (update_mem (get_mem confi) ((get_env confi) s) (nat_val n)) (get_stack confi))
| e_assig_i : forall confi s v n,
             v ={ (get_env confi) , (get_mem confi) }=> n -> s :=i: v -{ confi }>
             (config (get_last_of confi) (get_env confi) (update_mem (get_mem confi) ((get_env confi) s) (int_val n)) (get_stack confi))
| e_assig_b : forall confi s v n,
             v =| (get_env confi) , (get_mem confi) |=> n -> s :=b: v -{ confi }>
             (config (get_last_of confi) (get_env confi) (update_mem (get_mem confi) ((get_env confi) s) (bool_val n)) (get_stack confi))
| e_assig_s : forall confi s v n,
             v =< (get_env confi) , (get_mem confi) >=> n -> s :=s: v -{ confi }>
             (config (get_last_of confi) (get_env confi) (update_mem (get_mem confi) ((get_env confi) s) (str_val n)) (get_stack confi))
| e_decl_E : forall confi s,
             enum s -{ confi }> (update_conf confi s (str_val "a") 20 )
| e_add_e : forall confi s s1 v,
              (s +e s1 =e v )-{ confi }> (*adaug in locurile pt enum sirul ca valoare si in memorie ca variabila noua la care o sa salvez valoarea*)
       (config ((get_last_of confi)+1) (update_env (get_env confi) s1 (offset (get_last_of confi))) (update_mem (update_mem (get_mem confi) (poz_next ((get_env confi) s) (get_mem confi) 20) (str_val s1)) (update_env (get_env confi) s1 (offset (get_last_of confi)) s1) (nat_val v)) (get_stack confi))
| e_elim_e : forall confi s s1,
             (s -e s1) -{ confi }> (update_elim_e conf ((get_env confi) s) s1 20)
| e_seq : forall s1 s2 conf conf1 conf2,
      s1 -{ conf }> conf1 ->
      s2 -{ conf1 }> conf2 ->
      (s1 ;; s2) -{ conf }> conf2
| e_while_false : forall b s conf,
     b =|(get_env conf) , (get_mem conf)|=> false ->
     (while b s) -{ conf }> conf
| e_while_true : forall b s conf conf1,
     b =|(get_env conf) , (get_mem conf)|=> true ->
     (seq s (while b s)) -{ conf }> conf1 ->
     (while b s) -{ conf }> conf1
| e_if_true : forall b s conf conf',
        b =|(get_env conf) , (get_mem conf)|=> true ->
        s -{ conf }> conf' ->
        (iff b thenn s endd) -{ conf }> conf'
| e_if_false : forall b s conf,
      b =|(get_env conf) , (get_mem conf)|=> false ->
      (iff b thenn s endd) -{ conf }> conf 
where "A -{ C }> CON" := (eval A C CON).
