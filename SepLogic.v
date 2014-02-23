
Require Export Imp.

(* First we define syntax of the language *)

(* We could reuse aexp and bexp defined for Imp. *)

(* Redefine commands here. To distinguish them 
   from Imp commands, we call them scom *)
(* You need to change it into an inductive definition *)
Definition scom : Type := admit.


(* Program states, which is called sstate *)
Definition store := id -> nat.

(* if heap maps a natural number (address) to
   None, we say the address is not a valid address,
   or it is not in the domain of the heap *)
Definition heap := nat -> option nat.

(* Define an empty heap, which contains no memory cells *)
Definition emp_heap : heap := admit.

Definition in_dom (l: nat) (h: heap) : Prop :=
  exists n, h l = Some n.

Definition not_in_dom (l: nat) (h: heap) : Prop :=
  h l = None.

Theorem in_not_in_dec : 
  forall l h, {in_dom l h} + {not_in_dom l h}.
Admitted.

(* h1 and h2 have disjoint domain *)
Definition disjoint (h1 h2: heap) : Prop := admit.

(* union of two heaps *)
Definition h_union (h1 h2: heap) : heap :=
  fun l => 
    if (in_not_in_dec l h1) then h1 l else h2 l.

(* h1 is a subset of h2 *)
Definition h_subset (h1 h2: heap) : Prop := admit.

(* store update *)
Definition st_update (s: store) (x: id) (n: nat) : store :=
  fun x' => if eq_id_dec x x' then n else s x'.

(* heap update *)
Definition h_update (h: heap) (l: nat) (n: nat) : heap :=
  fun l' => if eq_nat_dec l l' then Some n else h l'.

Definition sstate := (store * heap) %type.

(* since program may abort, we extend our state
   definition to add a special state Abt *)
Inductive ext_state : Type :=
  St:  sstate -> ext_state    (* normal state *)
| Abt: ext_state.             (* abort *)


(* Next we define the operational semantics *)

(* big-step semantics. You should change it into 
   an inductive definition *)
Definition big_step: 
   scom * sstate -> ext_state -> Prop := admit.

(* small-step semantics. Should be inductive too *)
Definition small_step: 
   scom * ext_state -> scom * ext_state -> Prop 
  := admit.


(** Assertions **)
Definition sass := sstate -> Prop.

(* define semantics of assertion emp *)
Definition emp : sass := admit.

(* assertion l |-> n *)
Definition pto (l: nat) (n: nat) : sass := admit.
Notation "l '|->' n" := (pto l n) (at level 60).

(* p * q *)
Definition star (p q : sass) : sass := admit.
Notation "p '**' q" := (star p q) (at level 70).

(* p --* q *)
Definition simp (p q: sass) : sass := admit.
Notation "p '--*' q" := (simp p q) (at level 80).


Definition pure (p: sass) : Prop := admit.

Definition precise (p: sass) : Prop := admit.

Definition intuitionistic (p: sass) : Prop := admit.