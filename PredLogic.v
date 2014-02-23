Require Export SfLib.
Require Import ListSet.
(* see http://coq.inria.fr/distrib/V8.4/stdlib/Coq.Lists.ListSet.html 
   for the ListSet library *)
Require Import Imp.

(* acon true , acon false *)
Inductive assert: Type :=
  | PTrue: assert  (* true *)
  | PFalse: assert (* false *)
  | PEq: aexp -> aexp -> assert  (* e1 = e2 *)
  | PLt: aexp -> aexp -> assert  (* e1 < e2 *)
  | PImp: assert -> assert -> assert (* a1 ==> a2 *)
  | PAnd: assert -> assert -> assert (* a1 /\ a2 *)
  | PNot: assert -> assert (* not a *)
  | POr : assert -> assert -> assert (* a1 \/ a2 *)
  | PForall: id -> assert -> assert (* forall x. a *)
  | PExist: id -> assert -> assert  (* exists x. a *).



Fixpoint peval (p: assert) (st: state) : Prop :=
  match p with
  | PTrue => True
  | PFalse => False
  | PEq a1 a2 => (aeval st a1) = (aeval st a2)
  | PLt a1 a2 => (aeval st a1) < (aeval st a2)
  | PImp p1 p2 => (peval p1 st) -> (peval p2 st)
  | PAnd p1 p2 => 
       (peval p1 st) /\ (peval p2 st)
  | POr p1 p2 => (peval p1 st) \/ (peval p2 st)
  | PNot p' => ~ (peval p' st)
  | PForall x p' => forall n: nat, peval p' (update st x n)
  | PExist x p' => exists n: nat, peval p' (update st x n) 
  end.


Definition valid (p: assert): Prop := 
  forall st : state, peval p st.

Definition strongerThan (p q: assert) : Prop := 
  forall st, peval p st -> peval q st.



(* definition of judgment |- a *)
Inductive judge : assert -> Prop := 
  | xPlusZero : forall x: id, 
                  judge (PEq (APlus (AId x) (ANum 0)) (AId x))
  | SymmObjEq : forall a1 a2 : aexp,
                  judge (PImp (PEq a1 a2) (PEq a2 a1))
  | ModusPonens: forall p q: assert, 
                  judge p -> judge (PImp p q) -> judge q
  | Generalization: forall (x: id) (p: assert),
                      judge p -> judge (PForall x p).

Check judge.


(* prove the judgment |- forall x, x = x+0 *)
Lemma test: judge (PForall X (PEq (AId X) (APlus (AId X) (ANum 0)))).
Proof.
  Admitted.

(* exercise: prove the soundness of the simple logic theory *)
Lemma soundJudge: forall p, judge p -> valid p.
Proof.
  Admitted.

(* set of variables *)
Definition idSet := set id.

Definition emp_is : idSet := nil.

(* eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}. *)

Definition is_add (i: id) (is: idSet) := set_add eq_id_dec i is.

Definition is_remove (i: id) (is: idSet) := set_remove eq_id_dec i is.

Definition is_union (is1 is2: idSet) := set_union eq_id_dec is1 is2.

Definition is_In (i: id) (is: idSet) : Prop := set_In i is.

Fixpoint fv_aexp (a : aexp) : idSet := 
  match a with
  | ANum _ => emp_is
  | AId x => [x]
  | APlus a1 a2 => is_union (fv_aexp a1) (fv_aexp a2)
  | AMinus a1 a2 => is_union (fv_aexp a1) (fv_aexp a2)
  | AMult a1 a2 => is_union (fv_aexp a1) (fv_aexp a2)
  end.
  

Fixpoint fv_ast (p: assert) : idSet := 
  match p with
  | PTrue => emp_is
  | PFalse => emp_is
  | PEq a1 a2 => is_union (fv_aexp a1) (fv_aexp a2)
  | PLt a1 a2 => is_union (fv_aexp a1) (fv_aexp a2)
  | PImp p1 p2 => is_union (fv_ast p1) (fv_ast p2) 
  | PAnd p1 p2 => is_union (fv_ast p1) (fv_ast p2)
  | POr p1 p2 => is_union (fv_ast p1) (fv_ast p2)
  | PNot p' => fv_ast p'
  | PForall x p' => is_remove x (fv_ast p')
  | PExist x p' => is_remove x (fv_ast p')
  end.

(* exercise: prove the coincidence theorem shown in class *)
Lemma coincidence_exp: forall (st st': state) (a: aexp),
  (forall i: id, is_In i (fv_aexp a) -> st i = st' i)
  -> aeval st a = aeval st' a.
Proof.
  Admitted.

Theorem coincidence: forall (st st': state) (p: assert),
  (forall i: id, is_In i (fv_ast p) -> st i = st' i)
  -> (peval p st <-> peval p st').
Proof.
  Admitted.

Definition subst : Type := list (id * aexp).

Fixpoint lookup_subst (i: id) (delta: subst) : option aexp :=
  match delta with
  | nil => None
  | (i', a') :: d => if eq_id_dec i i' then Some a' else lookup_subst i d
  end.

(* this is a five star exercise (very difficult):
   define substitution, then formulate and prove 
   the substitution theorem shown in class. 
   *** Try to work on it early. Don't wait till 
       the last minute ***
*)
