
Require Export Imp.

(* First we define syntax of the language *)

(* We could reuse aexp and bexp defined for Imp. *)

(* Redefine commands here. To distinguish them 
   from Imp commands, we call them scom *)
(* You need to change it into an inductive definition *)
Inductive scom : Type :=
  | CSkip : scom
  | CAss : id -> aexp -> scom
  | CSeq : scom -> scom -> scom
  | CIf : bexp -> scom -> scom -> scom
  | CWhile : bexp -> scom -> scom
  | CMut : aexp -> aexp ->scom
  | CLook : id -> aexp -> scom
  | CCons : id -> aexp -> aexp -> scom
  | CDisp : aexp -> scom.

(* Program states, which is called sstate *)
Definition store := id -> nat.

(* if heap maps a natural number (address) to
   None, we say the address is not a valid address,
   or it is not in the domain of the heap *)
Definition heap := nat -> option nat.

(* Define an empty heap, which contains no memory cells *)
Definition emp_heap : heap := fun _ => None.

Definition in_dom (l: nat) (h: heap) : Prop :=
  exists n, h l = Some n.

Definition not_in_dom (l: nat) (h: heap) : Prop :=
  h l = None.

Theorem in_not_in_dec : 
  forall l h, {in_dom l h} + {not_in_dom l h}.
  unfold in_dom, not_in_dom.
  intros; destruct (h l).
  left. exists n. reflexivity.
  right. reflexivity.
Qed.

(* h1 and h2 have disjoint domain *)
Definition disjoint (h1 h2: heap) : Prop :=
  forall l, ~(in_dom l h1 /\ in_dom l h2).

(* union of two heaps *)
Definition h_union (h1 h2: heap) : heap :=
  fun l => 
    if (in_not_in_dec l h1) then h1 l else h2 l.

(* h1 is a subset of h2 *)
Definition h_subset (h1 h2: heap) : Prop :=
  forall l n, h1 l = Some n -> h2 l = Some n.

Definition h_eq (h1 h2: heap) : Prop :=
  forall l, h1 l = h2 l.

(* store update *)
Definition st_update (s: store) (x: id) (n: nat) : store :=
  fun x' => if eq_id_dec x x' then n else s x'.

(* heap update *)
Definition h_update (h: heap) (l: nat) (n: nat) : heap :=
  fun l' => if eq_nat_dec l l' then Some n else h l'.

Definition sstate := (store * heap) %type.

Definition ss (st:sstate) := @fst _ _ st.
Definition sh (st:sstate) := @snd _ _ st.
(* since program may abort, we extend our state
   definition to add a special state Abt *)
Inductive ext_state : Type :=
  St:  sstate -> ext_state    (* normal state *)
| Abt: ext_state.             (* abort *)


(* Next we define the operational semantics *)

(* big-step semantics. You should change it into 
   an inductive definition *)
Inductive big_step: 
   scom * sstate -> ext_state -> Prop :=
| E_Skip : forall st, big_step (CSkip, st) (St st)
| E_Ass  : forall st x e s h n,
             s = ss st ->
             h = sh st ->
             n = aeval s e ->
             big_step (CAss x e, st)
                      (St (st_update s x n, h))
| E_Seq  : forall st st' st'' c1 c2,
             big_step (c1, st) (St st'') ->
             big_step (c2, st'') (St st') ->
             big_step (CSeq c1 c2, st) (St st')
| E_IfTrue : forall st st' b c1 c2 s,
               s = ss st ->
               beval s b = true ->
               big_step (c1, st) (St st') ->
               big_step (CIf b c1 c2, st) (St st')
| E_IfFalse : forall st st' b c1 c2 s,
                s = ss st ->
                beval s b = false ->
                big_step (c2, st) (St st') ->
                big_step (CIf b c1 c2, st) (St st')
| E_WhileEnd : forall st b c s,
                 s = ss st ->
                 beval s b = false ->
                 big_step (CWhile b c, st) (St st)
| E_WhileLoop : forall st st'' st' b c s,
                  s = ss st ->
                  beval s b = true ->
                  big_step (c, st) (St st'') ->
                  big_step (CWhile b c, st'') (St st') ->
                  big_step (CWhile b c, st) (St st')
| E_MutOk : forall st e1 e2 s h l n,
              s = ss st ->
              h = sh st ->
              l = (aeval s e1) ->
              n = (aeval s e2) ->
              in_dom l h ->
              big_step (CMut e1 e2, st)
                       (St (s, (h_update h l n)))
| E_MutAbt : forall st e1 e2 s h l n,
               s = ss st ->
               h = sh st ->
               l = (aeval s e1) ->
               n = (aeval s e2) ->
               not_in_dom l h ->
               big_step (CMut e1 e2, st) Abt
| E_LookOk : forall st x e s h l n,
               s = ss st ->
               h = sh st ->
               l = (aeval s e) ->
               in_dom l h ->
               h l = Some n ->
               big_step (CLook x e, st)
                        (St (st_update s x n, h))
| E_LookAbt : forall st x e s h l,
                s = ss st ->
                h = sh st ->
                l = (aeval s e) ->
                not_in_dom l h ->
                big_step (CLook x e, st) Abt
| E_Cons : forall st x e1 e2 s h l n1 n2,
             s = ss st ->
             h = sh st ->
             not_in_dom l h ->
             not_in_dom (l+1) h ->
             n1 = (aeval s e1) ->
             n2 = (aeval s e2) ->
             big_step (CCons x e1 e2, st)
                      (St (s,
                           h_update (h_update h l n1) (l+1) n2))
| E_DispOk : forall st e s h l,
               s = ss st ->
               h = sh st ->
               l = (aeval s e) ->
               in_dom l h ->
               big_step (CDisp e, st)
                        (St (s,
                             fun l' =>
                               if eq_nat_dec l l' then None else h l'))
| E_DispAbt : forall st e s h l,
                s = ss st ->
                h = sh st ->
                l = (aeval s e) ->
                not_in_dom l h ->
                big_step (CDisp e, st) Abt.

(* small-step semantics. Should be inductive too *)
Inductive small_step: 
   scom * ext_state -> scom * ext_state -> Prop :=
| ES_Abt : forall c, small_step (c, Abt) (CSkip, Abt)
| ES_Skip : forall st, small_step (CSkip, St st) (CSkip, St st)
| ES_Ass  : forall st x e s h n,
              s = ss st ->
              h = sh st ->
              n = aeval s e ->
              small_step (CAss x e, St st)
                         (CSkip, St (st_update s x n, h))
| ES_SeqS  : forall st c2,
               small_step (CSeq CSkip c2, St st) (c2, St st)
| ES_Seq   : forall st st' c1 c1' c2,
               small_step (c1, St st) (c1', St st') ->
               small_step (CSeq c1 c2, St st) (CSeq c1' c2, St st')
| ES_IfTrue : forall st b c1 c2 s,
               s = ss st ->
               beval s b = true ->
               small_step (CIf b c1 c2, St st) (c1, St st)
| ES_IfFalse : forall st b c1 c2 s,
                s = ss st ->
                beval s b = false ->
                small_step (CIf b c1 c2, St st) (c2, St st)
| ES_WhileEnd : forall st b c s,
                 s = ss st ->
                 beval s b = false ->
                 small_step (CWhile b c, St st) (CSkip, St st)
| ES_WhileLoop : forall st b c s,
                  s = ss st ->
                  beval s b = true ->
                  small_step (CWhile b c, St st) (CSeq c (CWhile b c), St st)
| ES_MutOk : forall st e1 e2 s h l n,
              s = ss st ->
              h = sh st ->
              l = (aeval s e1) ->
              n = (aeval s e2) ->
              in_dom l h ->
              small_step (CMut e1 e2, St st)
                         (CSkip, St (s, (h_update h l n)))
| ES_MutAbt : forall st e1 e2 s h l n,
               s = ss st ->
               h = sh st ->
               l = (aeval s e1) ->
               n = (aeval s e2) ->
               not_in_dom l h ->
               small_step (CMut e1 e2, St st) (CMut e1 e2, Abt)
| ES_LookOk : forall st x e s h l n,
               s = ss st ->
               h = sh st ->
               l = (aeval s e) ->
               in_dom l h ->
               h l = Some n ->
               small_step (CLook x e, St st)
                          (CSkip, St (st_update s x n, h))
| ES_LookAbt : forall st x e s h l,
                s = ss st ->
                h = sh st ->
                l = (aeval s e) ->
                not_in_dom l h ->
                small_step (CLook x e, St st) (CLook x e, Abt)
| ES_Cons : forall st x e1 e2 s h l n1 n2,
             s = ss st ->
             h = sh st ->
             not_in_dom l h ->
             not_in_dom (l+1) h ->
             n1 = (aeval s e1) ->
             n2 = (aeval s e2) ->
             small_step (CCons x e1 e2, St st)
                        (CSkip, St (s,
                                    h_update (h_update h l n1) (l+1) n2))
| ES_DispOk : forall st e s h l,
               s = ss st ->
               h = sh st ->
               l = (aeval s e) ->
               in_dom l h ->
               small_step (CDisp e, St st)
                          (CSkip, St (s,
                                      fun l' =>
                                        if eq_nat_dec l l' then None else h l'))
| ES_DispAbt : forall st e s h l,
                s = ss st ->
                h = sh st ->
                l = (aeval s e) ->
                not_in_dom l h ->
                small_step (CDisp e, St st) (CDisp e, Abt).

(** Assertions **)
Definition sass := sstate -> Prop.

(* define semantics of assertion emp *)
Definition emp : sass :=
  fun st => match st with (s, h) => h_eq h emp_heap end.

Definition sig_heap (l: nat) (n: nat) : heap :=
  fun l' => if eq_nat_dec l l' then Some n else None.

(* assertion l |-> n *)
Definition pto (l: nat) (n: nat) : sass :=
  fun st => match st with (s, h) => h_eq h (sig_heap l n) end.
Notation "l '|->' n" := (pto l n) (at level 60).

(* p * q *)
Definition star (p q : sass) : sass :=
  fun st =>
    match st with (s, h) =>
                  exists h1, exists h2,
                               disjoint h1 h2 /\
                               h_eq h (h_union h1 h2) /\
                               p (s, h1) /\ q (s, h2)
    end.
Notation "p '**' q" := (star p q) (at level 70).

(* p --* q *)
Definition simp (p q: sass) : sass :=
  fun st =>
    match st with (s, h) =>
                  forall h',
                    disjoint h h' ->
                    p (s, h') ->
                    q (s, h_union h h')
    end.
Notation "p '--*' q" := (simp p q) (at level 80).


Definition pure (p: sass) : Prop :=
  forall s h h', p (s, h) <-> p (s, h').

Definition precise (p: sass) : Prop :=
  forall s h h' h'', h_subset h' h ->
                     h_subset h'' h ->
                     p (s, h') -> p (s, h'') ->
                     h_eq h' h''.

Definition intuitionistic (p: sass) : Prop :=
  forall s h h', h_subset h h' -> p (s, h) -> p (s, h').