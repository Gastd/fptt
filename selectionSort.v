Require Import Arith List.
Require Import Recdef.
Require Import Datatypes.

Fixpoint select_min (x: nat) (l: list nat) : nat * list nat :=
  match l with
  | nil => (x,l)
  | h :: tl => if (le_lt_dec x h) then
                 let (m,l') := select_min x tl in
                  (m, h::l')
               else 
                 let (m,l') := select_min h tl in
                  (m, x::l')
  end.

Compute (select_min 2 (1::nil)).
Compute (select_min 2 (1::2::3::0::1::nil)).

Lemma pair_fst: forall (x: nat) (y: nat) (l: list nat) (l': list nat), (x, l) = (y, l') -> x = y.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Lemma select_min_length: forall l l' x y, select_min x l = (y, l') -> length l = length l'.
Proof.
  (* intros l l' x y H. *)
  induction l.
  - intros l' x y H.
    simpl in H.
    inversion H.
    reflexivity.
  - intros l' x y H.
    generalize dependent l'.
    intros l'. case l'.
    + intro H.
      simpl in H.
      destruct (le_lt_dec x a).
      * destruct (select_min x l).
        inversion H.
      * destruct (select_min a l).
        inversion H.
    + intros n l'' H.
      simpl.
      apply f_equal.
      apply IHl with x y.
      simpl in H.
      destruct (le_lt_dec x a).
      * destruct (select_min x l).
        inversion H; subst.
        reflexivity.
      * destruct (select_min a l).
        inversion H; subst.
        
Admitted.

Function select (l: list nat) {measure length} : list nat :=
  match l with
  | nil => l
  | h :: tl =>
    let (m,l') := select_min h tl in
      (m :: (select l'))
  end.
Proof.
  intros.
  apply select_min_length in teq0.
  rewrite <- teq0.
  simpl.
  apply lt_n_Sn.
Qed.

Inductive ordenada : list nat -> Prop :=
  | lista_vazia : ordenada nil
  | lista_1: forall n : nat, ordenada (cons n nil)
  | lista_nv : forall (x y : nat) (l : list nat), ordenada (cons y l) -> x <= y -> ordenada (cons x (cons y l)).

Fixpoint num_oc n l := 
  match l with
    | nil => 0
    | cons h tl => 
      match eq_nat_dec n h with
        | left _ => S(num_oc n tl) 
        | right _ => num_oc n tl 
      end
  end.

Theorem selectionSort_correct: forall l, ordenada (selectionSort l) /\ (equiv l (selectionSort l)).
Proof.
Admitted.