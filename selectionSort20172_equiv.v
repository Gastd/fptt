Require Import Arith List.
Require Import Recdef.

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

Lemma select_min_length: forall l l' x y, select_min x l = (y, l') -> length l = length l'.
Proof.
  induction l.
  - simpl.
    intros l x y H.
    inversion H; subst.
    reflexivity.
  - intros l' x y.
    assert (H: select_min x l = (y, l') -> length l = length l').
        {
          apply IHl.
          }
        generalize dependent y.
        generalize dependent x.
        induction l'.
    + intros x y IH H.
      simpl in H.
      destruct (le_lt_dec x a).
      * destruct (select_min x l).
        inversion H.
      * destruct (select_min a l).
        inversion H.
    + intros x y IH H.
      simpl in H. 
      destruct (le_lt_dec x a).
      * simpl. apply f_equal.
        apply IHl with x y.
        destruct (select_min x l).
        inversion H; subst.
        reflexivity.
      * simpl. apply f_equal.
        apply IHl with a y.
        destruct (select_min a l).
        inversion H; subst.
        reflexivity.
Qed.

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

Lemma ordenada_sub: forall l n, ordenada (n :: l) -> ordenada l.
Proof.
  induction l.
  - intros n H.
    apply lista_vazia.
  - intros n' Hcons.
    inversion Hcons. subst.
    assumption.
Qed.

Fixpoint num_oc n l := 
  match l with
    | nil => 0
    | cons h tl => 
      match eq_nat_dec n h with
        | left _ => S(num_oc n tl) 
        | right _ => num_oc n tl 
      end
  end.

Definition equiv l l' := forall n:nat, num_oc n l = num_oc n l'.

Lemma equiv_trans: forall l l' l'', equiv l l' -> equiv l' l'' -> equiv l l''.
Proof.
  intros l l' l'' H H'.
  unfold equiv in *.
  intro n.
  apply eq_trans with (num_oc n l').
  apply H.
  apply H'.
Qed.

Lemma equiv_cons: forall l l' a, equiv l l' -> equiv (a::l) (a::l').
Proof.
  intros l l' n H.
  unfold equiv in *.
  intros n'.
  simpl.
  destruct (Nat.eq_dec n' n).
  - apply f_equal.
    apply H.
  - apply H.
Qed.

Lemma equiv_cons_comm: forall l l' x z, equiv l l' -> equiv (z :: x :: l) (x :: z :: l').
Proof.
  intros l l' x z H.
  unfold equiv in *.
  intro n. simpl.
  destruct (Nat.eq_dec n z).
  - destruct (Nat.eq_dec n x).
    + apply f_equal. apply f_equal.
      apply H.
    + apply f_equal.
      apply H.
  - destruct (Nat.eq_dec n x).
    + apply f_equal.
      apply H.
    + apply H.
Qed.

Lemma equiv_cons_cons: forall l l' x y z, equiv (x :: l) (y :: l') -> equiv (x :: z :: l) (y :: z :: l').
Proof.
  intros l l' x y z H.
  assert (H': equiv (z :: x :: l) (z :: y :: l')).
  {
    apply equiv_cons; assumption.
  }
  apply equiv_trans with (z :: x :: l).
  - apply equiv_cons_comm.
    unfold equiv; reflexivity.
  - apply equiv_trans with (z :: y :: l').
    + assumption.
    + apply equiv_cons_comm.
      unfold equiv; reflexivity.
Qed.

Lemma select_min_cons_le: forall l l' x y a, select_min x (a::l) = (y,a::l') -> x <= a -> select_min x l = (y,l').
Proof.
  intros l l' x y a H H'.
  simpl in H.
  destruct (le_lt_dec x a).
  - destruct (select_min x l).
    inversion H; subst.
    reflexivity.
  - destruct (select_min a l).
    apply le_not_lt in H'.
    contradiction.
Qed.

Lemma select_min_cons_lt: forall l l' x y a, select_min x (a::l) = (y,x::l') -> a < x -> select_min a l = (y,l').
Proof.
  intros l l' x y a H H'.
  simpl in H.
  destruct (le_lt_dec x a).
  - destruct (select_min x l).
    apply le_not_lt in l0.
    contradiction.
  - destruct (select_min a l).
    inversion H; subst.
    reflexivity.
Qed.

Lemma select_min_equiv: forall l l' x y, select_min x l = (y, l') -> equiv (x::l) (y::l').
Proof.
  induction l.
  - intros l x y H.
    simpl in H.
    inversion H; subst.
    unfold equiv; reflexivity.
  - intros l' x y. case l'.
    + simpl. intro H.
      destruct (le_lt_dec x a).
      * destruct (select_min x l).
        inversion H.
      * destruct (select_min a l).
        inversion H.
    + intros n l'' H.
      assert (H' := H).
      simpl in H.
      destruct (le_lt_dec x a).
      * destruct (select_min x l).
        inversion H; subst.
        apply equiv_cons_cons.
        clear H.
        apply IHl.
        apply select_min_cons_le in H'.
        ** assumption.
        ** assumption.        
      * destruct (select_min a l).
        inversion H; subst.
        apply equiv_trans with (a :: n :: l).
        ** apply equiv_cons_comm.
           unfold equiv; reflexivity.
        ** apply equiv_cons_cons.        
           apply IHl.
           apply select_min_cons_lt with n; assumption.
Qed.

Theorem selectionSort_equiv: forall l, equiv l (select l).
Proof.
  intro l.
  functional induction (select l).
  - unfold equiv.
    reflexivity.
  - unfold equiv in *.
    intro n.
    simpl.
    destruct (Nat.eq_dec n h).
    + destruct (Nat.eq_dec n m).
      * apply f_equal.
        apply select_min_equiv in e0.
        subst.
        unfold equiv in e0.
        apply eq_trans with (num_oc m l').
        assert (H: num_oc m (m :: tl) = num_oc m (m :: l')).
        {
          apply e0.
        }
        simpl in H.
        destruct (Nat.eq_dec m m).
        ** inversion H; subst.
           reflexivity.
        ** apply False_ind.
           apply n; reflexivity.
        ** apply IHl0.
      * apply select_min_equiv in e0.
        unfold equiv in e0.
        assert (H: num_oc n (h :: tl) = num_oc n (m :: l')).
        { apply e0. }
        clear e0.
        simpl in H.
        subst.
        destruct (Nat.eq_dec h h).
        ** destruct (Nat.eq_dec h m).
           *** contradiction.
           *** rewrite H.
               apply IHl0.
        ** destruct (Nat.eq_dec h m).
           *** contradiction.
           *** apply False_ind.
               apply n; reflexivity.
    + destruct (Nat.eq_dec n m).
      * subst.
        apply select_min_equiv in e0.
        unfold equiv in e0.
        assert (H := e0 m).
        simpl in H.
        destruct (Nat.eq_dec m h).
        ** destruct (Nat.eq_dec m m).
           *** contradiction.
           *** apply False_ind.
               apply n; reflexivity.
        ** destruct (Nat.eq_dec m m).
           *** rewrite H.
               apply f_equal.
               apply IHl0.
           *** apply False_ind.
               apply n1; reflexivity.
      * apply select_min_equiv in e0.
        unfold equiv in e0.
        assert (H := e0 n).
        simpl in H.
        destruct (Nat.eq_dec n h).
        ** contradiction.
        ** destruct (Nat.eq_dec n m).
           *** contradiction.
           *** rewrite H.
               apply IHl0.
Qed.

Lemma select_min_leq': forall h l m l', select_min h l = (m, l') -> m <= h.
Admitted.

Lemma select_min_smallest: forall x l y l', select_min x l = (y, l') -> Forall (fun z => y <= z) l'.
Proof.
  intros x l. generalize dependent x.
  induction l.
  - intros x y l' H.
    simpl in H.
    inversion H; subst.
    apply Forall_nil.
  - intros x y l' H.
    simpl in H.
    destruct (le_lt_dec x a).
    + destruct (select_min x l) eqn: H'.
      inversion H; subst. clear H.
      assert (H := H').
      apply select_min_leq' in H'.
      apply Forall_cons.
      * apply le_trans with x; assumption.
      * apply IHl with x; assumption.
    + destruct (select_min a l) eqn: H'.
      inversion H; subst. clear H.
      assert (H := H').
      apply select_min_leq' in H'.
      apply Forall_cons.
      * apply Nat.lt_le_incl in l0.
        apply le_trans with a; assumption.
      * apply Nat.lt_le_incl in l0.
        apply IHl with a; assumption.
Qed.

Lemma select_min_leq: forall h1 l1 m1 m2 h2 l2 l3, select_min h1 l1 = (m1, h2 :: l2) -> select_min h2 l2 = (m2, l3) -> m1 <= m2.
Proof.
  intros h1 l1. generalize dependent h1.
  induction l1.
  - intros h1 m1 m2 h2 l2 l3 H.
    inversion H; subst.
  - intros h1 m1 m2 h2 l2 l3 H1 H2.
    apply IHl1 with h1 h2 l2 l3.
    + assert (H: select_min h1 l1 = (m1, h2 :: l2) -> select_min h2 l2 = (m2, l3) -> m1 <= m2).
    {
      apply IHl1.
    }
      simpl in H1.
      destruct (le_lt_dec h1 a).
      * destruct (select_min h1 l1).
        admit.
      * admit.
    + assumption.
Admitted.

Lemma smallest_equiv:
  forall l y l', equiv l l' -> Forall (fun z => y <= z) l -> Forall (fun z => y <= z) l'.
Proof.
  intros l y l'; revert l y.
  induction l' using list_lenght_ind.
  - admit.
  - intros l y Heq H'.
    assert (Hlength: length l = length l').
    { apply equiv_length; assumption. }
    generalize dependent l'.
    intro l'. case l'.
    + intros IH Heq Hlen.
      apply Forall_nil.
    + intros n l'' IH Heq Hlen.
      apply Forall_cons.
      * admit.
      * apply IH with l''.
        ** simpl. auto.
        ** unfold equiv; reflexivity.
        ** admit.
Admitted.

Lemma select_min_cons: forall h h' a m l l', h <= a -> select_min h (a :: l) = (m, a :: h' :: l') -> select_min h l = (m, h' :: l').

Lemma select_min_min: forall l2 h1 l1 m1 m2 h2 l3, select_min h1 l1 = (m1, h2 :: l2) -> select_min h2 l2 = (m2, l3) -> m1 <= m2.
Proof.
Admitted.

Theorem selectionSort_sorts: forall l, ordenada (select l).
Proof.
  intro l. functional induction (select l).
  - apply lista_vazia.
  - generalize dependent l'.
    intro l'.
    case l'.
    + intros H H1.
      rewrite select_equation.
      apply lista_1.
    + intros h' tl' Hl Hord.
      rewrite select_equation in *.
      destruct (select_min h' tl') as [m' l''] eqn: H.
      apply lista_nv.
      assert (H': m <= m').
      (* { apply select_min_min with tl' h tl h' l''; assumption. } *)
      { apply select_min_min with tl' h tl h' l''; assumption. }
      * assumption.
      * inversion H.
        assumption.
Qed.