(** 116297 - Tópicos Avançados em Computadores - 2017/2           **)
(** Provas Formais: Uma Introdução à Teoria de Tipos - Turma B    **)
(** Prof. Flávio L. C. de Moura                                   **)
(** Email: contato@flaviomoura.mat.br                             **)
(** Homepage: http://flaviomoura.mat.br                           **)

(** Aluno:                                                        **)
(** Matrícula:                                                    **)

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

Lemma equiv_nil: forall l, equiv nil l -> l = nil.
Proof.
  induction l.
  - intro H.
    reflexivity.
  - intro H.
    unfold equiv in H.
    assert (H': num_oc a nil =  num_oc a (a :: l)).
    {
      apply H.
    }
    simpl in H'.
    destruct (Nat.eq_dec a a).
    + inversion H'.
    + apply False_ind.
      apply n; reflexivity.
Qed.

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

Lemma selectionSort_equiv: forall l, equiv l (select l).
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

(** Selection Sort sorts. *)

Lemma forall_leq_head: forall y h l, Forall (fun z => y <= z) (h::l) -> y <= h.
Proof.
  intros y h l H.
  inversion H; subst.
  assumption.
Qed.

Inductive Permutation : list nat -> list nat -> Prop :=
| perm_nil: Permutation nil nil
| perm_skip x l l' : Permutation l l' -> Permutation (x::l) (x::l')
| perm_swap x y l : Permutation (y::x::l) (x::y::l)
| perm_trans l l' l'' :
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Lemma forall_permutation: forall y l l', Permutation l l' -> Forall (fun z => y <= z) l -> Forall (fun z => y <= z) l'.
Proof.
  intros y l l' H H'.
  induction H.
  - apply Forall_nil.
  - inversion H'; subst.
    apply Forall_cons.
    + assumption.
    + apply IHPermutation.
      assumption.
  - inversion H'; subst.
    inversion H2; subst.
    apply Forall_cons.
    + assumption.
    + apply Forall_cons; assumption.
  - apply IHPermutation2.
    apply IHPermutation1.
    assumption.
Qed.

Lemma Permutation_implies_equiv: forall l l', Permutation l l' -> equiv l l'.
Proof.
  intros l l' H.
  induction H.
  - unfold equiv; reflexivity.
  - unfold equiv in *.
    intro n.
    simpl num_oc.
    destruct (Nat.eq_dec n x).
    + apply f_equal.
      apply IHPermutation.
    + apply IHPermutation.
  - unfold equiv in *.
    intro n.
    simpl num_oc at 1.
    destruct (Nat.eq_dec n y).
    + destruct (Nat.eq_dec n x).
      * simpl num_oc.
        destruct (Nat.eq_dec n x).
        ** destruct (Nat.eq_dec n y).
           *** reflexivity.
           *** contradiction.
        ** destruct (Nat.eq_dec n y).
           *** contradiction.
           *** contradiction.
      * simpl num_oc.
        destruct (Nat.eq_dec n x).
        ** destruct (Nat.eq_dec n y).
           *** contradiction.
           *** contradiction.
        ** destruct (Nat.eq_dec n y).
           *** reflexivity.
           *** contradiction.
    + destruct (Nat.eq_dec n x).
      * simpl num_oc.
        destruct (Nat.eq_dec n x).
        ** destruct (Nat.eq_dec n y).
           *** contradiction.
           *** reflexivity.
        ** destruct (Nat.eq_dec n y).
           *** reflexivity.
           *** contradiction.
      * simpl num_oc.
        destruct (Nat.eq_dec n x).
        ** destruct (Nat.eq_dec n y).
           *** contradiction.
           *** contradiction.
        ** destruct (Nat.eq_dec n y).
           *** contradiction.
           *** reflexivity.
  - unfold equiv in *.
    intro n.
    rewrite <- IHPermutation2.
    apply IHPermutation1.
Qed.

Lemma list_length_ind: forall (A : Type) (P : list A -> Prop),
       P nil ->
       (forall (l : list A), (forall (l' : list A), length l' < length l -> P l') -> P l) ->
       forall l : list A, P l.
Proof.
  intros A P BI PI.
  assert (H: forall (l1 l2: list A), length l2 <= length l1 -> P l2).
  {
    induction l1.
    - intros l H.
      inversion H.
      apply length_zero_iff_nil in H1.
      subst. assumption.
    - intros l2 H.
      apply PI.
      simpl in H.
      intros l' H'.
      apply IHl1.
      assert (H'': length l' < S (length l1)).
      {
        apply Nat.lt_le_trans with (length l2); assumption.
      }
      apply lt_n_Sm_le; assumption.
  }
  intro l.
  apply H with l.
  auto.
Qed.

Lemma equiv_implies_Permutation: forall l l', equiv l l' -> Permutation l l'.
Proof.
  intros l. induction l using list_length_ind.
  - intros l' H.
    apply equiv_nil in H. subst.
    apply perm_nil.
  - intros l' H'.
    generalize dependent l'. intro l'. case l'.
    + admit.
    + intros.
Admitted.

Lemma Permutation_equiv: forall l l', Permutation l l' <-> equiv l l'.
Proof.
  intros l l'.
  split.
  - apply Permutation_implies_equiv.
  - apply equiv_implies_Permutation.
Qed.

Lemma forall_equiv: forall y l l', Forall (fun z => y <= z) l -> equiv l l' -> Forall (fun z => y <= z) l'.
Proof.
  intros y l l' H H'.
  apply equiv_implies_Permutation in H'.
  apply forall_permutation with l; assumption.
Qed.

Lemma select_min_leq: forall h l m l', select_min h l = (m, l') -> m <= h.
Proof.
  intros h l; revert h; induction l using list_length_ind.
  - intros h m l' H.
    inversion H.
    auto.
  - intros h m l' H'.
    generalize dependent l.
    intro l.
    case l.
    + intros H H1.
      inversion H1.
      apply le_refl.
    + intros n l0 H H1.
      simpl in H1.
      destruct (le_lt_dec h n).
      * destruct (select_min h l0) eqn: H2.
        inversion H1; subst.
        apply H with l0 l2.
        ** simpl.
           apply lt_n_Sn.
        ** assumption.
      * destruct (select_min n l0) eqn: H2.
        inversion H1; subst.
        apply le_trans with n.
        ** apply H with l0 l2.
           *** simpl.
               apply lt_n_Sn.
           *** assumption.
        ** apply Nat.lt_le_incl in l1.
           assumption.
Qed.

Lemma select_min_smallest:
  forall x l y l', select_min x l = (y, l') ->
     Forall (fun z => y <= z) l'.
Proof.
  intros x l; revert x; induction l using list_length_ind.
  - intros x y l' HI.
    inversion HI; subst.
    apply Forall_nil.
  - intros x y l' H'.
    generalize dependent l'. intro l'.
    case l'.
    + intros H H1.
      inversion H1; subst.
      apply Forall_nil.
    + intros n l0 H H1.
      simpl in H1.
      destruct (select_min x l0) eqn: H2.
        inversion H1. subst.
        apply forall_leq_head with l0.
        apply Forall_cons.
Admitted.

Lemma select_forall: forall m l, ordenada l ->
                                 Forall (fun z => m <= z) l ->
                                 ordenada (m :: l).
Proof.
  intros m l.
  case l.
  - intros H H'.
    apply lista_1.
  - intros n l' H H'.
    apply lista_nv.
    + assumption.
    + inversion H'; subst.
      assumption.
Qed.

Theorem selectionSort_sorts: forall l, ordenada (select l).
Proof.
  intro l.
  functional induction (select l).
  - apply lista_vazia.
  - generalize dependent l'.
    intro l'.
    induction l' using list_length_ind.
    + intros H H1.
      rewrite select_equation.
      apply lista_1.
    + intros H0 H1.
      case l'.
      * rewrite select_equation.
        apply lista_1.
      * intros n l.
        rewrite select_equation.
        destruct (select_min n l) as [m' l''] eqn: H2.
        apply lista_nv.
        ** apply H.
        **


    case l'.
    + intros H H1.
      rewrite select_equation.
      apply lista_1.
    + intros n l Hl Hord.
      rewrite select_equation in *.
      destruct (select_min n l) as [m' l''] eqn: H.
      assert (H': ordenada (m' :: select l'') ->
                  Forall (fun z => m <= z) (m' :: select l'') ->
                  ordenada (m :: (m' :: select l''))).
      { apply select_forall. }
      apply lista_nv.
      * assumption.
      * inversion H.
        inversion Hl.
        apply select_min_leq in H.
        apply select_min_smallest in H2.
        apply forall_leq_head in H2.
        admit.
Admitted.

(** Exercício extra. *)
Lemma select_min_min: forall h1 l1 m1 m2 h2 l2 l3, select_min h1 l1 = (m1, h2::l2) -> select_min h2 l2 = (m2, l3) -> m1 <= m2.
Proof.
Admitted.
