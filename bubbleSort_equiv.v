Require Import Arith.
Require Import Recdef.
Require Import List.

Open Scope list_scope.

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

(** Prove os dois lemas a seguir. *)
Lemma equiv_sub: forall l l' a, equiv l l' -> equiv (a::l) (a::l').
Proof.
  intros l l' a H.
  unfold equiv in *.
  intro n.
  simpl num_oc.
  destruct (Nat.eq_dec n a).
  - subst.
    rewrite <- H.
    reflexivity.
  - subst.
    rewrite <- H.
    reflexivity.
Qed.

Lemma equiv_trans: forall l l' l'', equiv l l' -> equiv l' l'' -> equiv l l''.
Proof.
  intros l l' l'' H H1.
  unfold equiv in *.
  intro n.
  rewrite <- H1.
  rewrite <- H.
  reflexivity.
Qed.

Function bubble l {measure length l} :=
  match l with
    | h0 :: h1 :: tl =>
      match le_lt_dec h0 h1 with
        | left _ => h0 :: (bubble (h1 :: tl))
        | right _ => h1 :: (bubble (h0 :: tl))
      end
    | _ => l
    end.
Proof.
  intros. simpl. auto.
  intros. simpl. auto.
Defined.

Compute (bubble (1::3::0::nil)).

Lemma bubble_equiv: forall l, equiv (bubble l) l.
Proof.
  intro l.
  functional induction (bubble l).
  - unfold equiv in *.
    intro n.
    remember (h1 :: tl) as l eqn: H.
    simpl num_oc.
    destruct (Nat.eq_dec n h0).
    + rewrite IHl0.
      reflexivity.
    + rewrite IHl0.
      reflexivity.
  - unfold equiv in *.
    intro n.
    simpl num_oc at 1.
    destruct (Nat.eq_dec n h1).
    + rewrite IHl0.
      simpl.
      destruct (Nat.eq_dec n h0).
      * destruct (Nat.eq_dec n h1).
        ** reflexivity.
        ** apply False_ind.
           contradiction.
      * destruct (Nat.eq_dec n h1).
        ** reflexivity.
        ** apply False_ind.
           contradiction.
    + rewrite IHl0.
      simpl.
      destruct (Nat.eq_dec n h0).
      * destruct (Nat.eq_dec n h1).
        ** apply False_ind.
           contradiction.
        ** reflexivity.
      * destruct (Nat.eq_dec n h1).
        ** apply False_ind.
           contradiction.
        ** reflexivity.
  - unfold equiv.
    reflexivity.
Qed.

(** Construa uma nova prova do lema anterior usando o fato que equiv é uma relação transitiva. *)
Lemma bubble_equiv': forall l, equiv (bubble l) l.
Proof.
  intro l.
  functional induction (bubble l).
  - unfold equiv in *.
    intro n.
    remember (h1 :: tl) as l eqn: H.
    rewrite  (equiv_sub (bubble l) l).
    + reflexivity.
    + assumption.
  - unfold equiv in *.
    intro n.
    rewrite (equiv_sub (bubble (h0 :: tl)) (h0 :: tl)).
    simpl num_oc at 1.
    + destruct (Nat.eq_dec n h0).
      * destruct (Nat.eq_dec n h1).
        ** subst.
           inversion _x.
           admit. subst.
           contradiction.
        **
      *
    + assumption.
  - unfold equiv in *.
    intro n.
    reflexivity.
Qed.

(** Adicionar definição de bubbleSort *)
Fixpoint bubbleSort (l: list nat) : list nat :=
  match l with
  | nil => l
  | h::tl => bubble (h :: (bubbleSort tl))
  end.

Compute (bubbleSort (1::3::0::nil)).

Lemma bubbleSort_equiv: forall l, equiv (bubbleSort l) l.
Proof.
  induction l.
  - simpl.
    unfold equiv.
    reflexivity.
  - unfold equiv in *.
    intro n.
    simpl bubbleSort.
    simpl num_oc at 2.
    destruct (Nat.eq_dec n a).
    + rewrite <- IHl.
      assert (H: S (num_oc n (bubbleSort l)) = num_oc n (a::(bubbleSort l))).
      { simpl num_oc at 2.
        destruct (Nat.eq_dec n a).
        - reflexivity.
        - apply False_ind.
          contradiction. }
      rewrite H.
      generalize n.
      fold (equiv  (bubble(a :: bubbleSort l)) (a :: bubbleSort l)).
      apply bubble_equiv.
    + rewrite <- IHl.
      assert (H: num_oc n (bubbleSort l) = num_oc n (a::(bubbleSort l))).
      { simpl num_oc at 2.
        destruct (Nat.eq_dec n a).
        - apply False_ind.
          contradiction.
        - reflexivity. }
      rewrite H.
      generalize n.
      fold (equiv  (bubble(a :: bubbleSort l)) (a :: bubbleSort l)).
      apply bubble_equiv.
Qed.