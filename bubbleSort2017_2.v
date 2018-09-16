(** 116297 - Tópicos Avançados em Computadores - 2017/2           **)
(** Provas Formais: Uma Introdução à Teoria de Tipos - Turma B    **)
(** Prof. Flávio L. C. de Moura                                   **)
(** Email: contato@flaviomoura.mat.br                             **)
(** Homepage: http://flaviomoura.mat.br                           **)

(** Aluno:  Gabriel F P Araujo                                    **)
(** Matrícula: 12/0050943                                         **)

(** Formalização do algoritmo Bubble Sort. *)
(**
A ideia geral da formalização do algoritmo Bubble Sort foi feita em sala. Utilizando as informações dadas, faça a prova do teorema bubbleSort_correcao abaixo. Você pode adicionar os lemas (com provas completas!) que achar necessário.
 *)

Require Import Arith.
Require Import Recdef.
Require Import List.
Require Import Sorted.

Open Scope list_scope.

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

Fixpoint bubbleSort (l: list nat) : list nat :=
  match l with
  | nil => l
  | h::tl => bubble (h :: (bubbleSort tl))
  end.

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

Definition equiv l l' := forall n:nat, num_oc n l = num_oc n l'.

Lemma ordenada_n_l: forall h tl, ordenada (h :: tl) -> ((h :: tl) = bubble (h :: tl)).
Proof.
  intros h tl.
  induction (h :: tl).
  - intro H.
    reflexivity.
  - intro H.
    rewrite bubble_equation.
    destruct l.
    + reflexivity.
    + destruct (le_lt_dec a n).
      * rewrite <- IHl.
        ** reflexivity.
        ** inversion H.
           assumption.
      * inversion H; subst.
        apply le_not_lt in H4.
        contradiction.
Qed.

Lemma bubble_preserva_ordem : forall l n, ordenada l -> ordenada (bubble (n::l)).
Proof.
  (* intros l n H. *)
  induction l.
  - intros.
    rewrite bubble_equation.
    apply lista_1.
  - intros.
    rewrite bubble_equation.
    destruct (le_lt_dec n a).
    + rewrite <- ordenada_n_l.
      * apply lista_nv.
        assumption.
        assumption.
      * assumption.
    + rewrite bubble_equation.
      destruct l.
      * apply lista_nv.
        ** apply lista_1.
        ** apply Nat.lt_le_incl.
           assumption.
      * destruct (le_lt_dec n n0).
        ** apply lista_nv.
          *** assert (ordenada (bubble (n :: n0 :: l))).
            { apply IHl. inversion H. assumption. }
              rewrite bubble_equation in H0.
              destruct (le_lt_dec n n0).
              assumption.
              apply le_not_lt in l1.
              contradiction.
          *** apply Nat.lt_le_incl.
              assumption.
        ** apply lista_nv.
          *** assert (ordenada (bubble (n :: n0 :: l))).
            { apply IHl. inversion H. assumption. }
              rewrite bubble_equation in H0.
              destruct (le_lt_dec n n0).
              **** apply le_not_lt in l2.
                   contradiction.
              **** assumption.
          *** inversion H.
              assumption.
Qed.

Lemma num_oc_bubble: forall l n, num_oc n (bubble l) =  (num_oc n l).
Proof.
  intros l n.
  functional induction (bubble l).
  - simpl num_oc.
    destruct (Nat.eq_dec n h0).
    + destruct (Nat.eq_dec n h1).
      * rewrite IHl0.
        simpl num_oc.
        destruct (Nat.eq_dec n h1).
        ** tauto.
        ** contradiction.
      * rewrite IHl0.
        simpl num_oc.
        destruct (Nat.eq_dec n h1).
        ** contradiction.
        ** tauto.
    + destruct (Nat.eq_dec n h1).
      * rewrite IHl0.
        simpl num_oc.
        destruct (Nat.eq_dec n h1).
        ** tauto.
        ** contradiction.
      * rewrite IHl0.
        simpl num_oc.
        destruct (Nat.eq_dec n h1).
        ** contradiction.
        ** tauto.
  - simpl num_oc.
    destruct (Nat.eq_dec n h0).
    + destruct (Nat.eq_dec n h1).
      * rewrite IHl0.
        simpl num_oc.
        destruct (Nat.eq_dec n h0).
        ** reflexivity.
        ** contradiction.
      * rewrite IHl0.
        simpl num_oc.
        destruct (Nat.eq_dec n h0).
        ** reflexivity.
        ** contradiction.
    + destruct (Nat.eq_dec n h1).
      * rewrite IHl0.
        simpl num_oc.
        destruct (Nat.eq_dec n h0).
        ** contradiction.
        ** reflexivity.
      * rewrite IHl0.
        simpl num_oc.
        destruct (Nat.eq_dec n h0).
        ** contradiction.
        ** reflexivity.
  - reflexivity.
Qed.

Theorem bubbleSort_correcao: forall l, equiv (bubbleSort l) l /\ ordenada (bubbleSort l).
Proof.
  induction l.
  - split.
    + simpl.
      unfold equiv.
      intro n.
      reflexivity.
    + simpl.
      apply lista_vazia.
  - destruct IHl as [Hequiv Hord].
    split.
    + simpl.
      unfold equiv in *.
      intro n'.
      assert (H:  num_oc n' (bubble (a :: (bubbleSort l))) = num_oc n' ( a :: (bubbleSort l))).
      { apply num_oc_bubble. }
      apply Nat.eq_trans with (num_oc n' (cons a (bubbleSort l))).
      * assumption.
      * simpl. destruct (Nat.eq_dec n' a).
        ** apply eq_S.
           apply Hequiv.
        ** apply Hequiv.
    + simpl.
      assert (ordenada (bubbleSort l) -> ordenada (bubble (a :: bubbleSort l))).
      { apply bubble_preserva_ordem. }
      apply H.
      assumption.
Qed.