(** 116297 - Tópicos Avançados em Computadores - 2017/2           **)
(** Provas Formais: Uma Introdução à Teoria de Tipos - Turma B    **)
(** Prof. Flávio L. C. de Moura                                   **)
(** Email: contato@flaviomoura.mat.br                             **)
(** Homepage: http://flaviomoura.mat.br                           **)

(** Aluno: Gabriel F P Araujo                                     **)
(** Matrícula: 12/0050943                                         **)

(** Números naturais: **)

Inductive natural :=
| z: natural
| s: natural -> natural.

(** Igualdade proposicional. *)
Inductive eq_prop : natural -> natural -> Prop :=
| eq_prop_refl: forall x, eq_prop x x.

Notation "A == B" := (eq_prop A B) (at level 70).

(** Disjunção: *)
Inductive disj (A B: Prop) : Set :=
  | esq : A -> disj A B
  | dir : B -> disj A B.

(** Definimos o absurdo como um tipo indutivo vazio, isto é, sem construtores. Desta maneira podemos representar a negação de A como sendo (A -> falso). *)
Inductive falso: Prop :=.

(** Exercício 2: *)
Lemma eq_sn_not_n: forall n, (eq_prop (s n) n) -> falso.
Proof.
  induction n.
  - intro.
    inversion H.
  - intro.
    apply IHn.
    inversion H.
    exact H.
Qed.

(** Exercício 1: Decidibilidade da igualdade. *)
Lemma eq_dec: forall (n m: natural), disj (eq_prop n m) (((eq_prop n m)-> falso)) .
Proof.
  induction n.
  - induction m.
    + apply esq.
      apply eq_prop_refl.
    + destruct IHm.
      * apply dir.
        intro.
        inversion H.
      * apply dir.
        intro.
        inversion H.
  - induction m.
    + apply dir.
      intro.
      inversion H.
    + destruct IHm.
      * apply dir.
        intro.
        inversion H.
        rewrite H2 in e.
        inversion e.
        apply (eq_sn_not_n m).
        exact e.
      * assert (disj (eq_prop n m) (eq_prop n m -> falso)).
        { apply IHn. }
        destruct H.
         apply esq.
           inversion e.
           apply eq_prop_refl.
         apply dir.
         intro.
         inversion H.
         rewrite H2 in f0.
         apply f0.
         apply eq_prop_refl.
Defined.

Lemma eq_s: forall n m, n == m -> (s n) == (s m).
Proof.
  intros.
  induction H.
  apply eq_prop_refl.
Qed.

Lemma eq_comm: forall n m, n == m -> m == n.
Proof.
  intros.
  induction H.
  apply eq_prop_refl.
Qed.

Lemma eq_trans: forall n m l, n == m -> m == l -> n == l.
Proof.
  intros.
  induction H0.
  assumption.
Qed.

(** Considere o predicado binário le que define a relação de "menor ou igual que".  *)
Inductive le : natural -> natural -> Prop :=
| le_refl: forall n, le n n
| le_n_sm: forall n m, le n m -> le n (s m).

(** Exercício 3: *)
Lemma le_n_z: forall n, le n z -> (eq_prop n z).
Proof.
  intros.
  inversion H.
  apply eq_prop_refl.
Qed.

(** Exercício 4: O zero é menor ou igual que qualquer natural. *)
Lemma le_z: forall n, le z n.
Proof.
  intros.
  induction n.
  apply le_refl.
  apply le_n_sm.
  apply IHn.
Qed.

(** Exercício 5: *)
Lemma le_trans: forall n m k, le n m -> le m k -> le n k.
Proof.
  intros.
  induction H0.
  - exact H.
  - destruct IHle.
    * exact H.
    * inversion H0. subst.
      + apply le_n_sm.
        assumption.
      + apply le_n_sm.
        apply le_refl.
    * apply le_n_sm.
      apply le_n_sm.
      assumption.
Qed.

(** Exercício 6: *)
Lemma le_s: forall n m, le (s n) (s m) <-> le n m.
Proof.
  intros.
  split.
  - intro.
    inversion H. subst.
    * apply le_refl.
    * subst.
      assert (le n (s n) -> le (s n) m -> le n m).
      { intros. apply (le_trans n (s n) m). assumption. assumption. }
      apply H0.
      + apply le_n_sm.
        apply le_refl.
      + assumption.
  - intro.
    induction H.
    + apply le_refl.
    + apply le_n_sm.
      assumption.
Qed.

(** Exercício 7: *)
Lemma le_n_sm_eq: forall n m, (le n m -> falso) -> (le n (s m)) -> n == (s m).
Proof.
  intros n m Hfalso Hle.
  inversion Hle; subst.
  - apply eq_prop_refl.
  - apply falso_ind.
    apply Hfalso.
    assumption.
Qed.

(** Exercício 8: *)
Lemma le_nm_falso: forall n m, (le n m -> falso) -> (le m n).
Proof.
    induction n.
    - intros m H.
      assert (le z m).
      { apply le_z. }
      apply falso_ind.
      apply H; assumption.
    - intro m. case m.
      + intro H.
        apply le_n_sm.
        apply le_z.
      + intros n' Hfalso.        
        apply le_s.
        apply IHn.
        intro Hle.
        apply Hfalso.
        apply le_s.
        assumption.
Qed.

(** Exercício 9: *)
Lemma le_sn_not_n: forall n, le (s n) n -> falso.
Proof.
  induction n.
  - intro H.
    inversion H.
  - intro H.
    apply IHn.
    inversion H; subst.
      * assumption.
      * apply le_trans with (s(s n)).
        ** apply le_n_sm.
           apply le_refl.
        ** assumption.
Qed.

(** Exercício 10: O predicado [le] é decidível. *)
Lemma le_dec: forall (n m: natural), disj (le n m) (le n m -> falso).
Proof.
  induction n.
  - intro m.
    apply esq. 
    apply le_z.
  - induction m.
    + apply dir.
      intro H.
      inversion H.
    + destruct IHm as [H1 | H2].
      * apply esq.
        apply le_n_sm.
        assumption.
      * destruct (IHn m).
        ** apply esq.
           apply le_s.
           assumption.
        ** apply dir.
           intro H.
           apply f.
           apply le_s.
           assumption.
Defined. 
(**Defined**)