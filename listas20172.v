(** 116297 - TÃ³picos AvanÃ§ados em Computadores - 2017/2           **)
(** Provas Formais: Uma IntroduÃ§Ã£o Ã  Teoria de Tipos - Turma B    **)
(** Prof. FlÃ¡vio L. C. de Moura                                   **)
(** Email: contato@flaviomoura.mat.br                             **)
(** Homepage: http://flaviomoura.mat.br                           **)

(** Aluno: Gabriel F P Araujo                                     **)
(** MatrÃ­cula: 12/0050943                                         **)

Require Import naturais20172_gabarito.

Inductive lista :=
| nil : lista
| cons : natural -> lista -> lista.

Fixpoint num_oc (n:natural) (l:lista) : natural :=
  match l with
    | nil => z
    | cons h tl =>
      match eq_dec n h with
        | esq _ _ _ => s (num_oc n tl)
        | dir _ _ _ => num_oc n tl
      end
  end.

Definition equiv l l' := forall n, num_oc n l = num_oc n l'.

Inductive ordenada : lista -> Prop :=
  | nil_ord : ordenada nil
  | one_ord : forall n:natural, ordenada (cons n nil)
  | mult_ord : forall (x y : natural) (l : lista), ordenada (cons y l) -> le x y -> ordenada (cons x (cons y l)).

(** ExercÃ­cio 1: *)
Lemma ordenada_sub: forall l n, ordenada (cons n l) -> ordenada l.
Proof.
  intros.
  induction l.
  - apply nil_ord.
  - intros.
    inversion H.
    assumption.
Qed.

Fixpoint insercao_seq (n: natural) l :=
  match l with
    | nil => (cons n nil)
    | cons h tl =>
      match le_dec n h with
        | esq _ _ _ => cons n l
        | dir _ _ _ => cons h (insercao_seq n tl)
      end
  end.
  
  Print le_dec.

(** ExercÃ­cio 2: *)
Lemma insercao_seq_preserva_ordem : forall l n, ordenada l -> ordenada (insercao_seq n l).
Proof.
  intros.
  induction H.
  - simpl insercao_seq.
    apply one_ord.
  - simpl insercao_seq.
    case (le_dec n n0).
    + intro.
      apply mult_ord.
      apply one_ord.
      assumption.
    + intro.
      apply mult_ord.
      * apply one_ord.
      * apply le_nm_falso.
        assumption.
  - simpl insercao_seq.
    case (le_dec n x).
    + intro.
      apply mult_ord.
      * apply mult_ord.
        assumption.
        assumption.
      * assumption.
    + intro.
      case (le_dec n y).
      * intro.
        apply mult_ord.
        **apply mult_ord.
          assumption.
          assumption.
        **apply (le_nm_falso).
          intro.
          apply f.
          assumption.
      * intro.
        apply mult_ord.
        **apply le_nm_falso in f0.
          apply le_nm_falso in f.
          apply (ordenada_sub (cons y (insercao_seq n l))).
          apply (ordenada_sub y ((insercao_seq n l))).
          admit.
        **assumption.
Admitted.
  
Lemma eq_dec_n_n: forall n: natural, disj (eq_prop n n) (eq_prop n n -> falso) -> n == n.
Proof.
  intros.
  apply eq_prop_refl.
Qed.

(*Lemma num_oc_comm: forall n n', *)

(** ExercÃ­cio 3: *)
Lemma num_oc_insercao_seq: forall l n n', num_oc n (insercao_seq n' l) ==  num_oc n (cons n' l).
Proof.
  induction l.
  - intros n n'.
    simpl insercao_seq.
    apply eq_prop_refl.
  - intros n' n''.
    simpl insercao_seq.
    case (le_dec n'' n).
    + intro H.
      apply eq_prop_refl.
    + intro H.
      apply le_nm_falso in H.
      simpl.
      case (eq_dec n' n).
      * intro H'.
        case (eq_dec n' n'').
        ** intro Heq.
           apply eq_s.
           assert (Heq': num_oc n' (insercao_seq n'' l) == num_oc n' (cons n'' l)).
           { apply IHl. }
           simpl in Heq'.
           destruct (eq_dec n' n'').
            *** assumption.
            *** contradiction.
        ** intro Hfalso.
           apply eq_s.
           assert (Heq': num_oc n' (insercao_seq n'' l) == num_oc n' (cons n'' l)).
           { apply IHl. }
           simpl num_oc in Heq'.
           destruct (eq_dec n' n'').
            *** contradiction.
            *** assumption.
      * intro H'.
        case (eq_dec n' n'').
        ** intro Heq.
Admitted.