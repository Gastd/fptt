(** 116297 - Tópicos Avançados em Computadores - 2017/2           **)
(** Provas Formais: Uma Introdução à Teoria de Tipos - Turma B    **)
(** Prof. Flávio L. C. de Moura                                   **)
(** Email: contato@flaviomoura.mat.br                             **)
(** Homepage: http://flaviomoura.mat.br                           **)

(** Aluno:  Gabriel F P Araujo                                    **)
(** Matrícula: 12/0050943                                         **)

(** Atividade: Formalizar um algoritmo ordenação de sua preferência. *)

(** Esta atividade pode ser realizada individualmente ou em dupla. *)

(** Algumas dicas:
    1. Utilize a biblioteca Arith do Coq. Com isto você terá diversas propriedades sobre os números naturais, e listas de números naturais para utilizar. *)

(** Bubble Sort **)

Require Import Arith.
Require Import Nat.
Require Import Peano.
Require Import Recdef.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Sorting.Sorting.
Require Import Coq.Structures.OrderedType.

Print list.
Print pair.


Function borb(l: list nat) {measure length l}: list nat :=
  match l with
  | nil => nil
  | cons h tl => 
    match tl with
    | nil => cons h nil
    | cons h' tl' => 
      match (le_lt_dec h h') with
      | left _ => cons h (borb tl)
      | right _ => cons h' (borb (cons h tl'))
      end
    end
  end.
Proof.
 - intros; subst.
   simpl.
   apply Nat.lt_succ_diag_r.
 - intros.
   simpl.
   auto.
Defined.

Print le_lt_dec.

Function borb_once(n:nat) (l: list nat) {measure length l}: list nat :=
  match l with
  | nil => (cons n nil)
  | cons h tl => 
    match (le_lt_dec n h) with
    | left _ _ => cons n (cons h tl)
    | right _ _ => cons h (cons n tl)
    end
  end.

Print borb_F.
Print borb_ind.
Print borb_rec.
Print borb_tcc.
Check borb_equation.

Fixpoint num_oc (n:nat) (l:list nat) : nat :=
  match l with
    | nil => 0
    | cons h tl =>
      match le_lt_dec n h with
        | left _ _ => S (num_oc n tl)
        | right _ _ => num_oc n tl
      end
  end.

Definition equiv l l' := forall n, num_oc n l = num_oc n l'.

Lemma Sorted_sub: forall l n, Sorted le (cons n l) -> Sorted le l.
Proof.
  intros.
  induction l.
  - apply Sorted_nil.
  - inversion H; subst.
    assumption.
Qed.

Lemma le_nm_falso: forall n m, (~ (n <= m)) -> (m < n).
Proof.
  induction n.
    - intros m H.
      assert (le 0 m).
      { apply (le_0_n). }
      apply False_ind.
      apply H; assumption.
    - intro m. case m.
      + intro H.
        apply le_n_S.
        apply le_0_n.
      + intros n' Hfalso.
        apply lt_n_S.
        apply IHn.
        intro Hle.
        apply Hfalso.
        apply le_n_S.
        assumption.
Qed.

Lemma Sorted_l_once: forall n l, Sorted le (n :: l) -> ((n :: l) = (borb_once n l)).
Proof.
  induction l.
  - intro H.
    reflexivity.
  - intro H.
    rewrite borb_once_equation.
    destruct (le_lt_dec n a).
    + reflexivity.
    + inversion H; subst.
      inversion H3; subst.
      assert ((~ (n <= a))).
      { apply lt_not_le. assumption. }
      contradiction.
Qed.

Lemma Sorted_l: forall l, Sorted le (l) -> (l = (borb l)).
Proof.
  induction l.
  - intro H.
    reflexivity.
  - intro H.
    rewrite borb_equation.
    destruct (l).
    + reflexivity.
    + destruct (le_lt_dec a n).
      * rewrite <- IHl.
        reflexivity.
        inversion H; subst.
        assumption.
      * inversion H; subst.
        inversion H3; subst.
        assert ((~ (a <= n))).
        { apply lt_not_le. assumption. }
        contradiction.
Qed.

Lemma Sorted_n_l_once: forall h tl, Sorted le (h :: tl) -> ((h :: tl) = borb_once h  tl).
Proof.
  intros.
  functional induction (borb_once h  tl).
  - reflexivity.
  - reflexivity.
  - inversion H; subst.
    inversion H3; subst.
    assert ((~ (h <= h0))).
    { apply lt_not_le. assumption. }
    contradiction.
Qed.


Lemma Sorted_n_l: forall h tl, Sorted le (h :: tl) -> ((h :: tl) = borb (h :: tl)).
Proof.
  intros h tl H.
  functional induction (borb (tl)).
  - reflexivity.
  - rewrite borb_equation.
    destruct (le_lt_dec h h0).
    + reflexivity.
    + inversion H; subst.
      inversion H3; subst.
      assert ((~ (h <= h0))).
      { apply lt_not_le. assumption. }
      contradiction.
  - rewrite <- Sorted_l.
    + reflexivity.
    + assumption.
  - rewrite <- Sorted_l.
    + reflexivity.
    + assumption.
Qed.

(**deveria ser <->**)
(*functional induction (brob l).*)
Lemma borb_preserva_ordem : forall l: list nat, Sorted le l -> Sorted le (borb l).
Proof.
  induction l.
  - intro.
    rewrite borb_equation.
    apply Sorted_nil.
  - intro.
    rewrite <- Sorted_n_l.
    + assumption.
    + assumption.
Qed.

Lemma num_oc_borb: forall l n, num_oc n (l) = num_oc n (borb (l)).
Proof.
  intros l n.
  functional induction (borb l).
  - reflexivity.
  - reflexivity.
  - simpl num_oc.
    case (le_lt_dec n h).
    + intro nh.
      case (le_lt_dec n h').
      * intro nh'.
        rewrite <- IHl0.
        simpl num_oc.
        destruct (le_lt_dec n h').
        **tauto.
        **assert ((~ (n <= h'))).
          { apply lt_not_le. assumption. }
          contradiction.
      * intro h'n.
        rewrite <- IHl0.
        simpl num_oc.
        destruct (le_lt_dec n h').
        **assert ((~ (n <= h'))).
          { apply lt_not_le. assumption. }
          contradiction.
        **auto.
    + intro.
      destruct (le_lt_dec n h').
      * rewrite <- IHl0.
        simpl num_oc.
        destruct (le_lt_dec n h').
        **reflexivity.
        **assert ((~ (n <= h'))).
          { apply lt_not_le. assumption. }
          contradiction.
      * rewrite <- IHl0.
        simpl num_oc.
        destruct (le_lt_dec n h').
        **assert ((~ (n <= h'))).
          { apply lt_not_le. assumption. }
          contradiction.
        **reflexivity.
  - simpl num_oc.
    case (le_lt_dec n h).
    + intro nh.
      case (le_lt_dec n h').
      * intro nh'.
        rewrite <- IHl0.
        simpl num_oc.
        destruct (le_lt_dec n h).
        **reflexivity.
        **assert ((~ (n <= h))).
          { apply lt_not_le. assumption. }
          contradiction.
      * intro h'n.
        rewrite <- IHl0.
        simpl num_oc.
        destruct (le_lt_dec n h).
        **reflexivity.
        **assert ((~ (n <= h))).
          { apply lt_not_le. assumption. }
          contradiction.
    + intro hn.
      case (le_lt_dec n h').
      * intro nh'.
        rewrite <- IHl0.
        simpl num_oc.
        destruct (le_lt_dec n h).
        **assert ((~ (n <= h))).
          { apply lt_not_le. assumption. }
          contradiction.
        **reflexivity.
      * intro h'n.
        rewrite <- IHl0.
        simpl num_oc.
        destruct (le_lt_dec n h).
        **assert ((~ (n <= h))).
          { apply lt_not_le. assumption. }
          contradiction.
        **reflexivity.
Qed.

Lemma num_oc_borb_once_seq: forall l n n', (num_oc n (borb_once n' l)) =  (num_oc n (n' :: l)).
Proof.
  induction l.
  - intros n n'.
    rewrite borb_once_equation.
    reflexivity.
  - intros n n'.
    rewrite borb_once_equation.
    case (le_lt_dec n' a).
    + intro H.
      reflexivity.
    + intro H.
      apply lt_not_le in H.
      simpl.
      case (le_lt_dec n a).
      * intro H'.
        case (le_lt_dec n n').
        ** intro Hle.
           reflexivity.
        ** intro Hlt.
           reflexivity.
      * intro H'.
        case (le_lt_dec n n').
        ** intro Hle.
           reflexivity.
        ** intro Hlt.
           reflexivity.
Qed.

Lemma num_oc_borb_seq: forall l n, (num_oc n (borb l)) =  (num_oc n l).
Proof.
  induction l.
  - intros n.
    rewrite borb_equation.
    reflexivity.
  - intros n.
    rewrite <- num_oc_borb.
    reflexivity.
Qed.

Lemma borb_sorts: forall l a, Sorted le (borb l) -> Sorted le (borb (a :: l)).
Proof.
  intros l a.
  intro H.
  functional induction (borb (l)).
Admitted.

(**
    2. Utilize a formalização do algoritmo de ordenação por inserção desenvolvida em sala como parâmetro. *)
    

Theorem correcao: forall l, (equiv l (borb l)) /\ Sorted le (borb l).
Proof.
  (* induction l. *)
  intro l.
  functional induction (borb l).
  - split.
    * unfold equiv.
      intro n.
      reflexivity.
    * apply Sorted_nil. 
  - split.
    * unfold equiv.
      intro n.
      rewrite -> num_oc_borb.
      reflexivity.
    * apply Sorted_cons.
      ** apply Sorted_nil.
      ** apply HdRel_nil.
  - unfold equiv in *.
    remember (h' :: tl') as l eqn: H.
    split.
    + intro n.
      destruct IHl0 as [Hequiv Hord].
      simpl num_oc.
      destruct (le_lt_dec n h).
      * rewrite <- num_oc_borb.
        reflexivity.
      * rewrite <- num_oc_borb.
        reflexivity.
    + destruct IHl0 as [Hequiv Hord].
      apply Sorted_cons.
      * assumption.
      * inversion Hord.
        ** apply HdRel_nil.
        ** 
  - split.
    * unfold equiv.
      intro n.
      destruct IHl0 as [Hequiv Hord].
      simpl num_oc.
      destruct (le_lt_dec n h).
      ** destruct (le_lt_dec n h').
         *** rewrite <- num_oc_borb.
             simpl num_oc.
             destruct (le_lt_dec n h).
             **** reflexivity.
             **** assert ((~ (n <= h))).
                  { apply lt_not_le. assumption. }
                  contradiction.
         *** rewrite <- num_oc_borb.
             simpl num_oc.
             destruct (le_lt_dec n h).
             **** reflexivity.
             **** assert ((~ (n <= h))).
                  { apply lt_not_le. assumption. }
                  contradiction.
      ** destruct (le_lt_dec n h').
         *** rewrite <- num_oc_borb.
             simpl num_oc.
             destruct (le_lt_dec n h).
             **** assert ((~ (n <= h))).
                  { apply lt_not_le. assumption. }
                  contradiction.
             **** reflexivity.
         *** rewrite <- num_oc_borb.
             simpl num_oc.
             destruct (le_lt_dec n h).
             **** assert ((~ (n <= h))).
                  { apply lt_not_le. assumption. }
                  contradiction.
             **** reflexivity.
    * destruct IHl0 as [Hequiv Hord].
      inversion Hord; subst.
      ** apply Sorted_cons.
         *** apply Sorted_nil.
         *** apply HdRel_nil.
      ** apply Sorted_cons.
         *** auto.
         *** apply HdRel_cons.
             admit.
Admitted.

Theorem correcao_comp: forall (l:list nat), {l' | equiv l l' /\ Sorted le l'}.
Proof.
  intro l.
  exists (borb l).
  apply correcao.
Qed.
