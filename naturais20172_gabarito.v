(** 116297 - Tópicos Avançados em Computadores - 2017/2           **)
(** Provas Formais: Uma Introdução à Teoria de Tipos - Turma B    **)
(** Prof. Flávio L. C. de Moura                                   **)
(** Email: contato@flaviomoura.mat.br                             **)
(** Homepage: http://flaviomoura.mat.br                           **)

(**                   GABARITO                                    **)

(** Números naturais: *)

Inductive natural :=
| z: natural 
| s: natural -> natural. 

(** Igualdade proposicional. *)
Inductive eq_prop : natural -> natural -> Prop :=
| eq_prop_refl: forall z, eq_prop z z.

Notation "A == B" := (eq_prop A B) (at level 70).
  
(** Disjunção: *)
Inductive disj (A B: Prop) : Set :=
  | esq : A -> disj A B
  | dir : B -> disj A B.

(** Definimos o absurdo como um tipo indutivo vazio, isto é, sem construtores. Desta maneira podemos representar a negação de A como sendo (A -> falso). *)
Inductive falso: Prop :=.

(** Exercício 1: *)
Lemma eq_sn_not_n: forall n, s n == n -> falso.
Proof.
  induction n.
  - intro Hfalse.
    inversion Hfalse.
  - intro Hs. 
    apply IHn.
    inversion Hs.
    assumption.
Qed.    

(** Exercício 2: Decidibilidade da igualdade. *)
Lemma eq_dec: forall (n m: natural), disj (n == m) ((n == m-> falso)).
Proof.
  induction n.
  - induction m.
    + apply esq.
      apply eq_prop_refl.
    + destruct IHm as [Hm_is_z | Hm_not_z].
      * apply dir.
        intro Hfalse.
        inversion Hfalse.
      * apply dir.
        intro Hfalse.
        inversion Hfalse.
  - induction m.
    + apply dir.
      intro Hfalse.
      inversion Hfalse.
    + destruct IHm as [Hm_is_s | Hm_not_s].
      * apply dir.
        intro Hsmn.
        inversion Hsmn. subst.
        apply eq_sn_not_n with m.
        assumption.
      * assert (disj (n == m) (n == m -> falso)).
        { apply IHn. }
        destruct H.
        ** apply esq.
           inversion e. subst.
           apply eq_prop_refl.
        ** apply dir.
           intro Hs.
           inversion Hs. subst.
           apply f.
           apply eq_prop_refl.
Defined.           
           
(** Considere o predicado binário le que define a relação de "menor ou igual que".  *)
Inductive le : natural -> natural -> Prop :=
| le_refl: forall n, le n n
| le_n_sm: forall n m, le n m -> le n (s m).

(** Exercício 3: *)
Lemma le_n_z: forall n, le n z -> n == z.
Proof.
  intro n. case n.
  - intro H.
    apply eq_prop_refl.
  - intros n' H.
    inversion H.
Qed.    

(** Exercício 4: O zero é menor ou igual que qualquer natural. *)
Lemma le_z: forall n, le z n.
Proof.
  induction n.
  - apply le_refl.
  - apply le_n_sm.
    assumption.
Qed.    
  
(** Exercício 5: *)
Lemma le_trans: forall n m k, le n m -> le m k -> le n k.
Proof.
 intros n m k Hnm Hmk.
 induction Hmk.
 - assumption.
 - apply le_n_sm.
   apply IHHmk.
   assumption.
Qed.   

(** Exercício 6: *)
Lemma le_s: forall n m, le (s n) (s m) <-> le n m.
Proof.
  intros n m.
 split.  
  - intro H.
    inversion H; subst.
    + apply le_refl.
    + apply le_trans with (s n). 
      * apply le_n_sm.
        apply le_refl.
      * assumption.
  - intro H.
    induction H.
    + apply le_refl.
    + apply le_n_sm.
      assumption.
Qed.      

(** Exercício 7: *)
Lemma le_n_sm_eq: forall m n, (le n m -> falso) -> (le n (s m)) -> n == s m.
Proof.
  intros m n Hfalso Hle.
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
Qed.