(** Atividade sobre os numerais de Church. Adaptado de [Pierce:SF]. *)

Definition admit {T: Type} : T.  Admitted.

(** Tipo dos numerais. *)
Definition num := forall X : Type, (X -> X) -> X -> X.

(** Alguns numerais. *)
Definition zero : num :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition um : num := 
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition dois : num :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition tres : num :=
  fun (X : Type) (f : X -> X) (x : X) => f (f (f x)).

(** Exercício 1: Defina a função sucessor. *)
Definition suc (n : num) : num := 
  fun (X: Type) (f : X -> X) (x : X) => f (n X f x).

(** Exercício 2: Prove os seguintes fatos: *)
Example suc_1 : suc zero = um.
Proof.
  apply suc.
  - unfold num.
    intros.
    assumption.
  - intro H.
    unfold suc.
    unfold zero.
    unfold um.
    reflexivity.
  - unfold suc.
    unfold zero.
    unfold um.
    reflexivity.
Qed.

Example suc_2 : suc um = dois.
Proof.
  unfold suc.
  unfold um.
  unfold dois.
  reflexivity.
Qed.

Example suc_3 : suc dois = tres.
Proof.
  unfold suc.
  unfold dois.
  unfold tres.
  reflexivity.
Qed.

(** 
De uma forma geral podemos gerar o numeral de Church Cn, dado o natural n.
 *)

Fixpoint ch (n:nat) : num :=
  match n with
    | O => zero
    | S k => suc (ch k)
  end.

Compute (ch 0).
Compute (ch 1).
Compute (ch 2).
Compute (ch 3).

(** Exercício 3: *)
Theorem suc_S: forall n,  suc (ch n) = (ch (S n)).
Proof.
  intro n.
  simpl ch.
  reflexivity.
Qed.

(** Exercício 4: Defina a adição de dois numerais. *)
Definition soma (n m : num) : num := 
  fun (X : Type) (f: X->X) (x: X) => m X f (n X f x).

(** Exercício 5: Prove os seguintes fatos: *)
Example soma_1 : soma zero um = um.
Proof.
  unfold soma.
  unfold zero.
  unfold um.
  reflexivity.
Qed.

Example soma_2 : soma dois tres = soma tres dois.
Proof.
  unfold soma.
  unfold dois.
  unfold tres.
  reflexivity.
Qed.

Example soma_3 :
  soma (soma dois dois) tres = soma um (soma tres tres).
Proof.
  unfold soma.
  unfold dois.
  unfold tres.
  unfold um.
  reflexivity.
Qed.

(** Exercício 6: *)
Theorem suc_soma: forall n m, suc(soma n m) = soma (suc n) m.
Proof.
  intros n m.
  unfold suc.
  unfold soma.
  (* reflexivity. *)
Admitted.

(** Exercício 7: *)
Theorem suc_soma': forall n m, suc(soma (ch n) m) = soma (ch n) (suc m).
  intros n m .
  unfold ch.
  unfold suc.
  unfold soma.
  unfold zero.
  reflexivity.
Qed.

(** Exercício 8: *)
Theorem suc_soma_zero: forall m, suc(soma zero m) = soma zero (suc m).
Proof.
  intro m.
  unfold soma.
  unfold suc.
  reflexivity.
Qed.

(** Exercício 9: *)
Theorem soma_com: forall n m, soma  (ch n) (ch m) = soma (ch m) (ch n).
Proof.
  induction n.
  - intro m.
    simpl ch.
    unfold soma.
    unfold zero.
    reflexivity.
  - intro m.
    simpl ch.
    rewrite <- suc_soma.
    rewrite -> IHn.
    unfold suc.
    unfold soma.
    reflexivity.
Qed.

(** Exercício 10: *)
Theorem soma_zero_dir: forall n, soma (ch n) zero = (ch n).
Proof.
  intro n.
  unfold soma.
  unfold zero.
  reflexivity.
Qed.

(** Exercício 11: *)
Theorem soma_zero_esq: forall n, soma zero n = n.
Proof.
  intro n.
  unfold soma.
  unfold zero.
  reflexivity.
Qed.

(** Exercício 12: *)
Theorem suc_soma_um: forall n, suc (ch n) = soma um (ch n).
Proof.
  intro n.
  induction n.
  - unfold suc.
    unfold soma.
    unfold um.
    reflexivity.
  - simpl ch.
    rewrite -> IHn.
    rewrite -> suc_soma.
    unfold um.
    unfold soma.
    unfold suc.
    reflexivity.
Qed.

(** Exercício 13: *)
Theorem soma_assoc: forall n m k, soma (soma n m) k = soma n (soma m k).
Proof.
  intros n m k.
  unfold soma.
  reflexivity.
Qed.

(** Exercício 14: Defina a multiplicação de dois numerais. *)
Definition mult (n m : num) : num := 
  fun (X : Type) (f: X -> X) => m X (n X f).

(** Exercício 15: Prove os seguintes fatos: *)
Example mult_1 : mult um um = um.
Proof.
  unfold mult.
  unfold um.
  reflexivity.
Qed.

Example mult_2 : mult zero (soma tres tres) = zero.
Proof.
  unfold mult.
  unfold zero.
  unfold soma.
  unfold tres.
  reflexivity.
Qed.

Example mult_3 : mult dois tres = soma tres tres.
Proof.
  unfold mult.
  unfold dois.
  unfold tres.
  unfold soma.
  reflexivity.
Qed.

(** Exercício 16: *)
Theorem mult_zero_dir: forall n, mult (ch n) zero = zero.
Proof.
  intro n.
  unfold mult.
  unfold zero.
  reflexivity.
Qed.

(** Exercício 17: *)
Theorem mult_zero_esq: forall n, mult zero (ch n) = zero.
Proof.
  intro n.
  induction n.
  - unfold zero.
    unfold mult.
    reflexivity.
  - rewrite <- IHn.
    unfold zero.
    unfold mult.
    simpl ch.
    unfold suc.
   (*  reflexivity. *)
Admitted.

(** Exercício 18: Defina a exponenciação de dois numerais. *)
Definition exp (n m : num) : num := 
  fun (X: Type) (f: X -> X) (x: X) => m (n f x).

(** Exercício 19: Prove os seguintes fatos: *)
Example exp_0 : exp um um = um.
Proof.
  Admitted.

Example exp_1 : exp dois dois = soma dois dois.
Proof.
  Admitted.

Example exp_2 : exp tres dois = soma (mult dois (mult dois dois)) um.
Proof.
  Admitted.

Example exp_3 : exp tres zero = um.
Proof.
  Admitted.