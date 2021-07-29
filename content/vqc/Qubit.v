(** * Qubit: The Building Blocks of Quantum Computing *)

From VQC Require Export Matrix.
Require Import FunctionalExtensionality.
Require Import Bool.

(** Amazingly, Coq doesn't have this in its standard library, despite
    having _5_ variations on the same. For now, we'll prove it
    ourselves. For good measure, we'll prove another version too. *)

Lemma pow2_sqrt : forall x:R, 0 <= x -> (√ x) ^ 2 = x.
Proof. intros; simpl; rewrite Rmult_1_r, sqrt_def; auto. Qed.

Lemma pow2_sqrt2 : (√ 2) ^ 2 = 2.
Proof. apply pow2_sqrt; lra. Qed.

Lemma pown_sqrt : forall (x : R) (n : nat), 
  0 <= x -> √ x ^ (S (S n)) = (x * √ x ^ n)%R.
Proof.
  intros. simpl. rewrite <- Rmult_assoc. rewrite sqrt_sqrt; auto.
Qed.  

Lemma sqrt_neq_0_compat : forall r : R, 0 < r -> (√ r)%R <> 0.
Proof. intros. specialize (sqrt_lt_R0 r). lra. Qed.

Lemma sqrt_inv : forall (r : R), 0 < r -> √ (/ r) = (/ √ r)%R.
Proof.
  intros.
  replace (/r)%R with (1/r)%R by lra.
  rewrite sqrt_div_alt, sqrt_1 by lra.
  lra.
Qed.  

Lemma sqrt2_inv : √ (/ 2) = (/ √ 2)%R.
Proof.
  apply sqrt_inv; lra.
Qed.  

Lemma Csqrt_inv : forall (r : R), 0 < r -> RtoC (√ (/ r)) = (/ √ r).
Proof.
  intros r H.
  apply c_proj_eq; simpl.
  field_simplify_eq [(pow2_sqrt r (or_introl H)) (sqrt_inv r H)].
  rewrite Rinv_r. reflexivity.
  apply sqrt_neq_0_compat; lra.
  apply sqrt_neq_0_compat; lra.
  field. apply sqrt_neq_0_compat; lra.
Qed.  

Lemma Csqrt2_inv : RtoC (√ (/ 2)) = (/ √ 2).
Proof. apply Csqrt_inv; lra. Qed.  

(* ################################################################# *)
(** * Qubits *)

(** Let's start with the basic building block of quantum computing :
    The qubit *)

Notation Qubit := (Vector 2).

Definition WF_Qubit (ϕ : Qubit) : Prop := ϕ† × ϕ == I 1.

(** Note that this is equivalent to saying that [⟨ϕ,ϕ⟩ = 1],
    which partially explains the notation for qubits below. *)

(** **** Exercise: 2 stars, standard, recommended (WF_Qubit_alt)  

    Prove this statement. *)
Theorem WF_Qubit_alt : forall ϕ : Qubit, WF_Qubit ϕ <-> ⟨ϕ, ϕ⟩ = 1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Definition qubit0 : Qubit := fun i j => if (i =? 0)%nat then 1 else 0.
Definition qubit1 : Qubit := fun i j => if (i =? 1)%nat then 1 else 0.

Notation "∣ 0 ⟩" := qubit0.
Notation "∣ 1 ⟩" := qubit1.

(** A brief aside : Emacs and other text editors, as well as a famous
    xkcd comic and any well-developed aethestics, don't like seeing
    left angle braces without corresponding right angle braces. (Blame
    here goes to Paul Dirac.) Since emacs' auto-indentation will
    probably go out of whack at this point in the file, I recommend
    disabling it via M-x electric-indent-mode. *) 

(** With that done, let's show that our two "basis" qubits are indeed
    proper qubits *)

Lemma WF_qubit0 : WF_Qubit ∣0⟩. Proof. lma. Qed.
Lemma WF_qubit1 : WF_Qubit ∣1⟩. Proof. lma. Qed.

Lemma qubit_decomposition : forall (ϕ : Qubit), exists (α β : C), ϕ == α .* ∣0⟩ .+ β .* ∣1⟩.
Proof.
  (* WORKED IN CLASS *)
  intros.
  exists (ϕ 0 0)%nat, (ϕ 1 0)%nat.
  lma.
Qed.
  
(* ################################################################# *)
(** * Unitaries *)

(** The standard way of operating on a vector is multiplying it by a
    matrix. If A is an n × n matrix and v is a n-dimensional vector,
    then A v is another n-dimensional vector.

    In the quantum case, we want to restrict A so that for any qubit
    ϕ, A ϕ is also a valid qubit. Let's try to figure out what this
    restriction will look like in practice.

 *)

Lemma valid_qubit_function : exists (P : Matrix 2 2 -> Prop),
  forall (A : Matrix 2 2) (ϕ : Qubit), 
  P A -> WF_Qubit ϕ -> WF_Qubit (A × ϕ).
Proof.
  (* WORKED IN CLASS *)
  eexists.
  intros A ϕ p Q.
  unfold WF_Qubit in *.
  unfold inner_product in *.
  rewrite Mmult_adjoint. 
  rewrite Mmult_assoc.
  rewrite <- (Mmult_assoc (A†)).
  instantiate (1 := fun A => A† × A = I 2) in p.
  simpl in p.
  rewrite p.
  rewrite Mmult_1_l.
  apply Q.
Qed.
  
(** We will call these matrices _unitary_ for preserving the unit
    inner product *)

Notation Unitary n := (Matrix n n).

Definition WF_Unitary {n} (U : Unitary n) := U † × U == I n. 
Transparent WF_Unitary.

(** We'll start with three useful unitaries: The identity (I), the
    Pauli X matrix (X) and the Hadamard matrix (H): *)

(**

      X = 01         
          10            
*)

Definition X : Unitary 2 := 
  fun i j => if i + j =? 1 then 1 else 0.

(** 

      H = 1/√2 * 1  1
                 1 -1

**)

Definition H : Unitary 2 :=
  fun i j => if i + j =? 2 then -/√2 else /√2.

(** 

      Z = 1 0
          0 -1 
*)

Definition Z : Unitary 2 := 
  fun i j => if i + j =? 0 then 1 else if i + j =? 2 then -1 else 0.

Lemma WF_I : WF_Unitary (I 2). Proof. lma. Qed.
Lemma WF_X : WF_Unitary X. Proof. lma. Qed.
Lemma WF_Z : WF_Unitary Z. Proof. lma. Qed.

Lemma WF_H : WF_Unitary H. 
Proof. 
  (* WORKED IN CLASS *)
  unfold WF_Unitary, Mmult, adjoint, H; simpl.
  by_cell; try lca.
  - apply c_proj_eq; simpl; try lra.
    field_simplify.
    repeat rewrite pown_sqrt; simpl; lra.
    apply sqrt_neq_0_compat; lra.
  - apply c_proj_eq; simpl; try lra.
    field_simplify.
    repeat rewrite pown_sqrt; simpl; lra.
    apply sqrt_neq_0_compat; lra.
Qed.
  
Definition q_plus : Qubit := (fun _ _ => /√2). 
Definition q_minus : Qubit := (fun i j => if i =? 0 then /√2 else -/√2).

Notation "∣ + ⟩" := q_plus.
Notation "∣ - ⟩" := q_minus.

(** It's worth noticing that if we apply a Hadamard twice, we get our
    initial state back: *)

Lemma Hplus : H × ∣+⟩ == ∣0⟩.
Proof.
  unfold H, Mmult, q_plus.
  by_cell; try lca.
  apply c_proj_eq; simpl; try lra.
  field_simplify.
  repeat rewrite pown_sqrt; simpl; lra.
  apply sqrt_neq_0_compat; lra.
Qed.

(** **** Exercise: 2 stars, standard, recommended (Htwice)  

    Prove the general form of double Hadamard application *)
Theorem Htwice : forall ϕ : Qubit, H × (H × ϕ) == ϕ.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Solving equations with square roots *)

(** We're doing more work than we would like to solve equations with
    square roots. Here are a few tactics that build on what we've done
    above to extend [field_simplify] and [field] to deal with
    roots. *)

Ltac nonzero :=
  repeat split;
  try match goal with
  | |- ?x <> RtoC 0  => apply RtoC_neq
  end;
  repeat match goal with 
  | |- √?x <> 0      => apply sqrt_neq_0_compat
  | |- (/?x)%R <> 0  => apply Rinv_neq_0_compat
  end; 
  match goal with 
  | |- _ <> _        => lra
  | |- _ < _        => lra
  end.

Ltac R_field_simplify := repeat field_simplify_eq [pow2_sqrt2 sqrt2_inv].
Ltac R_field := R_field_simplify; nonzero; trivial.
Ltac C_field_simplify := repeat field_simplify_eq [Csqrt2_square Csqrt2_inv].
Ltac C_field := C_field_simplify; nonzero; trivial.

(** * Measurement **)

(** Measurement is a _probabilistic_ operation on a qubit. Since
    there are (generally) multiple possible outcomes of a measurement,
    we will represent measurement as a relation. 

    Note that some measurements, those with 0 probability, will never occur.
*)

Inductive measure : Qubit -> (R * Qubit) -> Prop :=
| measure0 : forall (ϕ : Qubit), measure ϕ (Cnorm2 (ϕ 0%nat 0%nat), ∣0⟩)
| measure1 : forall (ϕ : Qubit), measure ϕ (Cnorm2 (ϕ 1%nat 0%nat), ∣1⟩). 

(** **** Exercise: 3 stars, standard, optional (measure_sum)  

    State and prove that the sum of the measure outcomes for a valid qubit will always be 1. 
    Hint: Compare the definitions of norm2 and inner_product. *)
(* FILL IN HERE *)

(** [] *)

Lemma measure0_idem : forall ϕ p, measure ∣0⟩ (p, ϕ) -> p <> 0 -> ϕ = ∣0⟩.
Proof.
  (* WORKED IN CLASS *)
  intros.
  inversion H0; subst.
  - reflexivity.
  - contradict H1. lra.
Qed.
  
(** **** Exercise: 1 star, standard, recommended (measure1_idem)  *)
Lemma measure1_idem : forall ϕ p, measure ∣1⟩ (p, ϕ) -> p <> 0 -> ϕ = ∣1⟩.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Lemma measure_plus : forall ϕ p, measure ∣+⟩ (p, ϕ) -> p = (1/2)%R.
Proof.
  intros.
  inversion H0; subst. 
  - R_field.
  - R_field.
(*
  - sqrt_solve.
  - sqrt_solve.
*)
Qed.

(** **** Exercise: 2 stars, standard, recommended (measure_minus)  *)
Lemma measure_minus : forall ϕ p, measure ∣-⟩ (p, ϕ) -> p = (1/2)%R.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* *)
(* Thu Aug 1 13:45:52 EDT 2019 *)
