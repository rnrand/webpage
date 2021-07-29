(** * SQIMP: Quantum Programming in Coq **)

Require Export List.
Export ListNotations.
Require Import Bool.
Require Import Setoid.
Require Import Reals.
Require Import Psatz.
From VQC Require Import Matrix.
From VQC Require Import Qubit.
From VQC Require Import Multiqubit.

(** * A Small Quantum Imperative Language **)

Open Scope C_scope.
Open Scope matrix_scope.

(* ================================================================= *)
(** ** Unitaries as gates *)

Inductive Gate : nat -> Set := 
| G_H     : Gate 1 
| G_X     : Gate 1
| G_Z     : Gate 1
| G_CNOT  : Gate 2.

(** All of our programs will assume a fixed set of qubit registers.
    [app U [q1..qn]] will apply U to the registers q1 through qn. *)

Inductive com : Set :=
| skip : com
| seq  : com -> com -> com
| app  : forall {n}, Gate n -> list nat -> com.

Definition SKIP := skip.
Definition H' q := app G_H [q].
Definition X' q := app G_X [q].
Definition Z' q := app G_Z [q].
Definition CNOT' q1 q2 := app G_CNOT [q1; q2].  
Notation "p1 ; p2" := (seq p1 p2) (at level 50) : com_scope.

Arguments H' q%nat.
Arguments X' q%nat.
Arguments Z' q%nat.
Arguments CNOT' q1%nat q2%nat.

Open Scope com_scope.

(** A simple program to construct a bell state *)
Definition bell_com := H' 0; CNOT' 0 1. 

(** ** Denotation of Commands **)

(** Pad the given unitary with identities *)
Definition pad (n to dim : nat) (U : Unitary (2^n)) : Unitary (2^dim) :=
  if (to + n <=? dim)%nat then I (2^to) ⊗ U ⊗ I (2^(dim - n - to)) else Zero (2^dim) (2^dim).

Definition NOTC : Unitary 4 := fun i j => if (i + j =? 0) || (i + j =? 4) then 1 else 0.

Definition eval_cnot (dim m n: nat) : Unitary (2^dim) :=
  if (m + 1 =? n) then
    pad 2 m dim CNOT
  else if (n + 1 =? m) then
    pad 2 n dim NOTC
  else
    Zero _ _.

Definition g_eval {n} (dim : nat) (g : Gate n) (l : list nat) : Unitary (2^dim) :=
  match g, l with
  | G_H, [i]   => pad n i dim H
  | G_X, [i]   => pad n i dim X
  | G_Z, [i]   => pad n i dim Z
  | G_CNOT, i::[j] => eval_cnot dim i j
  | _, _     => Zero _ _
  end.

Fixpoint eval (dim : nat) (c : com) : Unitary (2^dim) :=
  match c with
  | skip    => I (2^dim)
  | app g l => g_eval dim g l
  | c1 ; c2  => eval dim c2 × eval dim c1 
  end.

Arguments eval_cnot /.
Arguments g_eval /.
Arguments pad /.

Lemma eval_bell : (eval 2 bell_com) × ∣0,0⟩ == bell.
Proof. 
  (* WORKED IN CLASS *)
  lma.
Qed.
  
(* ================================================================= *)
(** ** Relating Quantum Programs *)

Definition com_equiv (c1 c2 : com) := forall dim, eval dim c1 == eval dim c2.

Infix "≡" := com_equiv (at level 80): com_scope.

Lemma com_equiv_refl : forall c1, c1 ≡ c1. 
Proof. easy. Qed.

Lemma com_equiv_sym : forall c1 c2, c1 ≡ c2 -> c2 ≡ c1. 
Proof. easy. Qed.

Lemma com_equiv_trans : forall c1 c2 c3, c1 ≡ c2 -> c2 ≡ c3 -> c1 ≡ c3. 
Proof. 
  intros c1 c2 c3 H12 H23 dim. 
  unfold com_equiv in H12. 
  rewrite H12. easy. 
Qed.

Lemma seq_assoc : forall c1 c2 c3, ((c1 ; c2) ; c3) ≡ (c1 ; (c2 ; c3)).
Proof.
  intros c1 c2 c3 dim. simpl.
  rewrite Mmult_assoc. easy.
Qed.

Lemma seq_congruence : forall c1 c1' c2 c2',
    c1 ≡ c1' ->
    c2 ≡ c2' ->
    c1 ; c2 ≡ c1' ; c2'.
Proof.
  intros c1 c1' c2 c2' Ec1 Ec2 dim.
  simpl.
  unfold com_equiv in *.
  rewrite Ec1, Ec2.
  reflexivity.
Qed.

Add Relation com com_equiv 
  reflexivity proved by com_equiv_refl
  symmetry proved by com_equiv_sym
  transitivity proved by com_equiv_trans
  as com_equiv_rel.

Add Morphism seq 
  with signature (@com_equiv) ==> (@com_equiv) ==> (@com_equiv) as seq_mor.
Proof. intros x y H x0 y0 H0. apply seq_congruence; easy. Qed.

(** ** Superdense coding **)

Definition encode (b1 b2 : bool): com :=
  (if b2 then X' 0 else SKIP);
  (if b1 then Z' 0 else SKIP).

Definition decode : com :=
  CNOT' 0 1;
  H' 0.

Definition superdense (b1 b2 : bool) := bell_com ; encode b1 b2; decode.
  
Definition BtoN (b : bool) : nat := if b then 1 else 0.
Coercion BtoN : bool >-> nat.

Lemma superdense_correct : forall b1 b2, (eval 2 (superdense b1 b2)) × ∣ 0,0 ⟩ == ∣ b1,b2 ⟩.
Proof.
Admitted.






(* Thu Aug 1 13:45:52 EDT 2019 *)
