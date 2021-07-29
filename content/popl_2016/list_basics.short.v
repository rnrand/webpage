(* ###################################################################### *)
(** * Proofs and Programs *)

(** (We use [admit] and [Admitted] to hide solutions from exercises.) *)

Axiom admit : forall {T}, T.

(** [Inductive] is Coq's way of defining an algebraic datatype.  Its
    syntax is similar to OCaml's ([type]) or Haskell's ([data]). Here,
    we define [bool] as a simple algebraic datatype. *)

Module Bool.

Inductive bool : Type :=
| true : bool
| false : bool.

(** **** Exercise: 1 star (trivalue)  *)
(** Define a three-valued data type, representing ternary logic.  Here
    something can be true, false and unknown. *)

Inductive trivalue : Type :=
(* FILL IN HERE *)
.
(** [] *)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition orb (b1 b2: bool) : bool :=
(* WORK IN CLASS *)

Print orb.

(** We can also use an [if] statement, which matches on the first
    constructor of any two-constructor datatype, in our definition. *)

Definition andb (b1 b2: bool) : bool :=
(* WORK IN CLASS *)

(** Let's test our functions. The [Compute] command tells Coq to
    evaluate an expression and print the result on the screen.*)

Compute (negb true).
Compute (orb true false).
Compute (andb true false).

(** **** Exercise: 1 star (xor)  *)
(** Define xor (exclusive or). *)

Definition xorb (b1 b2 : bool) : bool :=
(* FILL IN HERE *) admit.

Compute (xorb true true).
(** [] *)


(** New tactics
    -----------

    - [intros]: Introduce variables into the context, giving them
      names.

    - [simpl]: Simplify the goal.

    - [reflexivity]: Prove that some expression [x] is equal to itself. *)

Example andb_false_l : forall b, andb false b = false.
Proof.
(* WORK IN CLASS *) Admitted.


(** **** Exercise: 1 star (orb_true_l)  *)
Theorem orb_true_l :
  forall b, orb true b = true.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** New tactic
    ----------

    - [destruct]: Consider all possible constructors of an inductive
      data type, generating subgoals that need to be solved
      separately. *)


(*  FULL: Here's an example of [destruct] in action. *)

Lemma orb_true_r : forall b : bool, orb b true = true.
(* Here we explicitly annotate b with its type, even though Coq could infer it. *)
Proof.
(* WORK IN CLASS *) Admitted.

(** We can call [destruct] as many times as we want, generating deeper subgoals. *)

Theorem andb_commutative : forall b1 b2 : bool, andb b1 b2 = andb b2 b1.
Proof.
(* WORK IN CLASS *) Admitted.

(** **** Exercise: 1 star (andb_false_r)  *)
(** Show that b AND false is always false  *)

Theorem andb_false_r :
(* FILL IN HERE *) admit.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (xorb_b_neg_b)  *)
(** Show that b xor (not b) is always true. *)

Theorem xorb_b_neg_b :
(* FILL IN HERE *) admit.
Proof.
(* FILL IN HERE *) Admitted.

Theorem rewrite_example : forall b1 b2 b3 b4,
  b1 = b4 ->
  b2 = b3 ->
  andb b1 b2 = andb b3 b4.

Proof.

(** New tactics
    -----------

    - [rewrite]: Replace one side of an equation by the other.

    - [apply]: Suppose that the current goal is [Q]. If [H : Q], then
      [apply H] solves the goal. If [H : P -> Q], then [apply H]
      replaces [Q] by [P] in the goal. If [H] has multiple hypotheses,
      [H : P1 -> P2 -> ... -> Pn -> Q], then [apply H] generates one
      subgoal for each [Pi]. *)

(* WORK IN CLASS *)
Qed.


(** **** Exercise: 1 star (xorb_same)  *)
(** Show that if [b1 = b2] then b1 xor b2 is false. *)

Theorem xorb_same :
(* FILL IN HERE *) admit.
Proof.
(* FILL IN HERE *) Admitted.

End Bool.


(* ###################################################################### *)

(** We will use the following option to make polymorphism more
    convenient. *)

Set Implicit Arguments.

(** * Lists *)

Module List.

Inductive list (T : Type) :=
| nil : list T
| cons : T -> list T -> list T.

Fixpoint app T (l1 l2 : list T) : list T :=
(* WORK IN CLASS *)

Notation "h :: t" := (cons h t) (at level 60, right associativity).
Notation "[ ]" := (nil _).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y [] ) ..).
Notation "l1 ++ l2" := (app l1 l2) (at level 60, right associativity).

(** Since [nil] can potentially be of any type, we add an underscore
    to tell Coq to infer the type from the context. *)

Check [].
Check true :: [].
Check [true ; false].
Check [true ; false] ++ [false].

Compute [true ; false] ++ [false].

Reserved Notation "l1 @ l2" (at level 60).
Fixpoint app' T (l1 l2 : list T) : list T :=
  match l1 with
  | [] => l2
  | h :: t  => h :: (t @ l2)
  end

  where "l1 @ l2" := (app' l1 l2).


(** **** Exercise: 1 star (snoc)  *)
(** Define [snoc], which adds an element to the end of a list. *)

Fixpoint snoc T (l : list T) (x : T) : list T :=
(* FILL IN HERE *) admit.

Lemma app_nil_l: forall T (l : list T), [] ++ l  = l.
Proof.
(* WORK IN CLASS *) Admitted.

Lemma app_nil_r: forall T (l : list T), l ++ []  = l.
Proof.

(** New tactic
    ----------

    - [induction]: Argue by induction. It works as [destruct], but
    additionally giving us an inductive hypothesis in the inductive
    case. *)
(* WORK IN CLASS *)

Lemma app_assoc :
  forall T (l1 l2 l3 : list T),
    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
(* WORK IN CLASS *) Admitted.

(** **** Exercise: 2 stars (snoc_app)  *)
(** Prove that [snoc l x] is equivalent to appending [x] to the end of
    [l]. *)

Lemma snoc_app : forall T (l : list T) (x : T), snoc l x = l ++ [x].
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** The natural numbers are defined in Coq's standard library as follows:

    Inductive nat : Type :=
      | O : nat
      | S : nat -> nat.

    where [S] stands for "Successor".

    Coq prints [S (S (S O))] as "3", as you might expect.

*)

Set Printing All.

Check 0.
Check 2.
Check 2 + 2.

Unset Printing All.

Check S (S (S O)).
Check 2 + 3.
Compute 2 + 3.

Fixpoint length T (l : list T) :=
(* WORK IN CLASS *)

Compute length [1; 1; 1].

(** **** Exercise: 3 stars (app_length)  *)

Lemma app_length : forall T (l1 l2 : list T),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
(* FILL IN HERE *) Admitted.

(** New Tactic
    ----------

    - [discriminate]: Looks for an equation between terms starting
      with different constructors, and solves the current goal. *)

Lemma app_eq_nil_l : forall T (l1 l2 : list T),
  l1 ++ l2 = [] -> l1 = [].
Proof.
(* WORK IN CLASS *) Admitted.

(** **** Exercise: 2 stars (app_eq_nil_r)  *)
(** Prove the same about [l2]. *)

Lemma plus_nil_r : forall T (l1 l2 : list T),
  l1 ++ l2 = [] -> l2 = [].
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

Fail Fixpoint shuffle T (l1 l2 : list T) :=
  match l1 with
  | [] => l2
  | h :: t => h :: shuffle l2 t
  end.

Print shuffle.


Fixpoint rev T (l : list T) :=
(* WORK IN CLASS *)

Lemma rev_app : forall T (l1 l2 : list T), rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
(* WORK IN CLASS *) Admitted.

(** **** Exercise: 2 stars (rev_app)  *)
(** Using [rev_app], prove that reversing a list twice results in the
    same list. *)

Lemma rev_involutive : forall T (l : list T), rev (rev l) = l.
Proof.
(* FILL IN HERE *) Admitted.

Fixpoint tr_rev_aux T (l acc : list T) : list T :=
  match l with
  | [] => acc
  | x :: l => tr_rev_aux l (x :: acc)
  end.

Definition tr_rev T (l: list T) := tr_rev_aux l [].


(** New Tactic
    ----------

    - [unfold]: Calling [unfold foo] expands the definition of [foo]
      in the goal.
*)

Lemma tr_rev_eq_rev :
  forall T (l : list T),
    tr_rev l = rev l.
Proof.
(* WORK IN CLASS *) Admitted.

End List.


(** You may have noticed that several of the proofs in this section,
    particularly regarding the associativity of the append function,
    closely resemble proofs about arithmetic. You might also be interested
    in Coq for its ability to prove results in mathematics. The
    material in this section should be sufficient for you to start
    formulating theorems about the natural numbers, such as the
    commutativity, associativity and distributivity of addition and
    multiplication.

    As noted above, the natural numbers are defined as follows:

    Inductive nat : Type :=
      | O : nat
      | S : nat -> nat.

    From there you can define +, -, *, /, ^ etc. We encourage you to
    start on your own, but to help we've included a module on arithmetic
    We hope you enjoy.

*)
