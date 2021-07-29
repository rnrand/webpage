Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VQC Require Import Complex.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From VQC Require Import Complex.
Import Check.

Goal True.

idtac "-------------------  Conj_mult_norm2  --------------------".
idtac " ".

idtac "#> Conj_mult_norm2".
idtac "Possible points: 1".
check_type @Conj_mult_norm2 ((forall c : C, c * c ^* = RtoC (Cnorm2 c))).
idtac "Assumptions:".
Abort.
Print Assumptions Conj_mult_norm2.
Goal True.
idtac " ".

idtac "-------------------  Csum_conj_distr  --------------------".
idtac " ".

idtac "#> Csum_conj_distr".
idtac "Possible points: 2".
check_type @Csum_conj_distr (
(forall (f : nat -> C) (n : nat),
 (Csum f n) ^* = Csum (fun x : nat => (f x) ^*) n)).
idtac "Assumptions:".
Abort.
Print Assumptions Csum_conj_distr.
Goal True.
idtac " ".

idtac "-------------------  Csum_unique  --------------------".
idtac " ".

idtac "#> Csum_unique".
idtac "Possible points: 3".
check_type @Csum_unique (
(forall (f : nat -> C) (k : C) (n x : nat),
 (x < n)%nat ->
 f x = k -> (forall x' : nat, x <> x' -> f x' = RtoC 0) -> Csum f n = k)).
idtac "Assumptions:".
Abort.
Print Assumptions Csum_unique.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 6".
idtac "Max points - advanced: 6".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- Conj_mult_norm2 ---------".
Print Assumptions Conj_mult_norm2.
idtac "---------- Csum_conj_distr ---------".
Print Assumptions Csum_conj_distr.
idtac "---------- Csum_unique ---------".
Print Assumptions Csum_unique.
idtac "".
idtac "********** Advanced **********".
Abort.

(* Thu Aug 1 22:26:43 EDT 2019 *)
