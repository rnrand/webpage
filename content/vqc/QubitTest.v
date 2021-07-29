Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VQC Require Import Qubit.

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

From VQC Require Import Qubit.
Import Check.

Goal True.

idtac "-------------------  WF_Qubit_alt  --------------------".
idtac " ".

idtac "#> WF_Qubit_alt".
idtac "Possible points: 2".
check_type @WF_Qubit_alt ((forall ϕ : Qubit, WF_Qubit ϕ <-> ⟨ ϕ, ϕ ⟩ = RtoC 1)).
idtac "Assumptions:".
Abort.
Print Assumptions WF_Qubit_alt.
Goal True.
idtac " ".

idtac "-------------------  Htwice  --------------------".
idtac " ".

idtac "#> Htwice".
idtac "Possible points: 2".
check_type @Htwice ((forall ϕ : Qubit, H × (H × ϕ) == ϕ)).
idtac "Assumptions:".
Abort.
Print Assumptions Htwice.
Goal True.
idtac " ".

idtac "-------------------  measure1_idem  --------------------".
idtac " ".

idtac "#> measure1_idem".
idtac "Possible points: 1".
check_type @measure1_idem (
(forall (ϕ : Qubit) (p : R), measure ∣ 1 ⟩ (p, ϕ) -> p <> 0 -> ϕ = ∣ 1 ⟩)).
idtac "Assumptions:".
Abort.
Print Assumptions measure1_idem.
Goal True.
idtac " ".

idtac "-------------------  measure_minus  --------------------".
idtac " ".

idtac "#> measure_minus".
idtac "Possible points: 2".
check_type @measure_minus (
(forall (ϕ : Qubit) (p : R), measure ∣ - ⟩ (p, ϕ) -> p = (1 / 2)%R)).
idtac "Assumptions:".
Abort.
Print Assumptions measure_minus.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 7".
idtac "Max points - advanced: 7".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- WF_Qubit_alt ---------".
Print Assumptions WF_Qubit_alt.
idtac "---------- Htwice ---------".
Print Assumptions Htwice.
idtac "---------- measure1_idem ---------".
Print Assumptions measure1_idem.
idtac "---------- measure_minus ---------".
Print Assumptions measure_minus.
idtac "".
idtac "********** Advanced **********".
Abort.

(* Thu Aug 1 22:26:51 EDT 2019 *)
