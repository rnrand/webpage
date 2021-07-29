Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From VQC Require Import Real.

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

From VQC Require Import Real.
Import Check.

Goal True.

idtac " ".

idtac "Max points - standard: 0".
idtac "Max points - advanced: 0".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "".
idtac "********** Advanced **********".
Abort.

(* Thu Aug 1 22:26:42 EDT 2019 *)
