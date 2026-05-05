Require Import Stdlib.Structures.OrderedTypeEx.
Require Import Stdlib.Structures.OrdersAlt.
Require Import Stdlib.MSets.MSetWeakList.
Require Import Stdlib.MSets.MSetFacts.
Require Import Stdlib.MSets.MSetProperties.
Require Import Stdlib.MSets.MSetEqProperties.



(* VarSet represents sets of strings*)
Module StringOT := Update_OT String_as_OT.
Module VarSet := MSetWeakList.Make StringOT.
Module VarSetFacts := MSetFacts.Facts VarSet.
Module VarSetProps := MSetProperties.Properties VarSet.
Module VarSetDecide := MSetDecide.WDecide VarSet.
Module VarSetEqProps := MSetEqProperties.WEqProperties VarSet.

(*
VarSet API:
(* membership *)
VarSet.mem x s        (* returns bool *)

(* add/remove *)
VarSet.add x s
VarSet.remove x s

(* union *)
VarSet.union s1 s2

VarSet.equal s1 s2    (* returns bool *)

(* size *)
VarSet.cardinal s
 *)

Definition var_set := VarSet.t.
