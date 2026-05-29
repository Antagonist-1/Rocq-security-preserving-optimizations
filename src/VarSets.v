Require Import Stdlib.Structures.OrderedTypeEx.
Require Import Stdlib.Structures.OrdersAlt.
Require Import Stdlib.MSets.MSetWeakList.
Require Import Stdlib.MSets.MSetFacts.
Require Import Stdlib.MSets.MSetProperties.
Require Import Stdlib.MSets.MSetEqProperties.

(*  Liveness analysis needs to compute the cardinality of a set, and fixpoint iteration needs set equality. Fmap didn't provide that.
Hence, we chose to use MSetWeakLists for sets other than variable valuation, for its wide set of properties.
*)

(* VarSet represents sets of variables (=strings)*)
Module StringOT := Update_OT String_as_OT.
Module VarSet := MSetWeakList.Make StringOT.
Module VarSetFacts := MSetFacts.Facts VarSet.
Module VarSetProps := MSetProperties.Properties VarSet.
Module VarSetDecide := MSetDecide.WDecide VarSet.
Module VarSetEqProps := MSetEqProperties.WEqProperties VarSet.

Definition var_set := VarSet.t.
