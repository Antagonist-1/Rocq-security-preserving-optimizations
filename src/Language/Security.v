Require Import Map.
Require Import Language.Syntax.


(* Define security levels for variables as either Public or Secret *)
Inductive sec_level :=
| Public
| Secret.

(* A security environment maps variables to their security levels *)
Definition sec_env := fmap var sec_level.

(* 
   A simple OR operation for security levels, where Secret dominates Public.
  Usefull for joining sec_env; if one of the two environments has a variable marked as Secret,
  the joined environment should also mark it as Secret.
*)
Definition join_sec (s1 s2 : sec_level) : sec_level :=
  match s1, s2 with
  | Secret, _ | _, Secret => Secret
  | Public, Public => Public
  end.

(* 
   A function to look up the security level of a variable in the security environment,
  returning Public if the variable is not found 
*)
Definition sec_lookup (se : sec_env) (x : var) : sec_level :=
  match se $? x with
  | Some level => level
  | None => Public (* Default can be changed to Secret or Public *)
  end.

(* 
    Join two security environments, combining their mappings using the join_sec operation.
    If a variable is absent from both environments, it stays absent.
    If it is present in exactly one environment, we keep that label.
    If it is present in both environments, we join the labels with [join_sec].
 *)
Definition join_sec_env (se1 se2 : sec_env) : sec_env :=
  merge (fun level1 level2 =>
    match level1, level2 with
    | None, None => None
    | Some level, None => Some level
    | None, Some level => Some level
    | Some level1', Some level2' => Some (join_sec level1' level2')
    end) se1 se2.


Definition is_secret (se : sec_env) (x : var) : Prop :=
  sec_lookup se x = Secret.

(* Could prove keys equivalence betweeen sec_env fmap and val fmap *) 
