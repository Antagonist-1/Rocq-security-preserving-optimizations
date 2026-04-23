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
  | None => Public
  end.

(* 
    A function to convert an optional security level to a security level, treating None as Public.
    This is useful for the join operation, where we want to treat missing variables as Public.
*)
Definition sec_of_option (level : option sec_level) : sec_level :=
  match level with
  | Some level' => level'
  | None => Public
  end.


(* 
    A function to join two security environments, combining their mappings using the join_sec operation.
    If a variable is marked as Secret in either environment, it will be marked as Secret in the joined environment.
    If a variable is not found in either environment, it will be treated as Public.
    if a variable is public in both environments, we don't store it in the joined environment, as sec_lookup will return Public by default for missing variables.
*)
Definition join_sec_env (se1 se2 : sec_env) : sec_env :=
  merge (fun level1 level2 =>
    match join_sec (sec_of_option level1) (sec_of_option level2) with
    | Public => None 
    | Secret => Some Secret
    end) se1 se2.


Definition is_secret (se : sec_env) (x : var) : Prop :=
  sec_lookup se x = Secret.

