Require Import Map.
Require Import VarSets.
Require Import Language.Syntax.
Require Import Language.Security.
From Stdlib Require Import List.
Import ListNotations.

Definition valuation := fmap var nat.

Inductive trace_event :=
| Branch: bool -> trace_event
| MemWrite: var -> trace_event.

(*
  We define two different context, one for standard execution (with valuation and trace) 
  and one that also carries secrets, used to check if a program is secure
 *)
Definition context := (valuation * list trace_event)%type.
Definition sec_context := (valuation * sec_env * list trace_event)%type.

(* Getters for contexts *)
Definition val_of (ctx: context) := fst ctx.
Definition trace_of (ctx: context) := snd ctx.

(* Getters for sec_context *)
Definition sec_val_of (ctx : sec_context) := fst (fst ctx).
Definition sec_of (ctx : sec_context) := snd (fst ctx).
Definition sec_trace_of (ctx : sec_context) := snd ctx.


(* Some custom notations to make writing contexts more convenient.  For example, we can write
   [($0, nil) t++ Branch true]
   instead of
   [($0, nil), trace_of ($0, nil) ++ (Branch true :: nil)].
*)


(* Prepending an event to the trace *)
Notation "ev 't::' ctx" :=
  (val_of ctx, ev :: trace_of ctx)
  (at level 60).

(* Appending an event to the trace *)
Notation "ctx 't++' ev" :=
  (val_of ctx, trace_of ctx ++ (ev :: nil))
  (at level 60).

(* Updating the valuation in the context *)
Notation "ctx 'v$+' ( k , v )" :=
  (val_of ctx $+ (k, v), trace_of ctx)
  (at level 50, left associativity).

(* Updating the valuation in a security context *)
Notation "ctx 'sv$+' ( k , v )" :=
  (sec_val_of ctx $+ (k, v), sec_of ctx, sec_trace_of ctx)
  (at level 50, left associativity).

(* Updating the security environment in a security context *)
Notation "ctx 's$+' ( k , level )" :=
  (sec_val_of ctx, update_sec (sec_of ctx) k level, sec_trace_of ctx)
  (at level 50, left associativity).

(* Appending an event to the trace in a security context *)
Notation "ctx 'st++' ev" :=
  (sec_val_of ctx, sec_of ctx, sec_trace_of ctx ++ (ev :: nil))
  (at level 60).

(* Define empty contexts to make writing examples easier *)
Definition empty_context : context := ($0, nil).
Definition empty_sec_context : sec_context := ($0, VarSet.empty, nil).


(* [trace_subseq src opt] means [opt] is a subsequence of [src]. *)
Inductive trace_subseq {A : Type} : list A -> list A -> Prop :=
  | SubseqNil : 
      trace_subseq [] []
  | SubseqKeep : forall x src opt,
      trace_subseq src opt ->
      trace_subseq (x :: src) (x :: opt)
  | SubseqDrop : forall x src opt,
      trace_subseq src opt ->
      trace_subseq (x :: src) opt.

(* An optimized context matches a source context if their valuations are
perfectly equal, and the optimized trace is a subsequence of the source trace *)
Definition match_ctx (ctx_src ctx_opt : context) : Prop :=
  val_of ctx_src = val_of ctx_opt /\
  trace_subseq (trace_of ctx_src) (trace_of ctx_opt).

(* The security environment and valuation must match exactly, but the security
trace can drop branches. *)
Definition match_sec_ctx (sctx_src sctx_opt : sec_context) : Prop :=
  sec_val_of sctx_src = sec_val_of sctx_opt /\
  sec_of sctx_src = sec_of sctx_opt /\
  trace_subseq (sec_trace_of sctx_src) (sec_trace_of sctx_opt).


Create HintDb trace_subseq_db.
Hint Constructors trace_subseq : trace_subseq_db.
(* If opt is a subseq of src, we can append an event to src and drop it. *)
Lemma trace_subseq_append_drop : forall A (src opt : list A) (x : A),
  trace_subseq src opt ->
  trace_subseq (src ++ [x]) opt.
Proof.
  intros A src opt x Hsubseq.
  induction Hsubseq; eauto with trace_subseq_db.
Qed.

(* If opt is subseq of src, we can safely append the same event to both *)
Lemma trace_subseq_append_keep : forall A (src opt : list A) (x : A),
  trace_subseq src opt ->
  trace_subseq (src ++ [x]) (opt ++ [x]).
Proof.
  intros A src opt x Hsubseq.
  induction Hsubseq; eauto with trace_subseq_db.
Qed.

Lemma trace_subseq_refl : forall A (l : list A),
  trace_subseq l l.
Proof.
  induction l; constructor; auto.
Qed.