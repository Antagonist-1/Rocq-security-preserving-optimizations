Require Import Map.
Require Import Language.Syntax.
From Stdlib Require Import List.
Import ListNotations.

(** ** Semantics *)

(** Our first step is to give a meaning to these new constructs.  Let's start with
    an interpreter for binary operators: *)
Definition interp_binop (b: BinopName) (n1 n2: nat) :=
  match b with
  | LogAnd => Nat.land n1 n2
  | Eq => if (n1 =? n2) then 1 else 0
  | Plus => n1 + n2
  | Minus => n1 - n2
  | Times => n1 * n2
  | Divide => n1 / n2
  | ShiftLeft => Nat.shiftl n1 n2
  | ShiftRight => Nat.shiftr n1 n2
  | Modulo => Nat.modulo n1 n2
  end.

(** For expressions, we'll use an interpreter to implement the following rules::

                 n1 = n2
              ------------
               ⟦n2⟧ᵥ = n1
   
       (x ↦ a) ∈ v         x ∉ v
      --------------     ----------
         ⟦x⟧ᵥ = a         ⟦x⟧ᵥ = 0
   
               ⟦e1⟧ᵥ = a1
               ⟦e2⟧ᵥ = a2
         a = interp_binop b a1 a2
      -----------------------------
          ⟦Binop b e1 e2⟧ᵥ = a
*)
 
Inductive trace_event := 
| Branch: bool -> trace_event
| MemWrite: var -> trace_event.

Definition valuation := fmap var nat.

(*we dont put secrets in context because they are static, not changing with the program*)
Definition context := (valuation * list trace_event)%type.

Definition val_of (ctx: context) := fst ctx.
Definition trace_of (ctx: context) := snd ctx.

Notation "ev 't::' ctx" :=
  (val_of ctx, ev :: trace_of ctx)
  (at level 60).
Notation "ctx 't++' ev" :=
  (val_of ctx, trace_of ctx ++ (ev :: nil))
  (at level 60).
Notation "ctx 'v$+' ( k , v )" :=
  (val_of ctx $+ (k, v), trace_of ctx)
  (at level 50, left associativity).

Definition empty_context : context := ($0, nil).

Fixpoint interp_arith (e: expr) (v: valuation) {struct e}: nat :=
  match e with
  | Const n => n
  | Var x => match v $? x with Some a => a | None => 0 end
  | Binop b e1 e2 => interp_binop b (interp_arith e1 v) (interp_arith e2 v)
  end.

(** For commands, we'll use an inductive [Prop] to define big-step semantics.
    This is an opportunity to show that compiler proofs can work with a variety
    of semantics styles, since we focused on small-step semantics in lecture.
    The rules for [Assign], [While], [If], and [Skip] are the same as usual; for
    example:

                    ⟦e⟧ᵥ = a
      ----------------------------------- EvalAssign
       (v, Assign x e) ↓ᵩ (v $+ (x, a))
   
       (c1, v) ↓ᵩ v'   (c2, v') ↓ᵩ v''
      ----------------------------------- EvalSequence
          (v, Sequence c1 c2) ↓ᵩ v''

    Notice the subscript φ: this indicates that we have an function_env of functions.
    This function_env of functions gives the body of each function, the names of its
    arguments, and the name of its return value.  For example, to say that the
    function "collatz" has body [CollatzBody], takes arguments "start" and "flight",
    and writes its result to "out", we would write::

        phi = $0 $+ ("collatz", (("start", "flight"), "out", CollatzBody))

    and to say that function "factorial" has body [FactBody], takes argument "n",
    and writes its result to "f", we might write the following (every function takes
    two parameters, so we use "" as the name of the second argument of "factorial").

        phi = $0 $+ ("factorial", (("n", ""), "f", FactBody))

    We need an additional rule [EvalAssignCall] for function calls:

               (f ↦ ((x1, x2), y, body)) ∈ φ
                  ⟦e1⟧ᵥ = a1    ⟦e2⟧ᵥ = a2
          (body, ($0 $+ (x1, a1) $+ (x2, a2))) ↓ᵩ v'
                        (y ↦ a) ∈ v'
       ------------------------------------------------
         (AssignCall x f e1 e2, v) ↓ᵩ (v $+ (x, a))

   A few notes:
   
   - This rule passes arguments by value: that is, the function's arguments are
     evaluated in the current valuation [v]: [⟦e⟧ᵥ = a].
   
   - The function function_env [phi] (represented as φ above) maps function names
     (strings) to function signatures and function bodies:
     [(f ↦ ((x1, x2), y, body)) ∈ φ].
   
   - Functions return their output in variables indicated by their signatures:
     [(y ↦ a) ∈ v1].
   
   - Functions do not have access to the contexts of their callers: [body] runs
     in a clean environment.
   
   Here is how it looks in Rocq: *)

Inductive eval (phi: function_env): context -> cmd -> context -> Prop :=
  | EvalSkip: forall ctx,
      eval phi ctx Skip ctx
  | EvalAssign: forall ctx x e a,
      interp_arith e (val_of ctx) = a ->
      eval phi ctx (Assign x e) (ctx v$+ (x, a))
  | EvalAssignCall: forall x f e1 e2 x1 x2 y body a1 a2 a ctx ctx',
    phi $? f = Some ((x1, x2), y, body) ->
    interp_arith e1 (val_of ctx) = a1 ->
    interp_arith e2 (val_of ctx) = a2 ->
    (*reset the environmnet, but keep the trace. we could also simply append it after*)
    eval phi (($0 $+ (x1, a1) $+ (x2, a2)), trace_of ctx) body ctx' ->
    val_of ctx' $? y = Some a ->
    eval phi ctx (AssignCall x f e1 e2) (val_of ctx $+ (x, a), trace_of ctx')
  | EvalSequence: forall ctx c1 ctx1 c2 ctx2,
      eval phi ctx c1 ctx1 ->
      eval phi ctx1 c2 ctx2 ->
      eval phi ctx (Sequence c1 c2) ctx2
  | EvalIfTrue: forall ctx e thn els ctx' c,
      interp_arith e (val_of ctx) = c ->
      c <> 0 ->
      eval phi (ctx t++ Branch true) thn ctx' ->
      eval phi ctx (If e thn els) ctx'
  | EvalIfFalse: forall ctx e thn els ctx',
      interp_arith e (val_of ctx) = 0 ->
      eval phi (ctx t++ Branch false) els ctx' ->
      eval phi ctx (If e thn els) ctx'
  | EvalWhileTrue: forall ctx e body ctx' ctx'' c,
      interp_arith e (val_of ctx) = c ->
      c <> 0 ->
      eval phi (ctx t++ Branch true) body ctx' ->
      eval phi ctx' (While e body) ctx'' ->
      eval phi ctx (While e body) ctx''
  | EvalWhileFalse: forall ctx e body,
      interp_arith e (val_of ctx) = 0 ->
      eval phi ctx (While e body) (ctx t++ Branch false).
