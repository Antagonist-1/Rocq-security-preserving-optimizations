(** * CS-428: Interactive Theorem Proving, Spring 2026 - Lab 6
    Adapted from 6.822 Formal Reasoning About Programs, Spring 2022 *)

From Stdlib Require Export NArith Arith.
From Stdlib Require Export Program.Equality.
Require Import Map.
From Stdlib Require Import String.

Arguments N.add : simpl nomatch.
Arguments N.sub : simpl nomatch.
Arguments N.mul : simpl nomatch.
Arguments N.div : simpl nomatch.
Arguments N.shiftl : simpl nomatch.
Arguments N.shiftr : simpl nomatch.

Declare Scope var_scope.

Notation var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.
Infix "==v" := var_eq (no associativity, at level 50).
String Notation var string_of_list_byte list_byte_of_string: var_scope.

Open Scope var_scope.

(** ** Language definition *)

(** We'll start with a variant of an usual imperative language, with a few
    twists: first, we'll generalize the [Plus] constructor, allowing a number of
    binary operators.  Second, we'll add function calls (for simplicity, all
    functions take two arguments, and they assign their results to variables). *)

Inductive BinopName :=
| LogAnd 
| Eq 
| ShiftLeft 
| ShiftRight 
| Times 
| Divide 
| Plus 
| Minus 
| Modulo.

Inductive expr :=
| Const : nat -> expr
| Var : var -> expr
| Binop : BinopName -> expr -> expr -> expr.

Inductive cmd :=
| Skip : cmd
| Assign : var -> expr -> cmd
| AssignCall : var -> var -> expr -> expr -> cmd
| Sequence : cmd -> cmd -> cmd
| If : expr -> cmd -> cmd -> cmd
| While : expr -> cmd -> cmd.

Declare Scope expr.
Delimit Scope expr with expr.

Coercion Const : nat >-> expr.
Coercion Var : var >-> expr.

(** The coercions defined in the previous section make programs easier to write by
    allowing to write [x] for [Var x] and [n] for [Const n], but they can be
    confusing when reading programs or proving properties, so the following line
    turns them off: *)

Set Printing Coercions.

Infix "&" := (Binop LogAnd) (at level 80) : expr.
Infix "==" := (Binop Eq) (at level 70) : expr.
Infix ">>" := (Binop ShiftRight) (at level 60) : expr.
Infix "<<" := (Binop ShiftLeft) (at level 60) : expr.
Infix "+" := (Binop Plus) (at level 50, left associativity) : expr.
Infix "-" := (Binop Minus) (at level 50, left associativity) : expr.
Infix "*" := (Binop Times) (at level 40, left associativity) : expr.
Infix "/" := (Binop Divide) (at level 40, left associativity) : expr.
Infix "mod" := (Binop Modulo) (at level 40) : expr.

Notation "x <- e" :=
  (Assign x e%expr)
    (at level 75).
Notation "x <- 'call1' f e1" :=
  (AssignCall x f e1%expr (Const 0))
    (at level 75, f at level 0, e1 at level 0).
Notation "x <- 'call2' f e1 e2" :=
  (AssignCall x f e1%expr e2%expr)
    (at level 75, f at level 0, e1 at level 0, e2 at level 0).
Infix ";;" :=
  Sequence (at level 76).
Notation "'when' e 'then' then_ 'else' else_ 'done'" :=
  (If e%expr then_ else_)
    (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" :=
  (While e%expr body)
    (at level 75).

Example Times3Plus1Body :=
  ("n" <- "n" * 3 + 1).

Example FactBody :=
  ("f" <- 1;;
    while "n" loop
      "f" <- "f" * "n";;
      "n" <- "n" - 1
    done).

Example FactRecBody :=
  (when "n" == 1 then
      "f" <- 1
    else
      "f" <- call1 "fact_r" ("n" - 1);;
      "f" <- "f" * "n"
    done).

Example FactTailRecBody :=
  (when "n" == 1 then
      "f" <- "acc"
    else
      "f" <- call2 "fact_tr" ("n" - 1) ("acc" * "n")
    done).

Example CollatzBody :=
  (when ("start" == 1) then
      Skip
    else when ("start" mod 2 == 0) then
          "start" <- "start" / 2
        else
          (* `call1 f arg` is short for `call2 f arg 0` *)
          "start" <- call1 "times3plus1" ("start" + 0)
        done;;
        "flight" <- call2 "collatz" "start" ("flight" + 1)
    done).

Notation TimesThreePlus1_signature := (("n", ""), "n", Times3Plus1Body).
Notation Fact_signature := (("n", ""), "f", FactBody).
Notation FactRec_signature := (("n", ""), "f", FactRecBody).
Notation FactTailRec_signature := (("n", "acc"), "f", FactTailRecBody).
Notation Collatz_signature := (("start", "flight"), "flight", CollatzBody).

Notation Collatz_env :=
($0
  $+ ("collatz", Collatz_signature)
  $+ ("times3plus1", TimesThreePlus1_signature)).

Notation Fact_env :=
  ($0
    $+ ("fact", Fact_signature)
    $+ ("fact_r", FactRec_signature)
    $+ ("fact_tr", FactTailRec_signature)).

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

Definition secrets := fmap var unit. (*store secrets in a set*)
Definition is_secret (s: secrets) (x: var) := s $? x = Some tt.

(*2 programs agree on public variables, with potentially different secrets
necessary to check*)
Definition agree_on_public (s: secrets) (v1 v2 : valuation) : Prop :=
  forall x, not (is_secret s x) -> v1 $? x = v2 $? x.

(*we dont put secrets in context because they are static, not changing with the program*)
Record context := {
    val: valuation;
    trace: list trace_event
}.
Print cons.

Definition empty_context : context := {| val := $0; trace := nil |}.

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

Definition function_env := fmap string ((var * var) * var * cmd).


Inductive eval (phi: function_env): context -> cmd -> context -> Prop :=
  | EvalSkip: forall ctx,
      eval phi ctx Skip ctx
  | EvalAssign: forall ctx x e a,
      interp_arith e ctx.(val) = a ->
      eval phi ctx (Assign x e) {|val := (ctx.(val) $+ (x, a)); trace := ctx.(trace)|}
  | EvalAssignCall: forall x f e1 e2 x1 x2 y body a1 a2 a ctx ctx',
    phi $? f = Some ((x1, x2), y, body) ->
    interp_arith e1 ctx.(val) = a1 ->
    interp_arith e2 ctx.(val) = a2 ->
    (*reset the environmnet, but keep the trace. we could also simply append it after*)
    eval phi {|val:=($0 $+ (x1, a1) $+ (x2, a2)); trace:=ctx.(trace)|} body ctx' ->
    ctx'.(val) $? y = Some a ->
    eval phi ctx (AssignCall x f e1 e2) {|val:=(ctx.(val) $+ (x, a)); trace:=ctx'.(trace)|}
  | EvalSequence: forall ctx c1 ctx1 c2 ctx2,
      eval phi ctx c1 ctx1 ->
      eval phi ctx1 c2 ctx2 ->
      eval phi ctx (Sequence c1 c2) ctx2
  | EvalIfTrue: forall ctx e thn els ctx' c,
      interp_arith e ctx.(val) = c ->
      c <> 0 ->
      eval phi ctx thn ctx' ->
      eval phi ctx (If e thn els) {|val := ctx'.(val); trace:=(cons (Branch true) ctx'.(trace))|}
  | EvalIfFalse: forall ctx e thn els ctx',
      interp_arith e ctx.(val) = 0 ->
      eval phi ctx els ctx' ->
      eval phi ctx (If e thn els) {|val:=ctx'.(val); trace:=(cons (Branch false) ctx'.(trace))|}
  | EvalWhileTrue: forall ctx e body ctx' ctx'' c,
      interp_arith e ctx.(val) = c ->
      c <> 0 ->
      eval phi ctx body ctx' ->
      eval phi ctx' (While e body) ctx'' ->
      eval phi ctx (While e body) {|val := ctx''.(val); trace:=(cons (Branch true) ctx''.(trace))|}
  | EvalWhileFalse: forall ctx e body,
      interp_arith e ctx.(val) = 0 ->
      eval phi ctx (While e body) {|val := ctx.(val); trace:=(cons (Branch false) ctx.(trace))|}.
