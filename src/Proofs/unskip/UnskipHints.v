Require Import Language.Main.

Create HintDb unskip_db.
Hint Constructors eval eval_trace eval_sec : unskip_db.
Hint Constructors trace_subseq : unskip_db.
Hint Resolve eval_trace_prefix : unskip_db.
Hint Resolve trace_subseq_append_drop trace_subseq_append_keep: unskip_db.
Hint Resolve trace_subseq_refl match_ctx_refl: unskip_db.
Hint Resolve trace_subseq_trans match_ctx_trans: unskip_db.
Hint Resolve branch_contradiction: unskip_db.
Hint Unfold match_ctx : unskip_db.