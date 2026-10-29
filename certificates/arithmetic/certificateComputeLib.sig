signature certificateComputeLib =
sig
  (* Normalize natural arithmetic and comparisons with kernel CV arithmetic.
     Surrounding Boolean connectives are left unchanged. *)
  val NAT_CONV : Abbrev.conv

  (* Snapshot currently loaded equations and fast numeric callbacks.
     Create once per bounded-computation context. *)
  val EVAL_COMPSET : unit -> computeLib.compset
  val EVAL_CONV : unit -> Abbrev.conv

  (* Closed a ** e MOD n: one complete kernel CV program evaluation, without
     constructing a ** e.  Closed arithmetic in a, e and n is normalized first. *)
  val MODPOW_CONV : Abbrev.conv
end
