signature polynomialCertificateLib =
sig
  (* The prime theorem is |- prime p, with p a numeral; the polynomial is
     a canonical ascending num list.  All candidate arithmetic is rechecked. *)
  (* Bounded addition/multiplication/list predicates only; no abstract inverses. *)
  val ARITH_CONV : Abbrev.conv
  (* Capture once for repeated bounded calculations in a certificate context. *)
  val BOUNDED_CONV : unit -> Abbrev.conv
  val REMAINDER_CONV : Thm.thm -> Term.term -> Abbrev.conv
  val MODPOW_CONV : Thm.thm -> Term.term -> Abbrev.conv
  val RABIN12_RULE : Thm.thm -> Term.term -> Thm.thm
  val NO_ROOTS_RULE : Thm.thm -> Term.term -> Thm.thm
end
