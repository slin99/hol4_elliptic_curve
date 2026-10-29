signature idealCertificateLib =
sig
  include Abbrev

  (* IDEAL_RULE r [(f1,c1), ...] (l = u) checks the integer-polynomial
     identity l-u = SUM ci*(li-ui), where concl fi is li=ui.
     The result concludes l=u and retains the input theorem hypotheses and
     ring-carrier obligations as hypotheses. No characteristic or division
     assumptions are introduced. Polynomials use ringLib operations over r,
     variables, integer/natural literals, and natural-literal powers only.
     An empty certificate checks an unconditional polynomial identity.
     Malformed polynomials and incorrect certificates raise HOL_ERR. *)
  val IDEAL_RULE : term -> (thm * term) list -> term -> thm
end
