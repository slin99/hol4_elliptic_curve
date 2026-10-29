signature primeCertificateLib =
sig
  (* Decimal n, Lucas witness, and complete prime factorisation of n-1.
     The supplied data are untrusted and all equations are kernel checked. *)
  type certificate = string * string * (string * int) list
  val PRIME_CERT_CONV : certificate list -> Abbrev.conv
end
