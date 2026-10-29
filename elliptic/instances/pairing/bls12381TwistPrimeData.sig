(* Interface to untrusted Lucas certificate data for the BLS12-381 twist
   cofactor. Consumers obtain proofs through primeCertificateLib, not by
   treating the certificates list as a primality verdict. *)

signature bls12381TwistPrimeData =
sig
  val certificates : primeCertificateLib.certificate list
end
