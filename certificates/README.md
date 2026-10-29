# Certificate checking

These theories and Standard ML libraries turn proposed arithmetic data into
HOL proofs: recursive primality certificates, polynomial remainder and
irreducibility certificates, explicit ideal identities, and elliptic-curve
scalar and order certificates. They support the [named fields](../fields/README.md)
and the elliptic-curve developments without treating candidate computations
as axioms.

## Arithmetic

* [certificateCompute](arithmetic/certificateComputeScript.sml): proved
  computational equations. `certificate_cv_modpow_def`,
  `certificate_cv_modpow_eq` and `certificate_modpow_to_cv` connect natural
  modular powers with a binary kernel CV program. The identities do not
  require a prime modulus, including at modulus zero. `certificate_gf_add`
  and `certificate_gf_mult` expose numeric `GF` operations.
* [certificateComputeLib](arithmetic/certificateComputeLib.sml)
  ([signature](arithmetic/certificateComputeLib.sig)): `NAT_CONV` normalizes
  natural arithmetic and comparisons without changing surrounding Boolean
  structure. `EVAL_COMPSET ()` and `EVAL_CONV ()` snapshot loaded equations
  and numeric callbacks for repeated bounded computations. `MODPOW_CONV`
  proves the value of closed `a ** e MOD n` without constructing `a ** e`.

## Primes

* [primeCertificate](primes/primeCertificateScript.sml):
  `prime_certificate_check` derives `prime n` from `1 < n`, a complete prime
  factor list for `n-1`, a Lucas witness, and the modular tests for every
  listed factor. Multiplicities are repeated list entries.
* [primeCertificateLib](primes/primeCertificateLib.sml)
  ([signature](primes/primeCertificateLib.sig)): a `certificate` is
  `(decimal_n, decimal_witness, [(decimal_prime_factor, multiplicity), ...])`.
  `PRIME_CERT_CONV certificates` converts `prime <numeral>` to `T` with a
  kernel equality. Supply recursive certificates for the factors too;
  proofs for 2 and 3 are built in. Each constructed converter caches
  successful primality proofs. The data table in
  [namedPrimeFields](../fields/namedPrimeFieldsScript.sml) is a concrete client.

## Polynomials and quotient arithmetic

* [polynomialCertificate](polynomials/polynomialCertificateScript.sml):
  `polynomial_certificate_remainder` checks a quotient/remainder identity
  and degree bound. `polynomial_certificate_pow_even`,
  `polynomial_certificate_pow_odd` and
  `polynomial_certificate_frobenius_compose` support modular powers.
  `polynomial_certificate_bezout` and `polynomial_certificate_no_roots`
  exclude factors or roots. `polynomial_certificate_rabin12` proves
  degree-twelve irreducibility over a finite field, using Frobenius tests
  at degrees 4, 6 and 12 and checked Bezout identities.
* [polynomialCertificateLib](polynomials/polynomialCertificateLib.sml)
  ([signature](polynomials/polynomialCertificateLib.sig)): `ARITH_CONV`
  and `BOUNDED_CONV ()` handle bounded polynomial/list arithmetic.
  `REMAINDER_CONV prime f` proves remainders modulo `f`;
  `MODPOW_CONV prime f` handles remainders of polynomial powers with closed
  natural exponents. Here `prime` proves `prime p` with literal `p`, and `f`
  is a canonical monic polynomial of positive degree over `GF p`.
  `RABIN12_RULE prime f` returns an irreducibility theorem for a
  degree-twelve modulus; `NO_ROOTS_RULE prime f` returns an empty-root-set
  theorem when its Frobenius/Bezout certificate succeeds.
* [bn254Degree12Certificate](polynomials/bn254Degree12CertificateScript.sml):
  defines `bn254_fp12_poly`, representing `X^12 - 18*X^6 + 82`, and proves
  `bn254_fp12_poly_monic`, `bn254_fp12_poly_degree` and
  `bn254_fp12_irreducible`.
* [bls12381Degree12Certificate](polynomials/bls12381Degree12CertificateScript.sml):
  defines `bls12381_fp12_poly`, representing `X^12 - 2*X^6 + 2`, and proves
  `bls12381_fp12_poly_monic`, `bls12381_fp12_poly_degree` and
  `bls12381_fp12_irreducible`. Both named theories use `RABIN12_RULE` and
  feed the [degree-twelve field constructions](../fields/pairingDegree12FieldsScript.sml).
* [pairingFieldCertificateLib](polynomials/pairingFieldCertificateLib.sml)
  ([signature](polynomials/pairingFieldCertificateLib.sig)):
  `QUOTIENT_CONV prime modulus` evaluates zero, one, sums, products,
  remainders and natural powers in `PolyModRing (GF p) modulus` using
  checked polynomial identities. The modulus must be canonical, monic and
  of positive degree. Irreducibility is not required for these quotient-ring
  calculations; abstract quotient inverses are deliberately not evaluated.
* [idealCertificateLib](polynomials/idealCertificateLib.sml)
  ([signature](polynomials/idealCertificateLib.sig)):
  `IDEAL_RULE r [(f1,c1), ...] (l=u)` checks the supplied identity
  `l-u = SUM ci*(li-ui)`, where `fi` proves `li=ui`. It uses integer
  polynomials in `ringLib` syntax, not coefficient lists, and performs no
  ideal search. The result retains the input theorem hypotheses and
  ring-carrier obligations; division and opaque atoms are not accepted.

### Polynomial representation

Numeric polynomial interfaces use **ascending coefficients**:
`[a; b; c]` means `a + b*X + c*X^2`. Coefficients are residues in `GF p`,
canonical lists have no trailing zeros, and **`[]` is zero**, not `[0]`.
Quotient representatives must also satisfy the relevant degree bound.
`PolyModRing` remains the mathematical field/ring; the libraries do not
replace its operations with an unchecked list implementation. This list
convention does not describe `IDEAL_RULE`'s separate `ringLib` syntax.

## Elliptic certificates

* [ellipticCertificates](elliptic/ellipticCertificatesScript.sml):
  `sw_field_sum_inv_witness`, `sw_field_prod_inv_witness` and
  `sw_GF_prod_inv_witness` check proposed inverses.
  `sw_scalar_double` and `sw_scalar_double_add` support binary evaluation
  of the existing `sw_group` exponent. `sw_prime_generator_order`
  establishes exact prime order for a nonidentity curve point annihilated
  by that prime, with curve and membership hypotheses.
  `finite_field_cube_nonresidue` supplies a finite-field cubic obstruction.
* [ellipticCMCertificates](elliptic/ellipticCMCertificatesScript.sml):
  abstract finite-group results for order-three endomorphism certificates.
  `cm_order_three_automorphism` and `cm_order_three_eigenvalue` explain the
  action. `cm_independent`, `cm_independent_product_card` and
  `cm_independent_card_bound` establish independence, product size and an
  ambient size lower bound from exact order, divisibility and prime-order
  eigenvalue exclusions. Callers must prove the endomorphism and its
  third-iterate identity; these are not inferred from a curve's name.
* [ellipticCertificateLib](elliptic/ellipticCertificateLib.sml)
  ([signature](elliptic/ellipticCertificateLib.sig)):
  `BINARY_SCALAR_CONV` takes an addition conversion and matching curve and
  point-membership proofs. `SCALAR_CONV prime curve member` specializes to
  literal prime-field points (`ECAffine x y` or `ECInfinity`). The
  `BINARY_SCALAR_CERTIFICATE_TAC` and
  `BINARY_SCALAR_OPERATION_CERTIFICATE_TAC` interfaces expose bounded
  milestone or operation goals, checked by `BINARY_SCALAR_STEP_TAC`.
  `SCALAR_CERTIFICATE_TAC` and `SCALAR_STEP_TAC` are the prime-field forms.
  Input theorem hypotheses are retained.
* [pairingCurveCertificateLib](elliptic/pairingCurveCertificateLib.sml)
  ([signature](elliptic/pairingCurveCertificateLib.sig)): specializes
  `FIELD_CONV` and `SCALAR_CONV` to numeric quadratic
  `PolyModRing (GF p) [1;0;1]`, requiring closed prime and field proofs
  (plus curve and membership proofs for scalars). `SCALAR_CERTIFICATE_TAC`
  and `SCALAR_STEP_TAC` expose/check curve operations;
  `POWER_CERTIFICATE_TAC` and `POWER_STEP_TAC` do the same for field powers.
  Preparation is bounded to at most sixteen binary bits per invocation.
  This is not a general evaluator for arbitrary extension towers.

The signature comments specify theorem argument order and the explicit
subgoal branch layout for certificate tactics. These tactics produce proof
obligations: candidate preparation alone does not discharge them.

## Use and trust boundary

For theory results, add the theory name to a HOL script's `Ancestors` and
use its `...Theory` exports. For ML checking, load the corresponding library
through `Libs` and consult its linked signature. The named degree-twelve
certificate scripts are compact examples of `polynomialCertificateLib` use.

Factor tables, ML long division/Euclid results, proposed inverse values,
coordinates and scalar trajectories are **data, not proofs**. Successful
checkers construct kernel theorems by proving the required arithmetic
identities and applying the logical checker rules. Missing or incorrect data
cannot substitute for those proofs. Existing hypotheses on supplied theorems
remain obligations unless the interface requires closed certificates.

Exact order of one point is not the order of the whole curve, and
independence/cardinality bounds require all the hypotheses stated in their
theorems.
