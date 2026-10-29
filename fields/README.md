# Named and pairing fields

This layer gives named prime fields for secp256k1, P-256, BN254 and
BLS12-381, polynomial quotient extension fields for the two pairing families,
and explicit embeddings from their quadratic to degree-twelve fields. It uses
HOL's `GF`, `PolyRing` and `PolyModRing` constructions rather than introducing
an independent arithmetic representation.

## Theories

* [namedPrimeFields](namedPrimeFieldsScript.sml): defines each family's base
  modulus `*_p`, scalar modulus `*_n`, `*_base_field = GF *_p` and
  `*_scalar_field = GF *_n`. The prefixes are `secp256k1`, `p256`, `bn254`
  and `bls12381`. Public results include `secp256k1_p_prime`, `p256_n_prime`,
  `bn254_p_prime`, `bls12381_n_prime`, and the corresponding primality results
  for the other moduli. Each named field has `_field`, `_finite_field`,
  `_card` and `_char` theorems, for example
  `bn254_base_field_finite_field` and `bls12381_scalar_field_card`.
* [pairingQuadraticFields](pairingQuadraticFieldsScript.sml): constructs
  `bn254_fp2` and `bls12381_fp2` modulo `X^2 + 1`. The reusable theorem
  `prime_3mod4_quadratic_irreducible` requires `prime p /\ p MOD 4 = 3`.
  Named entry points include `bn254_fp2_irreducible`,
  `bls12381_fp2_finite_field`, and the matching `_card`, `_char`, `_carrier`,
  `_coefficients_above_one` and `_frobenius_square` results for both fields.
* [pairingDegree12Fields](pairingDegree12FieldsScript.sml): constructs
  `bn254_fp12` modulo `X^12 - 18*X^6 + 82` and `bls12381_fp12` modulo
  `X^12 - 2*X^6 + 2`. It uses the
  [BN254](../certificates/polynomials/bn254Degree12CertificateScript.sml) and
  [BLS12-381](../certificates/polynomials/bls12381Degree12CertificateScript.sml)
  irreducibility certificates. Start with `bn254_fp12_finite_field` or
  `bls12381_fp12_finite_field`; each field also has `_card`, `_char`,
  `_carrier`, `_coefficients_above_eleven`, `_poly_coefficients` and
  `_frobenius_twelfth` theorems.
* [pairingFieldEmbeddings](pairingFieldEmbeddingsScript.sml): defines
  `bn254_fp2_to_fp12` and `bls12381_fp2_to_fp12` by polynomial substitution
  followed by reduction. The generators `bn254_fp12_w` and `bls12381_fp12_w`
  are `X`; the images of the quadratic generator are `w^6 - 9` and `w^6 - 1`,
  respectively. The `_field_homo` and `_inj` theorems for each map prove
  operation preservation and injectivity on the carriers. The `_constant`
  and `_i` theorems describe constant and generator images, supported by
  `bn254_fp12_i_relation`, `bls12381_fp12_i_relation` and the corresponding
  `_fp2_modulus_vanishes` results.

## Representation and use

Prime-field elements are natural residues less than the modulus. Extension
field elements are **canonical polynomial lists in ascending coefficient
order**: `[a; b; c]` represents `a + b*X + c*X^2`. Coefficients are residues
in the base field, trailing zero coefficients are absent, and **`[]` is zero**;
`[0]` is not its canonical representation. In particular, the constant
inclusion is `if c = 0 then [] else [c]`, with `c < p`.

The `_carrier` theorems characterize representatives by `Poly (GF p) x` and
degree less than two or twelve. These are not pair/tower datatypes. Use the
field record operations, such as `bn254_fp2.prod.op`, rather than assuming
ordinary list operations implement the field. Frobenius theorems and the
embedding's injectivity are statements about carrier elements.

To use a theory in a HOL script, add its name to `Ancestors`; its exported
facts are available through the corresponding `...Theory` structure. For
example, `pairingFieldEmbeddings` supplies
`bn254_fp2_to_fp12_field_homo` and `bn254_fp2_to_fp12_inj`. The dependency
path is named primes, extension fields, then embeddings; certificate theories
supply the arithmetic and irreducibility prerequisites.

## Certificates and scope

The large Lucas tables in `namedPrimeFieldsScript.sml` are untrusted data.
[primeCertificateLib](../certificates/primes/primeCertificateLib.sig) checks
subsidiary primes, factorisations and modular equations. Degree-twelve
irreducibility uses
[polynomialCertificateLib](../certificates/polynomials/polynomialCertificateLib.sig),
which checks proposed remainder and Bezout identities before applying the HOL
criterion. See the [certificate layer](../certificates/README.md) for checker
interfaces and the trust boundary.

Primality of a named scalar modulus alone is not a curve-order theorem,
and field embeddings alone do not define or prove properties of a pairing.
