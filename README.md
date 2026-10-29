# HOL4 Algebra

Finite fields and short-Weierstrass elliptic curves for secp256k1, P-256,
BN254 and BLS12-381, built on HOL4's modern group, ring, field and polynomial
libraries. The development provides mathematical specifications and proofs;
it does not implement optimized arithmetic, serialization, precompiles or
pairing evaluation.

## Build

Install [holbuild](https://github.com/charles-cooper/holbuild) version 0.11.3 or newer
and Poly/ML. Run commands from this directory:

```sh
# Resolve the pinned HOL checkout and algebra dependencies.
holbuild context

# Build the default roots and their dependencies.
holbuild

# Build a single theory, including its dependencies.
holbuild shortWeierstrassTheory

# Build the worked example over GF 5.
holbuild shortWeierstrassSmallTheory
```

[holproject.toml](holproject.toml) pins HOL to
`652d1f0aad5cd537ed1e5d470ba3444e70ba470e` and selects the default roots.
[holexamples.manifest.toml](holexamples.manifest.toml) selects algebra example
sources from that same checkout; it is not a second version of HOL.
Build products and dependency state live under `.holbuild/`.
The first build may need to fetch and build the pinned toolchain and its
upstream algebra theories. Concrete scalar and polynomial certificates can
be substantially more expensive than the small example.

[Holmakefile](Holmakefile) also lists theory targets and upstream include
paths for a configured HOL installation. The commands above use holbuild's
pinned project context; they do not require an independently selected
`HOLDIR`.

## Library map

The organization follows HOL's algebra library convention: a theory map in
each library README and a documentation block beside each theory's source.
The source statements are authoritative for hypotheses and rewrite attributes.

- **[Fields](fields/README.md)** — named base/scalar prime fields, quadratic
  and degree-12 polynomial quotient fields, and inclusions between them.
- **[Groups](groups/README.md)** — the short-Weierstrass Abelian-group theorem,
  scalar multiplication, rational torsion, generated subgroups and cofactors.
- **[Elliptic curves](elliptic/README.md)** — affine and homogeneous
  representations, elementary cardinality arguments, field-map transport,
  coordinate scaling and cube-root endomorphisms.
- **[Concrete instances](elliptic/instances/README.md)** — curve parameters,
  generator orders, prime-order subgroups, full cardinalities and twist maps.
- **[Certificates](certificates/README.md)** — reusable arithmetic,
  primality, polynomial and elliptic certificate proof infrastructure.

Start with
[`shortWeierstrassScript.sml`](elliptic/core/shortWeierstrassScript.sml) for the
point type and curve predicate, then
[`shortWeierstrassGroupScript.sml`](groups/shortWeierstrassGroupScript.sml) for
the group law. The compact worked development
[`shortWeierstrassSmallScript.sml`](elliptic/core/shortWeierstrassSmallScript.sml)
enumerates a six-point curve over `GF 5`, proves its generator order and torsion
facts, and transports it to an isomorphic field.

## Using the mathematical interface

For a theory using scalar multiplication and torsion, import the existing
curve theories in its ancestry:

```sml
Theory myCurveFacts
Ancestors
  shortWeierstrass shortWeierstrassGroup ellipticTorsion
```

The main interface is:

| Expression / theorem | Meaning |
| --- | --- |
| `ShortWeierstrassCurve r a b` | A field, coefficients in its carrier, characteristic other than 2 or 3, and nonzero discriminant. |
| `sw_points r a b` | `ECInfinity` and affine carrier coordinates satisfying `y^2 = x^3 + a*x + b`. |
| `sw_group r a b` | Group record with identity `ECInfinity` and operation `sw_add r a b`. |
| `short_weierstrass_abelian_group` | The curve predicate implies `AbelianGroup (sw_group r a b)`. |
| `(sw_group r a b).exp P n` | Natural-number scalar multiplication `[n]P`. |
| `order (sw_group r a b) P` | Point order; HOL uses `0` for infinite order. |
| `sw_torsion_group r a b n` | Rational curve points annihilated by multiplication by `n`. |
| `Generated (sw_group r a b) P` | The existing group library's structure of natural-number multiples of `P`; the finite-field subgroup results are in `ellipticTorsion`. |

Record definitions and point constructors are total. Group laws do not apply
to arbitrary `ECAffine` values: retain the curve and carrier-membership
hypotheses of the theorem being used.

## Representations and proof boundaries

- Prime fields use the existing `GF p` model. Extension fields use
  `PolyModRing`, with **ascending** coefficient lists and canonical zero `[]`.
  `[a;b]` means `a + b*X`; `[0]` is not the canonical zero polynomial.
- Homogeneous triples represent `(X/Z,Y/Z)`, not Jacobian coordinates.
  The total projective decoder is not a representation-validity check.
- A full curve group, its rational `n`-torsion and a named generated subgroup
  are different objects. A generator of a prime-order subgroup need not
  generate the entire curve. Full cofactors are not effective
  hash-to-curve cofactors.
- Field and twist inclusions are injective maps into extension-field curve
  points; they are not assertions of surjectivity onto all those points.
- Numerical witnesses and external certificate discovery are untrusted input.
  The certificate libraries construct HOL proofs of their asserted properties;
  an external primality or point-count verdict is not used as a proof.

## Documentation conventions and background

This documentation adopts the theory-oriented organization of HOL's
[Abstract Algebra library](https://github.com/HOL-Theorem-Prover/HOL/blob/652d1f0aad5cd537ed1e5d470ba3444e70ba470e/examples/algebra/README.md),
its [Field Library guide](https://github.com/HOL-Theorem-Prover/HOL/blob/652d1f0aad5cd537ed1e5d470ba3444e70ba470e/examples/algebra/field/README.md)
and [in-source field-map documentation](https://github.com/HOL-Theorem-Prover/HOL/blob/652d1f0aad5cd537ed1e5d470ba3444e70ba470e/examples/algebra/field/fieldMapScript.sml).
Local theory headers give purpose, representation assumptions and selected
public definitions/theorems rather than repeating every proof statement.

[The design plan](hol4-algebra-plan.typ) and its
[PDF](hol4-algebra-plan.pdf) record requirements and proposed interfaces.
They are planning material, not a current build report or the API reference.
