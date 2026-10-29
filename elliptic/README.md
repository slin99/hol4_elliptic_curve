# Elliptic Curve Library

Short-Weierstrass curves `y^2 = x^3 + a*x + b` over HOL's modern fields,
with homogeneous representations, maps and elementary cardinality arguments.
The group law is in the [group library](../groups/README.md); named curve
parameters and certificate applications are in the
[instance library](instances/README.md).

## Core theories

- [**shortWeierstrass**](core/shortWeierstrassScript.sml) — the `sw_point`
  datatype, curve equation, discriminant, `ShortWeierstrassCurve` predicate
  and point set. `sw_points_member` connects set membership to the equation.
- [**shortWeierstrassProjective**](core/shortWeierstrassProjectiveScript.sml)
  — nonzero homogeneous triples, nonzero scaling, equivalence and the relation
  to affine points and infinity. `sw_projective_curve_iff_rep` connects the
  homogeneous equation with the representation relation;
  `sw_projective_reps_equiv` characterizes equality of represented points.
- [**ellipticCardinality**](core/ellipticCardinalityScript.sml) — the
  two-points-per-x bound, odd-cardinality arguments and exact-order criteria.
  `sw_points_card_bound` proves `CARD points <= 2*CARD field + 1`.
  The `sw_cardinality_from_odd_divisor`, `sw_cardinality_from_odd_subgroup`
  and `sw_cardinality_from_odd_point_order` theorems combine this bound with
  divisibility and absence of nonidentity 2-torsion. These are elementary
  arguments, not Hasse's theorem or an assumed curve-order formula.
- [**shortWeierstrassSmall**](core/shortWeierstrassSmallScript.sml) — a worked
  example over `GF 5`: the six points of `y^2 = x^3 + 1`, generator `(2,2)`,
  3-torsion, projective facts and transport through an isomorphic option-valued
  field.

## Morphism theories

- [**ellipticMorphisms**](morphisms/ellipticMorphismsScript.sml) — apply a
  field map to affine coordinates with `sw_map_point`, fixing infinity.
  `sw_field_homo_group` transports the group operation;
  `sw_field_iso_group` gives a group isomorphism for a field isomorphism.
  `sw_curve_homo_scalar`, `sw_curve_iso_order` and `sw_curve_iso_torsion`
  expose scalar, order and torsion transport.
- [**ellipticScaling**](morphisms/ellipticScalingScript.sml) — change affine
  coordinates by `(x,y) -> (u^2*x,u^3*y)`, sending coefficients to
  `(u^4*a,u^6*b)`. With nonzero carrier `u`, `sw_scale_group_iso` gives a
  group isomorphism. `sw_scale_scalar`, `sw_scale_order` and
  `sw_scale_torsion` give the associated transport facts.
- [**ellipticCMMap**](morphisms/ellipticCMMapScript.sml) — on curves with
  `a = 0`, send `(x,y)` to `(beta*x,y)` for a carrier element satisfying
  `beta^3 = 1`. `sw_cm_map_group_endo` and `sw_cm_map_group_iso` package the
  map, and `sw_cm_map_third` states that its third iterate is the identity.
  The hypothesis allows `beta = 1`; it does not require a primitive root.

## Representations

`ECInfinity` is the identity point. `ECAffine x y` is only a constructor;
`sw_on_curve` additionally requires both coordinates in the field carrier
and the equation. `ShortWeierstrassCurve` requires a field, carrier
coefficients, characteristic different from 2 and 3 and nonzero discriminant.
These hypotheses must not be dropped when applying the group theorems.

Homogeneous coordinates are **ordinary projective coordinates**, not
Jacobian coordinates:

- For nonzero `Z`, `(X,Y,Z)` decodes to `(X/Z,Y/Z)`.
- Curve representatives of infinity are `(0,Y,0)` with nonzero carrier `Y`.
- The homogeneous equation is `Y^2*Z = X^3 + a*X*Z^2 + b*Z^3`.
- `sw_projective_valid` checks a nonzero carrier triple, not the curve equation.
  `sw_projective_rep` is the curve-representation relation.
- `sw_projective_to_point` is total and sends every `Z = 0` input to infinity.
  This does not make every such triple a valid representative.

Use `sw_point_projective_roundtrip` for embedding then decoding, and
`sw_projective_point_roundtrip` for recovering an equivalent homogeneous
representative. `sw_projective_on_curve_scale` preserves the curve predicate
under nonzero homogeneous scaling. This common scaling of all three
coordinates differs from the affine model change in `ellipticScaling`.

## Choosing a map or certificate

A field inclusion gives a map into points over the target field, not a
surjection onto every target-field point. Use a field isomorphism for the
`sw_field_iso_group` theorem; use
[pairingTwistMorphisms](instances/pairing/pairingTwistMorphismsScript.sml)
for injective twist embeddings into the degree-12 fields.

To prove exact point order `N > 0`,
`group_exact_order_certificate` and `sw_exact_order_certificate` require
`[N]P = O` and `[N/q]P <> O` for every prime divisor `q` of `N`.
An annihilation equation alone proves only that the order divides `N`.
The [certificate library](../certificates/README.md) supplies arithmetic and
coordinate proof machinery for concrete applications.

See the [project README](../README.md#build) for builds and pinned dependencies.
