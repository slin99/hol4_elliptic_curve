# Curve Group Library

The rational points of a nonsingular short-Weierstrass curve form an Abelian
group over a field of characteristic other than 2 or 3. These theories use
HOL's existing `groupTheory` records and operations.

## Theory

- [**shortWeierstrassGroup**](shortWeierstrassGroupScript.sml) — negation,
  chord-and-tangent addition, closure, associativity and the group record.
  `short_weierstrass_abelian_group` is the principal entry point;
  `short_weierstrass_finite_group` adds finiteness when the field is finite.
- [**ellipticTorsion**](ellipticTorsionScript.sml) — scalar laws, rational
  torsion as a kernel, generated subgroups, point orders and cofactor clearing.
  Start with `sw_torsion_member`, `sw_torsion_subgroup`, `sw_torsion_order`,
  `sw_generated_subgroup` and `sw_generator_card`.
- [**swAssocAlgebra**](swAssocAlgebraScript.sml) — polynomial identities
  supporting the associativity proof. Denominator inverses appear as explicit
  variables satisfying inverse equations in the existing commutative-ring
  model. Consumers normally import the group theory instead of these lemmas.

The point datatype, equation and nonsingularity predicate are in
[shortWeierstrass](../elliptic/core/shortWeierstrassScript.sml).
See the [curve guide](../elliptic/README.md) for representations and maps, and
[concrete instances](../elliptic/instances/README.md) for named generators and
cardinalities.

## Operations

For `g = sw_group r a b`:

| Record operation | Curve interpretation |
| --- | --- |
| `g.carrier` | `sw_points r a b` |
| `g.id` | `ECInfinity` |
| `g.op P Q` | `sw_add r a b P Q` |
| `g.inv P` | `sw_neg r P`, under the curve and membership hypotheses |
| `g.exp P n` | Natural-number scalar multiplication `[n]P` |

`sw_group_carrier`, `sw_group_id`, `sw_group_op` and `sw_group_inv` connect
these interfaces. The coordinate definitions are total; their group laws
require `ShortWeierstrassCurve r a b` and point membership where stated.

## Torsion, generators and cofactors

`sw_torsion_group r a b n` consists of rational curve points killed by `[n]`.
It is not a statement about all torsion points over an algebraic closure.
`sw_torsion_zero` gives the whole group, while `sw_torsion_one_carrier` gives
only infinity. `sw_torsion_order` characterizes membership by divisibility of
the point order; HOL encodes infinite order as `0`.

`Generated g P` has carrier consisting of natural-number multiples of `P`.
The finite-field results `sw_generated_subgroup` and `sw_generated_cyclic`
establish the subgroup and cyclic-group properties. A point of positive
order `n` generates a structure with `n` elements (`sw_generator_card`).
This does not establish that it generates the whole curve. Use
`sw_cofactor_one_generated` when its order equals the full curve cardinality.

`sw_cofactor_clearing` uses a proved full cardinality `h*n` to place `[h]P`
in rational `n`-torsion. It neither proves `[h]P` is nonzero nor identifies
that torsion with a particular named generated subgroup.
`sw_cofactor_clearing_order` proves an exact output order when the input's
exact order is known to be `h*n` with both factors positive.

For a complete small example, see
[shortWeierstrassSmall](../elliptic/core/shortWeierstrassSmallScript.sml).
Build commands are in the [project README](../README.md#build).
