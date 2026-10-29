(* ------------------------------------------------------------------------- *)
(* Polynomial Identities Supporting Curve Associativity                      *)
(* ------------------------------------------------------------------------- *)
(*
   Documentation

   Coordinate identities over the existing commutative Ring model used by
   shortWeierstrassGroup. Denominator inverses are explicit variables with
   inverse equations; no field division or curve-group structure is assumed.
   Local arithmetic notation denotes ring_add, ring_mul and ring_pow.

   Main results:
     sw_secant_equations_algebra, sw_tangent_equations_algebra
                                Derive low-degree slope equations.
     sw_assoc_outputs_algebra   Compare the final coordinate formulas.
     sw_assoc_coordinates_algebra
                                Coordinate identity used in associativity.

   IDEAL_USING_TAC supplies polynomial ideal certificates to ringLib's proof
   machinery. These lemmas support the group proof; they are not a standalone
   assertion of the group law without its geometric case analysis.
*)

Theory swAssocAlgebra
Ancestors
  ringLib
Libs
  ringLib idealCertificateLib

open ringLibTheory

Overload "+"[local] = ``ring_add (r:'a Ring)``
Overload "-"[local] = ``ring_sub (r:'a Ring)``
Overload "*"[local] = ``ring_mul (r:'a Ring)``
Overload "**"[local] = ``ring_pow (r:'a Ring)``

fun IDEAL_USING_TAC certificate (asl, goal) =
  let
    val th = idealCertificateLib.IDEAL_RULE ``r:'a Ring``
      (map (fn (eq, coefficient) => (ASSUME eq, coefficient)) certificate) goal
    val carrier_facts = map ASSUME (List.filter pred_setSyntax.is_in asl)
    val closure = [RING_0, RING_1, RING_NEG, RING_ADD, RING_SUB, RING_MUL,
                   RING_POW, RING_OF_NUM, RING_OF_INT]
    fun discharge (premise, result) =
      if List.exists (aconv premise) asl then result
      else PROVE_HYP
        (prove (premise,
          REPEAT (FIRST (map ACCEPT_TAC carrier_facts @
                         map MATCH_ACCEPT_TAC closure @
                         map MATCH_MP_TAC closure @ [CONJ_TAC])))) result
  in
    ACCEPT_TAC (List.foldl discharge th (hyp th)) (asl, goal)
  end

Theorem sw_secant_equations_algebra:
  !(r:'a Ring) x1 y1 x2 y2 a b di m.
  EVERY (\x. x IN ring_carrier r) [x1; y1; x2; y2; a; b; di; m] /\
  y1 ** 2 = x1 ** 3 + a * x1 + b /\
  y2 ** 2 = x2 ** 3 + a * x2 + b /\
  (x2 - x1) * di = ring_1 r /\
  m = (y2 - y1) * di ==>
  y2 - y1 = m * (x2 - x1) /\
  m * (y1 + y2) = x1 ** 2 + x1 * x2 + x2 ** 2 + a
Proof
  rpt gen_tac >> REWRITE_TAC[listTheory.EVERY_DEF] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  conj_tac >-
    IDEAL_USING_TAC
      [(``m = (y2 - y1) * di``, ``ring_neg r (x2 - x1)``),
       (``(x2 - x1) * di = ring_1 r``, ``ring_neg r (y2 - y1)``)] >>
  IDEAL_USING_TAC
    [(``m = (y2 - y1) * di``, ``y1 + y2``),
     (``y1 ** 2 = x1 ** 3 + a * x1 + b``, ``ring_neg r di``),
     (``y2 ** 2 = x2 ** 3 + a * x2 + b``, ``di``),
     (``(x2 - x1) * di = ring_1 r``,
      ``x1 ** 2 + x1 * x2 + x2 ** 2 + a``)]
QED

Theorem sw_tangent_equations_algebra:
  !(r:'a Ring) x y a di m.
  EVERY (\x. x IN ring_carrier r) [x; y; a; di; m] /\
  (ring_of_num r 2 * y) * di = ring_1 r /\
  m = (ring_of_num r 3 * x ** 2 + a) * di ==>
  y - y = m * (x - x) /\
  m * (y + y) = x ** 2 + x * x + x ** 2 + a
Proof
  rpt gen_tac >> REWRITE_TAC[listTheory.EVERY_DEF] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  conj_tac >- IDEAL_USING_TAC [] >>
  IDEAL_USING_TAC
    [(``m = (ring_of_num r 3 * x ** 2 + a) * di``, ``y + y``),
     (``(ring_of_num r 2 * y) * di = ring_1 r``,
      ``ring_of_num r 3 * x ** 2 + a``)]
QED

Theorem sw_assoc_outputs_algebra:
  !(r:'a Ring) x1 y1 x2 y2 x3 m n ux uy vx vy k l.
  EVERY (\x. x IN ring_carrier r)
    [x1; y1; x2; y2; x3; m; n; ux; uy; vx; vy; k; l] /\
  y2 - y1 = m * (x2 - x1) /\
  ux = m ** 2 - x1 - x2 /\
  uy = m * (x1 - ux) - y1 /\
  vx = n ** 2 - x2 - x3 /\
  vy = n * (x2 - vx) - y2 /\
  k * (vx - x1) = vy - y1 /\
  k - l = m - n /\
  (m - n) * (m + l) = x1 - x3 ==>
  let xl = k ** 2 - x1 - vx;
      xr = l ** 2 - ux - x3
  in xl = xr /\ k * (x1 - xl) - y1 = l * (ux - xr) - uy
Proof
  rpt gen_tac >> REWRITE_TAC[listTheory.EVERY_DEF, LET_THM] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  `k ** 2 - x1 - vx = l ** 2 - ux - x3` by
    IDEAL_USING_TAC
      [(``k - l = m - n``, ``k + l + m - n``),
       (``(m - n) * (m + l) = x1 - x3``, ``ring_of_num r 2``),
       (``ux = m ** 2 - x1 - x2``, ``ring_1 r``),
       (``vx = n ** 2 - x2 - x3``, ``ring_neg r (ring_1 r)``)] >>
  `k * (x1 - (k ** 2 - x1 - vx)) - y1 = l * (ux - (l ** 2 - ux - x3)) - uy` by
    IDEAL_USING_TAC
      [(``k ** 2 - x1 - vx = l ** 2 - ux - x3``, ``ring_neg r k``),
       (``(m - n) * (m + l) = x1 - x3``, ``ring_neg r (l + n)``),
       (``k * (vx - x1) = vy - y1``, ``ring_neg r (ring_1 r)``),
       (``k - l = m - n``, ``ring_neg r (l ** 2) + ux + vx + x3``),
       (``uy = m * (x1 - ux) - y1``, ``ring_1 r``),
       (``vy = n * (x2 - vx) - y2``, ``ring_neg r (ring_1 r)``),
       (``ux = m ** 2 - x1 - x2``, ``ring_neg r (l + n)``),
       (``vx = n ** 2 - x2 - x3``, ``l + m``),
       (``y2 - y1 = m * (x2 - x1)``, ``ring_1 r``)] >>
  ASM_REWRITE_TAC[]
QED

(* The secant equations also cover a tangent when the two points coincide.
   Keeping these low-degree equations avoids a single large ideal search over
   all curve equations, intermediate coordinates, and denominator inverses. *)
Theorem sw_assoc_coordinates_algebra:
  !(r:'a Ring) x1 y1 x2 y2 x3 y3 a m n ux uy vx vy k l ia ib.
  EVERY (\x. x IN ring_carrier r)
    [x1; y1; x2; y2; x3; y3; a; m; n; ux; uy; vx; vy; k; l; ia; ib] /\
  y2 - y1 = m * (x2 - x1) /\
  y3 - y2 = n * (x3 - x2) /\
  m * (y1 + y2) = x1 ** 2 + x1 * x2 + x2 ** 2 + a /\
  n * (y2 + y3) = x2 ** 2 + x2 * x3 + x3 ** 2 + a /\
  ux = m ** 2 - x1 - x2 /\
  uy = m * (x1 - ux) - y1 /\
  vx = n ** 2 - x2 - x3 /\
  vy = n * (x2 - vx) - y2 /\
  (vx - x1) * ia = ring_1 r /\
  (x3 - ux) * ib = ring_1 r /\
  k = (vy - y1) * ia /\
  l = (y3 - uy) * ib ==>
  let xl = k ** 2 - x1 - vx;
      xr = l ** 2 - ux - x3
  in xl = xr /\ k * (x1 - xl) - y1 = l * (ux - xr) - uy
Proof
  rpt gen_tac >> REWRITE_TAC[listTheory.EVERY_DEF, LET_THM] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  `k * (vx - x1) = vy - y1` by
    IDEAL_USING_TAC
      [(``k = (vy - y1) * ia``, ``vx - x1``),
       (``(vx - x1) * ia = ring_1 r``, ``vy - y1``)] >>
  `l * (x3 - ux) = y3 - uy` by
    IDEAL_USING_TAC
      [(``l = (y3 - uy) * ib``, ``x3 - ux``),
       (``(x3 - ux) * ib = ring_1 r``, ``y3 - uy``)] >>
  `(y2 + y2) * m = (x2 - x1) * m ** 2 + (x1 ** 2 + x1 * x2 + x2 ** 2 + a)` by
    IDEAL_USING_TAC
      [(``y2 - y1 = m * (x2 - x1)``, ``m``),
       (``m * (y1 + y2) = x1 ** 2 + x1 * x2 + x2 ** 2 + a``, ``ring_1 r``)] >>
  `(y2 + y2) * n = (x2 ** 2 + x2 * x3 + x3 ** 2 + a) - (x3 - x2) * n ** 2` by
    IDEAL_USING_TAC
      [(``y3 - y2 = n * (x3 - x2)``, ``ring_neg r n``),
       (``n * (y2 + y3) = x2 ** 2 + x2 * x3 + x3 ** 2 + a``, ``ring_1 r``)] >>
  `(k - l - (m - n)) * (vx - x1) * (x3 - ux) = ring_0 r` by
    IDEAL_USING_TAC
      [(``k * (vx - x1) = vy - y1``, ``x3 - ux``),
       (``l * (x3 - ux) = y3 - uy``, ``ring_neg r (vx - x1)``),
       (``(y2 + y2) * m = (x2 - x1) * m ** 2 + (x1 ** 2 + x1 * x2 + x2 ** 2 + a)``, ``m + n``),
       (``(y2 + y2) * n = (x2 ** 2 + x2 * x3 + x3 ** 2 + a) - (x3 - x2) * n ** 2``, ``ring_neg r (m + n)``),
       (``uy = m * (x1 - ux) - y1``, ``vx - x1``),
       (``vy = n * (x2 - vx) - y2``, ``x3 - ux``),
       (``ux = m ** 2 - x1 - x2``, ``n * x1 - n * x2 + y1 + y2``),
       (``vx = n ** 2 - x2 - x3``, ``m * x1 - m * x3 - y1 - y3``),
       (``y2 - y1 = m * (x2 - x1)``, ``ring_neg r ((m - n) * (m + n))``),
       (``y3 - y2 = n * (x3 - x2)``, ``ring_neg r (n ** 2) + x1 + x2 + x3``)] >>
  `k - l = m - n` by
    IDEAL_USING_TAC
      [(``(k - l - (m - n)) * (vx - x1) * (x3 - ux) = ring_0 r``, ``ia * ib``),
       (``(vx - x1) * ia = ring_1 r``, ``ring_neg r (k - l - (m - n))``),
       (``(x3 - ux) * ib = ring_1 r``, ``ring_neg r ((k - l - (m - n)) * (vx - x1) * ia)``)] >>
  `((m - n) * (m + l) - x1 + x3) * (x3 - ux) = ring_0 r` by
    IDEAL_USING_TAC
      [(``l * (x3 - ux) = y3 - uy``, ``m - n``),
       (``(y2 + y2) * m = (x2 - x1) * m ** 2 + (x1 ** 2 + x1 * x2 + x2 ** 2 + a)``, ``ring_1 r``),
       (``(y2 + y2) * n = (x2 ** 2 + x2 * x3 + x3 ** 2 + a) - (x3 - x2) * n ** 2``, ``ring_neg r (ring_1 r)``),
       (``uy = m * (x1 - ux) - y1``, ``ring_neg r m + n``),
       (``ux = m ** 2 - x1 - x2``, ``x1 - x3``),
       (``y2 - y1 = m * (x2 - x1)``, ``ring_neg r m + n``),
       (``y3 - y2 = n * (x3 - x2)``, ``m - n``)] >>
  `(m - n) * (m + l) = x1 - x3` by
    IDEAL_USING_TAC
      [(``((m - n) * (m + l) - x1 + x3) * (x3 - ux) = ring_0 r``, ``ib``),
       (``(x3 - ux) * ib = ring_1 r``, ``ring_neg r ((m - n) * (m + l) - x1 + x3)``)] >>
  MATCH_MP_TAC (BETA_RULE (REWRITE_RULE [LET_THM] (Q.SPECL
    [`r`, `x1`, `y1`, `x2`, `y2`, `x3`, `m`, `n`,
     `ux`, `uy`, `vx`, `vy`, `k`, `l`] sw_assoc_outputs_algebra))) >>
  ASM_SIMP_TAC bool_ss [listTheory.EVERY_DEF]
QED

val _ = export_theory();
