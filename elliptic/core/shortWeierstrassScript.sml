Theory shortWeierstrass
Ancestors
  field

Datatype:
  sw_point = ECInfinity | ECAffine 'a 'a
End

Definition sw_curve_rhs_def:
  sw_curve_rhs (r:'a field) a b x =
    r.sum.op (r.sum.op (r.prod.exp x 3) (r.prod.op a x)) b
End

Definition sw_discriminant_def:
  sw_discriminant (r:'a field) a b =
    r.sum.inv
      (r.prod.op (r.sum.exp r.prod.id 16)
        (r.sum.op
          (r.prod.op (r.sum.exp r.prod.id 4) (r.prod.exp a 3))
          (r.prod.op (r.sum.exp r.prod.id 27) (r.prod.exp b 2))))
End

Definition ShortWeierstrassCurve_def:
  ShortWeierstrassCurve (r:'a field) a b <=>
    Field r /\
    a IN r.carrier /\
    b IN r.carrier /\
    char r <> 2 /\
    char r <> 3 /\
    sw_discriminant r a b <> r.sum.id
End

Definition sw_on_curve_def:
  (sw_on_curve (r:'a field) a b ECInfinity <=> T) /\
  (sw_on_curve r a b (ECAffine x y) <=>
    x IN r.carrier /\
    y IN r.carrier /\
    r.prod.exp y 2 = sw_curve_rhs r a b x)
End

Definition sw_points_def:
  sw_points (r:'a field) a b = {P | sw_on_curve r a b P}
End

Theorem sw_on_curve_ECInfinity[simp]:
  !(r:'a field) a b. sw_on_curve r a b ECInfinity
Proof
  rw[sw_on_curve_def]
QED

Theorem sw_on_curve_ECAffine[simp]:
  !(r:'a field) a b x y.
    sw_on_curve r a b (ECAffine x y) <=>
    x IN r.carrier /\
    y IN r.carrier /\
    r.prod.exp y 2 = sw_curve_rhs r a b x
Proof
  rw[sw_on_curve_def]
QED

Theorem sw_points_member[simp]:
  !(r:'a field) a b P.
    P IN sw_points r a b <=> sw_on_curve r a b P
Proof
  rw[sw_points_def]
QED

val _ = export_theory();
