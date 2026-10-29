structure idealCertificateLib :> idealCertificateLib =
struct

open HolKernel Drule boolSyntax ringSyntax

val ERR = mk_HOL_ERR "idealCertificateLib" "IDEAL_RULE"

fun IDEAL_RULE r certificate target =
  let
    val ringty = type_of r
    val (tyname, tyargs) = dest_type ringty
    val _ =
      if tyname = "Ring" andalso length tyargs = 1 andalso
         ringty = mk_thy_type {Thy = "ringLib", Tyop = "Ring", Args = tyargs}
      then () else raise ERR "Expected a ringLib Ring term"
    val elementty = hd tyargs
    fun opterm op' = list_mk_icomb (op', [r])
    val add = opterm ring_add_tm
    val sub = opterm ring_sub_tm
    val mul = opterm ring_mul_tm
    val zero = list_mk_icomb
      (prim_mk_const {Thy = "ringLib", Name = "ring_0"}, [r])
    fun binary op' x y = list_mk_comb (op', [x,y])
    fun same_ring r' =
      if aconv r r' then () else raise ERR "Mixed rings in polynomial"
    fun polynomial tm =
      let
        fun unary dest =
          let val (r',x) = dest tm in same_ring r'; polynomial x end
        fun binary_check dest =
          let val (r',x,y) = dest tm
          in same_ring r'; polynomial x; polynomial y end
      in
        if type_of tm <> elementty then raise ERR "Wrong polynomial type"
        else if is_var tm then ()
        else if is_ring_0 tm orelse is_ring_1 tm then same_ring (rand tm)
        else if is_ring_of_num tm then
          let val (r',n) = dest_ring_of_num tm
          in
            same_ring r';
            if numSyntax.is_numeral n then ()
            else raise ERR "Expected a natural coefficient literal"
          end
        else if is_ring_of_int tm then
          let val (r',n) = dest_ring_of_int tm
          in
            same_ring r';
            if intSyntax.is_int_literal n then ()
            else raise ERR "Expected an integer coefficient literal"
          end
        else if is_ring_neg tm then unary dest_ring_neg
        else if is_ring_add tm then binary_check dest_ring_add
        else if is_ring_sub tm then binary_check dest_ring_sub
        else if is_ring_mul tm then binary_check dest_ring_mul
        else if is_ring_pow tm then
          let val (r',x,n) = dest_ring_pow tm
          in
            same_ring r'; polynomial x;
            if numSyntax.is_numeral n then ()
            else raise ERR "Expected a natural exponent literal"
          end
        else raise ERR "Expected an integer polynomial (no division or opaque atoms)"
      end
    fun equation tm =
      if is_eq tm then
        let val (l,u) = dest_eq tm
        in polynomial l; polynomial u; (l,u) end
      else raise ERR "Expected an equality"
    val (l,u) = equation target
    fun summand (f,c) =
      let
        val (_,b) = equation (concl f)
        val _ = polynomial c
        (* Congruence replaces only this equation's left-hand occurrence;
           rewriting all occurrences could loop for equations such as x=x+y. *)
        val diff = AP_THM (AP_TERM sub f) b
      in
        AP_TERM (mk_comb (mul,c)) diff
      end
    fun sum [] = REFL zero
      | sum [th] = th
      | sum (th::ths) = MK_COMB (AP_TERM add th, sum ths)
    val sumth = sum (map summand certificate)
    (* Neither normalization query contains any original equation premise.
       In particular RING_RULE cannot perform ideal/Groebner search here. *)
    val identity = UNDISCH_ALL (ringLib.RING_RULE
      (mk_eq (binary sub l u, lhs (concl sumth))))
    val vanishes = UNDISCH_ALL (ringLib.RING_RULE
      (mk_eq (rhs (concl sumth), zero)))
    val difference = TRANS identity (TRANS sumth vanishes)
    val sub_zero = UNDISCH
      (SPECL [r,l,u] ringLibTheory.RING_SUB_EQ_0)
  in
    EQ_MP sub_zero difference
  end

end
