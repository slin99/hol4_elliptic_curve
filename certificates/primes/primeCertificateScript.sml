Theory primeCertificate
Ancestors
  arithmetic divides gcd list rich_list number prime ring pred_set combinatorics

Theorem prime_certificate_divides_product:
  prime q ==> (q divides (u * v) <=> q divides u \/ q divides v)
Proof
  metis_tac[P_EUCLIDES, DIVIDES_MULT, MULT_COMM]
QED

(* A full Lucas certificate establishes order n-1, hence the maximal
   possible totient.  Its factor and witness data need not be trusted. *)
Theorem prime_certificate_phi[local]:
  !n. 1 < n /\ phi n = n - 1 ==> prime n
Proof
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `CARD (Euler n) = CARD (residue n)` by
    metis_tac[phi_eq_totient, totient_def, residue_card] >>
  `Euler n SUBSET residue n` by simp[Euler_thm] >>
  `Euler n = residue n` by
    metis_tac[SUBSET_EQ_CARD, Euler_finite, residue_finite] >>
  rewrite_tac[prime_def] >> conj_tac >- decide_tac >>
  gen_tac >> strip_tac >>
  `b <= n` by metis_tac[DIVIDES_LEQ_OR_ZERO, NOT_ZERO_LT_ZERO] >>
  Cases_on `b = n` >> simp[] >>
  `0 < b /\ b < n` by
    metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO, LESS_OR_EQ] >>
  `b IN residue n` by simp[residue_def] >>
  `coprime n b` by metis_tac[Euler_element] >>
  metis_tac[coprime_common_factor, DIVIDES_REFL]
QED

Theorem prime_certificate_divisor[local]:
  !d k. 0 < d /\ d divides k /\ d < k ==>
    ?q. prime q /\ q divides k /\ d divides (k DIV q)
Proof
  rpt strip_tac >>
  `k = d * (k DIV d)` by metis_tac[DIVIDES_EQN_COMM] >>
  `k DIV d <> 1` by (strip_tac >> fs[]) >>
  `?q. prime q /\ q divides (k DIV d)` by
    metis_tac[PRIME_FACTOR] >>
  `0 < q` by metis_tac[PRIME_POS] >>
  `?t. k DIV d = t * q` by metis_tac[divides_def] >>
  `k = (d * t) * q` by metis_tac[MULT_ASSOC] >>
  `k DIV q = d * t` by metis_tac[MULT_DIV] >>
  qexists_tac `q` >>
  metis_tac[divides_def, MULT_COMM]
QED

Theorem prime_certificate_lucas[local]:
  !n a. 1 < n /\ a ** (n - 1) MOD n = 1 /\
    (!q. prime q /\ q divides (n - 1) ==>
         a ** ((n - 1) DIV q) MOD n <> 1) ==>
    prime n
Proof
  rpt strip_tac >>
  `0 < n /\ 0 < n - 1` by decide_tac >>
  `ordz n a divides (n - 1)` by metis_tac[ZN_order_divides_exp] >>
  `0 < ordz n a` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `ordz n a <= n - 1` by metis_tac[DIVIDES_LE] >>
  `ordz n a = n - 1` by
    (spose_not_then assume_tac >>
     `ordz n a < n - 1` by decide_tac >>
     `?q. prime q /\ q divides (n - 1) /\
        ordz n a divides ((n - 1) DIV q)` by
       metis_tac[prime_certificate_divisor] >>
     `0 < (n - 1) DIV q` by
       metis_tac[DIVIDES_EQN_COMM, MULT_EQ_0, PRIME_POS,
                 NOT_ZERO_LT_ZERO] >>
     metis_tac[ZN_order_divides_exp]) >>
  `phi n < n /\ ordz n a <= phi n` by
    metis_tac[phi_lt, ZN_order_upper] >>
  irule prime_certificate_phi >> decide_tac
QED

Theorem prime_certificate_product[local]:
  !fs q. EVERY prime fs /\ prime q /\ q divides PROD fs ==> MEM q fs
Proof
  Induct >-
    (simp[PROD] >> metis_tac[DIVIDES_ONE, NOT_PRIME_1]) >>
  simp[PROD] >> rpt strip_tac >>
  `q divides h \/ q divides PROD fs` by metis_tac[P_EUCLIDES] >>
  metis_tac[prime_divides_only_self]
QED

Theorem prime_certificate_check:
  !n a fs.
    1 < n /\ n - 1 = PROD fs /\ EVERY prime fs /\
    a ** (n - 1) MOD n = 1 /\
    EVERY (\q. a ** ((n - 1) DIV q) MOD n <> 1) fs ==>
    prime n
Proof
  rpt strip_tac >>
  match_mp_tac (Q.SPECL [`n`, `a`] prime_certificate_lucas) >>
  simp[] >>
  rpt strip_tac >>
  `MEM q fs` by metis_tac[prime_certificate_product] >>
  fs[EVERY_MEM] >> metis_tac[]
QED
