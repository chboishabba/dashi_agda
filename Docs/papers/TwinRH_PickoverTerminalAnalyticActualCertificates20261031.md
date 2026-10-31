# Three terminal analytic targets: actual progress, imported proofs, and exact max-cuts

Date: 2026-10-31. This is a mathematical proof audit, not a claim to have resolved the RH/twin-prime conjectures or the target giant sine sign. No CI requested; no Agda/Lean kernel check was performed this pass.

## T: actual shifted Mangoldt two-point correlation

Let T(X)=sum_{2<=n<=X-2} Lambda(n)Lambda(n+2), pi_2(X)=#{n:2<=n<=X-2,n,n+2 both prime}, and P(X)=sum over prime-only pairs log(n)log(n+2). Let Q(X) be the count of proper prime powers p^k<=X (k>=2).

**Elementary complete estimate:** 0<=T(X)-P(X)<=2Q(X)(log X)^2, Q(X)<=floor(sqrt X)floor(log_2 X). The discrepancy is O(sqrt X (log X)^3)=o(X). Proof: a non-prime-only nonzero pair must have a proper prime power at an endpoint; every power appears at most once per endpoint; each weight <= (log X)^2; count integer bases <=sqrt X and exponent indices <=floor(log_2 X).

**Imported unconditional analytic bound (Brun's sieve theorem, classical original authorship):** pi_2(X)=O(X/(log X)^2). Therefore P(X)<= (log X)^2 pi_2(X)=O(X) and T(X)=O(X). This is a genuine real weighted shifted-prime correlation estimate. It DOES NOT imply T(X)>=cX or infinitely many gap-two pairs. Reuse Brun/Selberg source rather than attribute the analytic upper bound to a DASHI finite script. A proof-bearing Agda port of Brun's asymptotic inequality and the actual Mangoldt/log ordered-real inequality remains unimplemented.

**Independent finite two-point CRT bound:** for z>=2, set k=number of primes p<=z, density D_z=(1/2)*prod_{3<=p<=z}(1-2/p), and B_z=2*3^(k-1). CRT plus three-way inclusion-exclusion for each odd p gives, for X>=z+2,

  0<=pi_2(X)<= z + X*D_z + B_z.

The survivor count has absolute discrepancy <=B_z from its main term. Complete proof: each inclusion-exclusion residue condition is one congruence modulo a product of distinct primes; its count differs from X divided by that product by <=1; there are B_z terms. At most z genuine prime pairs have their first prime <=z, and all the others pass the small-prime sieve. Combining with the proper-power estimate yields the *fully explicit genuine Mangoldt bound*

  0<=T(X)<= (log X)^2 * (z + X*D_z + B_z
                         + 2*floor(sqrt X)*floor(log_2 X)).

The source-written and independently finitely checked script is scripts/check_twin_prime_two_point_crt_sieve_estimate.py. This is not a new infinitude theorem. The exact new terminal obligation is an unbounded positive lower-bound certificate for actual shifted-prime correlation, or equivalent gap-two infinitude. No known purely finite sieve satisfies that; Polymath8b's parity obstruction must be overcome by genuinely new arithmetic information.

Sources: Brun's twin sieve as summarized in sieve lecture notes https://sites.math.rutgers.edu/~alexk/files/BrunSelberg.pdf ; Polymath8b parity discussion https://link.springer.com/article/10.1186/s40687-014-0012-7 . Existing Agda: DASHI/Arithmetic/SixWheelCRTExact.agda, FinitePrimeProductSieveExact.agda, TwinPrimeActualPairSectionGluingExact.agda, DASHI/Analysis/ChebyshevPrimeCounting.agda.

## R: actual completed zeta zero carrier + 7/8 theorem

The correct stronger OpenAI source is September 30, 2026: https://github.com/openai/math/tree/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026 ; the alternative October 5, 2026 proof gives only 11/12. Their authorship is OpenAI, not DASHI. OpenAI's publicly posted Lean comparator theorem OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re comes from lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean using the separate Detector/FinalAssemblyUnconditional proof. The ComparatorChallenges statement has an intentional sorry placeholder; it is NOT the proof file. lean/docs/003.md describes the formalization's precise scope; independent external specialist review is separate.

Source written: DASHI/Analysis/RiemannQuasiRHActualXiZeroReflectionExact.agda. This consumes the ACTUAL AnalyticSubstrate.CompletedRiemannZeta, not a rational-coordinate stand-in. A minimal XiZeroValueSemantics witnesses that the owner's abstract isZero predicate means actual xi value equals zero and conjugation fixes zero. From the existing completed xi functional equation, conjugation and zero-equivalence, it proves that nontrivial zero at s implies nontrivial zero at conj(oneMinus s). A separate ClaimedRightZeroFree consumes the SOURCE's theorem statement, and transports exclusion from real-part >7/8 to the reflected-left condition on the same actual analytic carrier.

Absent analytic real arithmetic connecting the predicate at conj(oneMinus s) with Re(s)<1/8, no literal numerical left interval is asserted by the Agda module. The imported right-side exclusion is NOT locally re-proved. A 7/8 outer strip does not imply RH (critical line 1/2); terminal missing lemma remains full off-line exclusion including 1/2<Re(s)<=7/8. Preserve the G2/G3 joint quartic remainder proof owner.

## P: real phase of sin(99^(9999!))

New exact script scripts/check_pickover_certified_compressed_modular_phase.py computes a rational Machin interval [L,U] for pi, midpoint alpha=a/b and delta=(U-L)/2, and the compact signed residue r congruent to b*99^m modulo 2a, for small m. There is an integer q with N=99^m=r/b+2q alpha, and |q|<=bN/(2a)+1. Consequently by sine's 1-Lipschitz inequality,

  |sin N-sin(r/b)| <= ((bN/a)+2)*delta.

Combining this drift bound with a rational Taylor enclosure around r/b gives an exact rational sine sign only when zero is excluded; the program fails closed otherwise. An early capped-power comparison does not construct 99^m if the approximation is manifestly too coarse. The --pickover option attempts m=9999! without fabricating a certificate. Independent local exact-rational calculations agreed with high-precision signs for m=1,2,3,4,6,8, but were NOT for the terminal m.

**Information barrier:** finite congruences alone cannot determine real sine sign for every integer, because for any modulus M, the progression n=r+kM is equidistributed mod 2pi (M/(2pi) irrational). Any special-argument shortcut must use a real-irrational transfer theorem beyond an arbitrary fixed finite residue/fibre. With a naive rational pi surrogate, the phase drift scales as N*|pi-alpha|, demanding ~log_10 N ~ 9999!*log_10(99) digits of pi for a uniform certificate; this is an obstruction to THIS method, not a theorem against all compressed certificates. Neither the specific terminal sign nor its sign-enclosing interval has been produced.

Canonical owners: BishopMachinArctanConstructionExact, BishopMachinQuarterAngleBranchExact, JInvariantBishopTrigUnitPhaseExact, SignedSSPFRACTRANWeaveExact, QuadraticIrrationalSignedApproximationFibreExact, SSP369Ultrametric, selected 369/27 pants gluing. The Machin-real to trigonometric-pi branch seam must be preserved.

## Attribution / evidence distinctions

Original Brun/Polymath/Hardy-Littlewood mathematical results remain original. The OpenAI 7/8 and 11/12 manuscripts and Lean proof own their theorem; the new DASHI analytic bridge is an independent proof adapter. A kernel-verified external theorem is not an Agda-kernel theorem without a witnessed semantic import. Experimental counts, numeric matches and finite scripts do not certify infinite arithmetic conclusions. Do not touch ESD or promote Monster/SSP/C3 numerology into same-object Hecke representations.


## 2026-10-31 concrete infinite fixed-sieve failure certificate

New `scripts/check_twin_prime_finite_screen_infinite_composite_witnesses.py` (commit `0c9e12545cbc535c4f5c38ea1568df44abc8c354`) constructs a proof-bearing **infinite family of composite false positives** for each fixed finite set F of primes containing 2 and 3. Set W=∏_{p∈F}p, choose distinct P,Q>max(F), and CRT-solve n≡−1 (mod W), n≡0 (mod P), n≡−2 (mod Q). All n=n0+tWPQ for t≥1 survive every p∈F while n and n+2 are both composite. For full canonical SSP15 F, one locally independently checked example is n=13050476785267491359789, with 73|n and 79|(n+2), yet no SSP15 prime divides either endpoint. This is a theorem for arbitrary fixed F, with one test example, and completely rules out *fixed-screen survivor counting alone* as a twin-infinitude proof. It does NOT rule out genuinely dynamic or parity-breaking prime-distribution mathematics. The remaining lemma T03 must inject genuinely global arithmetic beyond any fixed finite chart.

New actual xi zero-carrier adapter, explicit Brun upper estimate, and Pickover fail-closed phase test are detailed above. The original terminal goals remain RH at 1/2, positive gap-two lower correlation, and the true giant sine sign, none of which is accomplished by this finite-sieve no-go.
