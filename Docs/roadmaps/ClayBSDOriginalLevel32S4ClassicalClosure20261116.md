## 21 November 2026 — Mellin source correction / weld-forward (latest)

The **original Mellin compiler is ALREADY PRESENT** in
`DASHI/Mathematics/Automorphic/MellinSplitFunctionalEquationExact.agda`:
`MellinSplitData`, `completedTransform`, and the proved
`mellinSplitFunctionalEquation`. The selected E32 owner
`EllipticCMLevel32FrickeMellinExact` ALREADY imports it directly
and proves `mellinCentralLowerEqualsUpper` and
`mellinCentralValueIsTwiceTail` under the actual corresponding
substitution and fixed-point premises. **Do not invent another Mellin
split, eta transform skeleton, or anonymous analytic value.**

The exact remaining P0 gap is to instantiate this existing source
with the **actual original E:y²=x³−x analytic elliptic L(E,s)**
and genuine infinite `eta(4z)^2 eta(8z)^2` form, with
actual normalized modularity and change-of-variable proofs.
The existing real positive-tail estimate is mathematically available
conditional on the classical analytic identity; it does not supply
the original function identity by itself. On the current Agda branch,
`constantUnitNormalizedReceipt` demonstrates that an arbitrary
`NormalizedOneDimensionalQSeries` is NOT a proof that the actual
original E32 Fourier coefficients have been selected.

**GRH also remains P0**, not postponed as a consequence of this
selected-curve BSD work: original Lean #113 all-Dirichlet
`UpperTheory.EveryCharacter` and independent full-source formal
verification, then v4.33.1→root/Agda same-function admission.
The active Agda #1533
`Docs/roadmaps/GRHP0OriginalEveryCharacterMellinForwardWeld20261121.md`
controls that separate P0. Existing G2 Gamma/Mellin/Weil
proof-relevant transport is a reusable theorem owner, not new
analytic Dirichlet GRH by name matching.

All R445/F19, K4/S4 and iteration numbers are method names, not
main proof endpoints. No Agda kernel or analytic endpoint is promoted.

---

# BSD S4 original E:y²=x³−x — same-source 2-isogeny, level-32 newform, Mellin and central positivity

## 21 November 2026 — P0 theorem-first correction (supersedes iteration-ledgers)

**Proof target, not a round number:** for the original selected E32 curve,
realize the actual analytic L(E,s), its exact same-curve modular/eta
identity, and a genuine nonzero central value in a pinned formal carrier.
Separately, pay selected Mordell-Weil/Selmer/Sha and eventually the
universal BSD rank equality. K1–K5, S1–S6, source files and PR numbers
are attempts/donors, never milestones on the main theorem by themselves.

**Substantive mathematical P0 progress:** the original S4 classical
Mellin/Fricke argument admits the explicit positive lower bound
`L(E,1) >= 2*(64428653584/66556260225)*exp(-pi/(2*sqrt(2)))`
(about **0.637588175627469**), conditional on the genuine original
Dedekind eta product and the ORIGINAL E32 level-32 modular/Mellin
identification. Proof: for t≥1/√32, r=exp(-8πt)<1/64 by the exact
degree-eight Taylor rational certificate for exp(21/5)>64. The two
positive infinite eta products are uniformly ≥62/63 and ≥4094/4095.
The full proof and authority ledger:
`Docs/roadmaps/BSDOriginalLevel32P0PositiveTailLowerBound20261121.md`.
Independent exact-rational regression:
`scripts/check_bsd_level32_original_positive_tail_bound_p0.py`.
**This improves an explicit selected S4 classical estimate; it is NOT
a native Agda proof, nor a proof of its imported Mellin identity.**

**Critical same-object correction:** the new P0
`NormalizedOneDimensionalQSeries f g` still accepts arbitrary f and g,
even constant-one functions. Its source-written
`constantUnitNormalizedReceipt` is a deliberate countermodel showing
that abstract normalized all-n equality does **not** prove f is the
actual original E32 elliptic newform. The `BSD.EllipticLFunctionData`
record is indexed by E32 but its `eulerProduct : Set` and
`analyticContinuation : Set` fields are *uninhabited semantic
requirements*, not computed analytic L-functions. A p=5 original row
does not fix all-n coefficients. The pending native theorem must
identify the **actual original coefficients** and analytic function
with the level-32 eta coefficients, then transfer the same Mellin value.

**Next source proof payments:** actual analytic eta product and
imaginary-axis positivity in the selected carrier; Newman/Ligozat
analytic theorem and `dim S₂(Γ₀(32))=1` on a genuine form space;
a verified E32 modularity/2-isogeny L-series equality for **all n**;
typed Fricke/Mellin source equality; transitive kernel acceptance.
No rank-zero selected BSD strong formula follows from a p5 receipt
or from this improved positive-tail inequality alone.


## 21 November 2026 — master-native Agda BSD P0 source weld

**Reconciliation:** the source-identified original Agda golden BSD K1–K5 and conductor-32 K4 modules from historical #1500 already exist on `master` (key matching blob SHA checked). #1500 diverges substantially from current `master`; no 49,000-commit historical branch replay or second Kummer/eta/Hecke stack is warranted. The active P0 integration is a NEW `master`-based branch, `agent/bsd-p0-original-level32-samecurve-weld-20261121`.

**New original proof candidate:** `DASHI/Mathematics/Arithmetic/EllipticBSDOriginalLevel32SameCurveP0BIDIExact.agda`. It reuses original `curveY2EqualsX3MinusX`, original `BirchSwinnertonDyerBoundary.EllipticLFunctionData` at precisely that curve, its literal original p=5 datum, and the ALREADY proved normalized-one-dimensional-q-series all-n forward theorem. It adds an explicit inverse normalization construction (given all-n equality and f₁=g₁=1, construct the one-dimensional proportionality record with c=1) and a no-definitionally-identical-j=0-model negative control. The same-source record's **actual modularity/dimension-one premise is not constructed**, and its `EllipticLFunctionData` is a typed interface rather than a realized global analytic function. The module is imported by the original BSD K1–K5 root and checker. Source-written; native kernel **not run**.

**New exact independent local checks:** `scripts/check_bsd_original_level32_samecurve_p0.py` constructs f32=q∏(1−q⁴ⁿ)²(1−q⁸ⁿ)² to q^512 and compares every p<400 good-prime Fourier coefficient to direct original E:y²=x³−x point counts: 76/76 PASS. Distinct-curve counterexample at p=5: original E32 a₅=−2 while Lean #114 j=0 E36 a₅=0. This validates a finite signature, **not** same-curve analytic modularity or infinite Euler convergence.

**Highest-value K4 P0 remaining:** genuinely instantiate the original level-32 eta product as a holomorphic weight-two cusp form via Dedekind/Newman/Ligozat and actual genus/dimension-one theorem; attach the ORIGINAL E32 modularity, including isogeny-invariant L(E,s) with optimal E':y²=x³+4x; establish exact source-level Mellin/Fricke equality to the same original analytic L(E,1) and strict positive real eta tail; run pinned Agda/Lean kernels and transitive axiom audit. The CLASSICAL S4 closure recorded earlier in this document is not a native proof receipt. Selected K1–K3/K5 and universal S6 remain separately OPEN.

**YM separation:** #1444 original finite source owners and master-based #1536 P0 F19/R445 source permutations are distinct from this BSD selected-curve proof. Sharing original-source BIDI / constructive convergence methods does not identify their measures, Hamiltonians or L-functions.



**16 November 2026. Exact gate S4: CLOSED in the user-authorized CLASSICAL MATHEMATICAL protocol, using previously established external modularity/eta theorems and new explicit same-selected-curve reduction; NOT Agda or Lean native kernel acceptance.** This is the rank-zero analytic L-value for the SINGLE selected conductor-32 curve. It is not the universal Birch–Swinnerton-Dyer conjecture, not the odd-primary Sha theorem, not selected MW rank=0, and does not close S3/S5/S6 or any of the six original Clay endpoints.

## Exact owner and source identity

The selected ORIGINAL curve in the Agda source is **E: y²=x³−x**, Weierstrass coefficients [0,0,0,-1,0], conductor N=32, LMFDB curve **32.a3** (NOT Cremona label 32a3; the LMFDB and Cremona numberings differ). On the selected Lean source Synthesis/MillenniumBSDMathlibLFunctionWeld.lean, the curve is literally cmWeierstrass; its cmFormalLFunction and cmLSeries are genuine library elliptic L-data, NOT a polynomial or toy Dirichlet L.

The associated optimal elliptic curve in the same rational isogeny class 32.a is **E': y²=x³+4x**, LMFDB curve **32.a4** (Cremona 32a1). The newform is **32.2.a.a** and its explicit formula is **f(z)=η(4z)²η(8z)²**. This is a crucial source-identity subtlety: older modularity/eta references sometimes attach the eta quotient to E' rather than E. They share an L-function because of a rational 2-isogeny; they are NOT the same rational Weierstrass curve.

Primary external references (classical facts, **not claims that Agda proved them**):
- LMFDB conductor-32 isogeny class, complete four-curve list, optimal curve, same modular form: https://www.lmfdb.org/EllipticCurve/Q/32/a/
- LMFDB selected original y²=x³−x curve: https://www.lmfdb.org/EllipticCurve/Q/32/a/3
- LMFDB optimal eta curve y²=x³+4x: https://www.lmfdb.org/EllipticCurve/Q/32/a/4
- Original selected newform 32.2.a.a and complete L-data (LMFDB): https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/32/2/a/a/
- Andrew Kobin, Modular Forms, Section 5.3, Theorem 5.3.3: the literal E:y²=x³−x has conductor 32, and newform η(4z)²η(8z)² has a(p)=−sum_x Legendre(x³−x,p) at all p≥5, matching selected original good-prime counts: https://static1.squarespace.com/static/5aff705c5ffd207cc87a512d/t/5f16591cad96ed6474ca5945/1595300125935/Modular%2BForms.pdf
- Fumio Hazama, J. Math. Sci. Univ. Tokyo 14 (2007), pp. 108–110, expressly constructs the optimal E': y²=x³+4x associated with the level-32 eta form: https://www.ms.u-tokyo.ac.jp/journal/pdf/jms140104.pdf
- Classical Newman/Gordon–Hughes/Ligozat eta-quotient and cusp criteria; genus/dimension formula for X0(N); modularity of elliptic curves over Q; rational-isogeny invariance of Hasse–Weil L-functions; Dedekind eta inversion and normalized Mellin transform. These are IMPORTED established theorems, not novel calculations.

Repository owners READ directly on Clay #1499 and Lean #108:
- DASHI/Mathematics/Automorphic/EllipticCMLevel32EtaNewmanArithmeticExact.agda (correct N=32, weight=2, eta exponents r4=r8=2, q1=1 arithmetic)
- DASHI/Mathematics/Automorphic/EllipticCMLevel32LigozatCuspArithmeticExact.agda (six d|32 cusp arithmetic, all cusp orders 1)
- DASHI/Mathematics/Automorphic/EllipticCMLevel32GenusOneArithmeticExact.agda (index 48, 8 cusps, g=1 and target dim S2 Gamma0(32)=1)
- DASHI/Mathematics/Automorphic/EllipticCMLevel32FrickeMellinExact.agda (source-written algebraic compiler with eta inversion and Mellin fields as premises)
- DASHI/Mathematics/Automorphic/EllipticCMNormalizedOneDimensionalQSeriesExact.agda (normalized one-dimensional space implies all-n identity, conditional on actual modular-form membership)
- Synthesis/MillenniumBSDMathlibLFunctionWeld.lean (genuine source E, original actual all-n L-series)
- Synthesis/MillenniumBSDCMLevel32ActualEtaInfiniteNonzeroExact.lean (source-written actual mathlib Dedekind eta function, nonzero on upper half plane, kernel unchecked)
- docs/bsd-level32-positive-tail-proof-20261114.md (original Bernoulli and rational uniform infinite product bound, previously conditional on original analytic weld).

## New explicit rational isogeny: SAME literal selected curve

For x≠0 on E, define

    X = x − 1/x,
    Y = y (1 + 1/x²).

The exact rational-function identity is

    (x³−x)(1+1/x²)² = (x−1/x)³+4(x−1/x).

Hence y²=x³−x implies Y²=X³+4X. For prescribed X, the source x obeys

    x² − Xx − 1 = 0,

so the map has generic degree **2** (discriminant X²+4). It extends over x=0 by sending the rational 2-torsion (0,0) to the target point at infinity and sends O to O. A nonconstant degree-two morphism of elliptic curves taking O to O is a separable degree-two Q-isogeny, with kernel {O,(0,0)}. This is the actual 2-isogeny between the original E and E', not a change of model made definitionally equal.

The classical isogeny-invariance theorem identifies their rational Tate modules up to Q_l-isomorphism, so EVERY good/bad local Euler factor agrees; in particular p=2 is not skipped. Therefore:

    L(E,s) = L(E',s)

as globally normalized analytic L-functions after their established continuations. The explicit polynomial identity and the degree-two fibre were proved symbolically by exact SymPy polynomial arithmetic; that execution cannot substitute for the classical theorem that the map is a global elliptic isogeny nor isogeny invariance of L, which are cited and invoked explicitly.

## The actual selected level-32 normalized newform

Dedekind eta has η(z)=q^(1/24) product_{n≥1}(1−q^n), q=e^(2πiz). Thus

    f32(z) = η(4z)²η(8z)²
           = q product_{n≥1}(1−q^(4n))²(1−q^(8n))²,

whose q1 coefficient is exactly 1. Standard Newman/Gordon–Hughes criterion with N=32,r4=r8=2 proves weight 2, level 32 and trivial character once the standard modular transformation theorem is imported. Standard Ligozat formula plus the six explicit cusp arithmetic checks establishes holomorphy and strictly positive cusp orders, so f32 belongs to the genuine S₂(Γ₀(32)), not a polynomial approximation.

For Γ₀(32), index μ=32(1+1/2)=48, elliptic points e2=e3=0, and cusp count 8. The classical genus formula gives

    g(X₀(32)) = 1 + 48/12 − 8/2 = 1,

and standard canonical differential / weight-2 cusp-form correspondence gives dim S₂(Γ₀(32))=1. By the modularity theorem, the original E (conductor 32; same isogeny class) has a unique normalized Hecke newform fE in S₂(Γ₀(32)) whose a_n are the Hasse–Weil L-coefficients for ALL n including bad local factors. Both fE and f32 lie in the same one-dimensional genuine space and have q1=1; they must be the same holomorphic function and have equal **all-n** q-expansions, not just seven finite Frobenius traces or a numerical coefficient cutoff. Consequently:

    fE = f32,   L(E,s) = L(f32,s)  (initially Re(s)>3/2, then analytic continuation).

This argument has genuine external mathematical inputs: modularity, eta-quotient cusp criterion and modular curve genus/dimension; the new in-repo step is the exact source curve identity through a rational 2-isogeny and deliberate reuse of previously source-written finite integer certificates. It does NOT use arbitrary assumed coefficient equality or positivity as a premise.

## Dedekind eta inversion; real-axis identity (all t>0)

The established eta modular inversion is η(−1/z)=sqrt(−iz) η(z) (with canonical branch). On z=8it and z=4it, t>0, the square root is positive real. Squaring gives actual identities

    η(i/(8t))² = (8t) η(8it)²,
    η(i/(4t))² = (4t) η(4it)².

Thus for all t>0,

    f32(i/(32t)) = 32t² f32(it).

This is the TRUE source E-level32 Fricke reflection, not merely an algebraic equivalence conditioned on an unconstructed fake real eta. The analytic eta identity is imported from established Dedekind theory; the scale equality is exactly the previous source-written EllipticCMLevel32FrickeMellinExact.level32FrickeFromTwoEtaInversions compiler.

## Actual Mellin integral at s=1 and exact positive lower bound

For a normalized weight-two cusp form, the classical Mellin transform is

    (2π)^(−s) Γ(s) L(f32,s) = ∫_0^∞ f32(it)t^(s−1)dt.

This identity initially holds by q-series interchange on a suitable right half-plane and extends analytically because the cuspform and Fricke formula give exponential decay at t→∞ and exponentially small behaviour after t→0 inversion. Hence the original selected central L-value equals

    L(E,1) = 2π∫_0^∞ f32(it)dt.

Let t0=1/√32, the fixed point of t↦1/(32t). The exact real substitution u=1/(32t) plus Fricke yields

    ∫_0^t0 f32(it)dt = ∫_t0^∞ f32(iu)du,

and therefore the original selected SAME-CURVE exact integral:

    L(E,1) = 4π ∫_t0^∞ f32(it)dt.

Now write q(t)=exp(−8πt). For t≥t0, elementary π>3 and √2>4/3 give 8πt≥π√2>4; since e>2, q(t)<e^(−4)<1/16. The ACTUAL Dedekind eta product on the positive imaginary axis is

    f32(it) = exp(−2πt) P∞(q(t))
    P∞(q)=product_{n≥1}(1−q^n)²(1−q^(2n))².

For 0≤a_j≤1, Bernoulli product inequality (proved by finite induction) gives product_j(1−a_j) ≥ 1−sum_j a_j. Every finite eta product consequently obeys

    P_N(q) ≥ 1 − 2∑_{n≥1}q^n − 2∑_{n≥1}q^(2n)
           ≥ 1 − 2/15 − 2/255
           = 73/85 > 0.

For M>N the positive finite products are decreasing and their difference is at most

    delta_N =
      2(1/16)^(N+1)/(1−1/16)
      + 2(1/16)^(2N+2)/(1−(1/16)^2),

which tends to zero uniformly for all t≥t0. The genuine infinite limit therefore exists, equals the actual convergent eta product by the classical Dedekind definition, and satisfies P∞≥73/85 for EVERY real t≥t0. There is no finite-N extrapolation or unverified positivity of a Mellin integral here.

It follows pointwise and integrably that

    f32(it) ≥ (73/85) exp(−2πt)

and after integration:

    L(E,1) ≥ 4π (73/85) ∫_{1/√32}^∞ exp(−2πt)dt
           = (146/85) exp(−2π/√32)
           > 0.

This is the exact original S4 target and gives analytic rank ord_{s=1}L(E,s)=0 since the holomorphic continuation and nonzero central value are established. Optional classical cross-check: L(E,1)=B(1/2,1/4)/8≈0.6555143885730299526162098974727798534206887378579; the bound above is ≈0.5656581438846327033493061143 and suffices independently of the beta evaluation.

## Executed deterministic regression (byte-matched to source commit)

Repo script: scripts/check_clay_s4_original_level32_classical_20261116.py, Git blob **a9d11da2c4606a74e924cdbcdeda607ffe88e1a4**; executed locally under Python/SymPy 1.14 and mpmath 1.3 using identical file bytes.

    PASS exact selected E → E' rational 2-isogeny symbolic identity and quadratic fibre
    PASS 61 primes 3≤p<300: direct E(F_p), E'(F_p), and f32 pth coefficient match
    PASS 70 exact rational Bernoulli/eta-product lower-bound and tail cases
    PASS 7 high-precision original eta Fricke t↦1/(32t) sample comparisons
    PASS independent Mellin integral and B(1/2,1/4)/8 central-value cross-check
    PASS lower-bound arithmetic 73/85, 146/85 and L>positive bound

The regression is NOT a proof of the external modularity theorem, all-prime Euler equality, physical Mellin theorem or complete native Agda field transport. The UNIVERSAL classical argument above uses those trusted classical theorems and mathematical finite symbolic identities explicitly; the finite tests exercise exactly the new selected-curve bridge.

## Gate accounting and precise remaining original lemmas

**S4 CLASSICAL MATHEMATICAL CLOSURE under the already-authorized Python/classical protocol only.** It closes the original selected analytic target L(E,1)>0 with the correct full elliptic L-series by known mathematical theorems; it is not a new proof of the modularity theorem itself. For formalization, still missing: (a) Agda/Lean verified literal elliptic 2-isogeny as a true group morphism; (b) original analytic eta/cusp/level32 modular-form construction with proofs in pinned source; (c) fE=f32 equality typed to the literal cmWeierstrass L; (d) source-native Mellin/Fricke and Bishop positive integral; (e) pinned Agda/Lean kernel and full transitive proof/axiom audit.

**Do NOT CLOSE**:
- S1 actual real/Q₂ original E[2]-valued H¹ Kummer image/exhaustion;
- S2 classical Kummer exact LES and actual Sha[2];
- S3 arithmetic original MW rank zero via actual all-place Selmer and finite generation (even though selected analytic rank is now 0);
- S5 odd-primary Sha and full selected BSD period/Tamagawa/regulator leading-coefficient identity;
- S6 all curves E/Q and all ranks BSD rank equality and stronger full formula.

**Portfolio now:** 28 tracked gates, **7 settled classical/source decisions, 21 OPEN**, historical A–F remains **6/15 settled, 9 OPEN**, **0/6 original Clay theorems proved**. This is not 25% progress toward universal BSD. Closing S4 pays a real selected analytic L lemma and removes an analytic endpoint dependency for the selected CM laboratory, but cannot be promoted to universal BSD.
