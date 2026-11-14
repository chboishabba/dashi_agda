# Bishop eta / native factorial complex exponential — actual cross-PR source weld

**Date:** 2026-11-13  
**Destination:** PR #1478 `chatgpt/analytic-j-tetration-abel-transport`  
**Original eta donor:** PR #1408 at `28d85aa529155352a025de9e12853ecad1e4214e`.  
**Status:** source dependency closure transferred; new same-source term proof written; **Agda 2.9 kernel OPEN**.

## Exactly what changed

The following 10 original PR #1408 files were transferred **verbatim** into PR #1478 (verified against both GitHub blob SHAs, 10/10 identical):

1. `DASHI/Analysis/BishopRiemannDirichletBaselSameObjectExact.agda`
2. `DASHI/Analysis/BishopRiemannAnalyticSetoidExpReuseExact.agda`
3. `DASHI/Foundations/BishopNegativeLogGeometricSourceConvergenceExact.agda`
4. `DASHI/Foundations/BishopRound11TrigAtZeroExact.agda`
5. `DASHI/Analysis/BishopDirichletUniformBaselTailsExact.agda`
6. `DASHI/Analysis/BishopRiemannDirichletExponentialTermExact.agda`
7. `DASHI/Analysis/BishopOriginalDirichletEtaFinitePairingExact.agda`
8. `DASHI/Analysis/BishopOriginalXiPolynomialReflectionSameCarrierExact.agda`
9. `DASHI/Analysis/BishopOriginalEtaZetaEvenCutoffSeriesWeldExact.agda`
10. `DASHI/Analysis/BishopOriginalEtaEvenSourceScaleFiniteWeldExact.agda`

**Direct import audit:** all 35 distinct DASHI modules imported externally by the transferred source files and their new consumer resolve at the #1478 destination head. This is a **source presence** audit only, not a proof of Agda elaboration or transitive axiom freedom.

The new `DASHI/Analysis/BishopOriginalEtaNativeFactorialExpSourceWeldExact.agda` connects `BishopOriginalDirichletEtaFinitePairingExact.OriginalRound11DirichletEta.sourceTerms` to the **actual original native Bishop complex factorial exponential** using `BishopComplexExpFactEqualsNativeExpExact.originalBishopExpFactEqualsNativeExp`:

- `actualOriginalEtaExponentialRealIsNativeFactorialLimit`
- `actualOriginalEtaExponentialImagIsNativeFactorialLimit`
- `actualOriginalEtaTermFactorialSeriesConverges`
- `OriginalRound11.originalRound11EtaTermIsNativeExpReal`
- `OriginalRound11.originalRound11EtaTermFactorialConvergence`

The argument of the factorial expansion is specifically the original
`Terms.bishopNegativeSLn Terms.sourceCanonicalNatLogCandidate s n`.
Both native exponential results and the Dirichlet eta term use the
same vendored Bishop-real coordinates, despite different Cartesian
complex record constructors. The conversion is definitional, rather
than an unproved equality-reflection or a new abstract complex carrier.

## Exact remaining mathematics (do not promote)

The original `BishopOriginalEtaEvenSourceScaleFiniteWeldExact` already proves:

```
OriginalDyadicSourceScale (Selected.sourceTerms s) scale
  -> eta_(2N) + scale*zeta_N + scale*zeta_N ≈C zeta_(2N).
```

The antecedent is NOT derived by the factorial/native exp convergence theorem. To discharge it, the actual original canonical natural logarithm and native Bishop exponent must satisfy, for the chosen term `a(k)=exp(-s L(k+1))`:

1. The original `L(2(k+1)) ≃ L(2)+L(k+1)`, not a generic abstract `log` record.
2. Genuine multiplication of the same complex native exp: `exp(z+w) ≈C exp(z)*exp(w)` and distributive `-s` law on those original Bishop complex reals.
3. Therefore the literal dyadic source identity `a(2k+1) ≈C a(1)*a(k)` with `a(1)=2^{-s}` on the original selected source. This is the first **unpaid mathematical** interface after the source transfer.
4. A proper compact-uniform eta Cauchy bound for complex `s` with real part bounded below by a **positive** `σ`, with `|s|` controlled on the compact set; a naive real alternating-series estimate is insufficient.
5. Original zeta analytic identity on the appropriate connected half-plane, including handling `1-2^{1-s}` zeros/removable singularities, and any RH-specific analytic wall separately.

**Do not infer** the eta factor, compact-uniform convergence, original zeta continuation, Weil positivity, or RH from the finite eta algebra or termwise exp equality alone.

## Acceptance, runner, authority

Run locally on PR #1478:

```sh
bash scripts/check_bishop_eta_native_exp_cross_pr_local.sh
```

It checks 12 source roots with the existing project Agda 2.9 runner. Respects AGDA_BIN, PATH Agda, Nix fallback; no CI or Docker. It fails closed if the toolchain is missing. The kernel was NOT run during this transfer because Agda/Nix was unavailable in the assistant runtime. Source readback: 10 imported blobs exact, 1 new explicit proof consumer with no explicit postulate/hole in its text.

## Cross-programme provenance

See PR #1499, `Docs/roadmaps/DASHIAllLaneSourceDonorMaxCut20261113.json`. Source status has changed from "not co-located" to "co-located and source-written", **not** "Agda accepted" or "analytic theorem closed". The other Karp, BSD, NS, RH, Hodge, YM, Lean-world, Monster, biology and Cybersyn owner records retain their independent mathematical/empirical obligations.


## 14 November: exact original dyadic two-leaf source reduction

**New actual proof source** `DASHI/Analysis/BishopOriginalEtaDyadicSourceLawReductionExact.agda`, committed on #1478. This is in addition to the 10 original #1408 transferred files and their direct same-term native factorial exp consumer.

- `OriginalDyadicNatLogLaw`: exact still-OPEN original `Terms.sourceCanonicalNatLogCandidate` source law `L(2(k+1)) ≃ L(2)+L(k+1)`, with `suc (Eta.twice k)` as the actual zero-based even-positive source index.
- `OriginalBishopAnalyticExpAddLaw`: exact still-OPEN additive-to-multiplicative theorem for `ExpBridge.bishopAnalyticComplexExp T` on the original Bishop/Riemann complex carrier; it is NOT a new exponential or foreign `ConcreteComplex` constructor.
- `originalDyadicNegativeSLogIsSum`: source-written **both-coordinate Bishop real ring/distributivity proof**, deriving `-s*L(2(k+1)) ≈ -s*L(2)+(-s*L(k+1))` from the first explicit analytic leaf.
- `originalEtaDyadicScaleFromLogAndExp`: source-written composition of the preceding exponent identity, genuine `ExpBridge.bishopAnalyticExpCongruent`, and the second explicit analytic leaf. Its target is the PRE-EXISTING `Scale.OriginalDyadicSourceScale` for the ORIGINAL `Terms.bishopDirichletExponentialTerm T logNat s`, not an independent replacement of the source.
- `OriginalRound11.originalRound11EtaZetaFiniteFromTwoLaws`: actual selected Round11 `Selected.sourceTerms`, with scale EXACTLY `Selected.sourceTerms s (suc zero)` (the literal source `a_s(1)=exp(-s L(2))`). Reuses `Scale.OriginalRound11.actualOriginalRound11EtaFiniteScaleBridge` for **every** finite cutoff on the same Bishop carrier.

**Max-cut status:** the finite dyadic implication is now reduced to two named UNINHABITED original analytic laws, rather than an unspecified arbitrary source scaling premise. This is mathematical implementation of a conditional reduction, not proof of the log law, exp multiplication, full dyadic identity or infinite eta convergence. Local Agda kernel receipt still OPEN. The dedicated checker registers **13** targets; the larger Bishop golden checker registers **100** targets, neither count implies successful checker execution. P1.L's source-written original 8/27 inequality remains dependent on `R4.BishopSquareRootCalculus`, so no change to Newton, Koenigs, Kneser, or RH terminal gates.

**Highest-information next proofs:** (1) prove the original Nat-log multiplicative law from the selected convergent `-log(1-x)` coefficient series, including the configured elementary-data setoid identification; (2) prove the original native Bishop sine/cosine addition laws, and combine them with the existing Bishop real exponential Cauchy-product law into `OriginalBishopAnalyticExpAddLaw`; (3) inhabit the two leaves, then construct a valid complex compact-uniform eta Cauchy tail. The source-only checker must be run with pinned Agda 2.9 before any acceptance claim.
