**Additional exact source-written tree-level coupling seam:** `inverseCoupling54`, `inverseCoupling43`, `inverseCoupling32` and `treeLevelCouplingTowerCoheres` prove the *algebraic* coherence of `lambda_2 = L_3 L_4 L_5 lambda_5`, where `lambda_d=1/g_d^2`, on the rational zero-mode bookkeeping carrier. These are identities under assumed tree-level circle matching, **not** a nonperturbative threshold calculation, positivity/units receipt or 5D UV completion. Exact-head Agda kernel checking remains pending.

# The strongest DASHI five-sector YM / Lorentz / KK / gravity BIDI steelman
**Date:** 2026-11-03. **Status:** candidate complete-theory specification + finite source-written Agda proof; physical continuum and Clay claims are NOT closed.

## Abstract: an imagined complete theorem, without pretending to have proven it

**Conjectural complete result (the "year-3000" steelman):** There exists a single physical construction with a reversible microscopic history model, boundary-conditioned observable filtration, an intrinsically selected and time-oriented (3,1) metric, a reflection-positive 4D Euclidean Yang--Mills theory with a nontrivial continuum limit and strictly positive mass gap, a consistent low-energy Kaluza--Klein extension, and dimensionally reduced 3D and 2D regimes which recover the independently established gauge observables when the scalar/KK sectors and coupling/scale hypotheses match. Its gravitational and candidate repulsive phenomena arise by varying one effective action, with positive universal Newton coupling and physical quantum stress. Every comparison is made between identical selected observables in a matched theory, not between arbitrary theories that merely have the same dimensional label.

**The result above is a proposed theorem to PROVE, not a present scientific finding.** The existing Agda repository has extensive finite and conditional proof owners, not an accepted full constructive 4D YM or all-sector gravity solution. Clay still regards the 4D existence/mass gap question as open.

## 1. The selected microscopic-to-Lorentzian route

Choose a microscopic state space `Omega`, involution `Theta`, reversible dynamics `U_t` with `Theta U_t Theta = U_{-t}`, and two physically specified boundary conditions `B_-`, `B_+`. Let `F_t` denote the **actual accessible observer filtration** and `pi_t` the lossy measurement of a history. The future condition may change the smoother's inferred latent history without permitting intervention on a previously recorded observation.

The original finite history carrier `FiniteHistoryOrientationExact` proves time-reversal-invariant transition action and distinct future-conditioned hidden histories for the same past record. The original `HistoryWeightFiltrationExact` proves filtration asymmetry. `TSFVFiltrationArrowLorentzBridgeExact` proves that a deterministic coarse-past decoder cannot recover both selected histories. The shift pressure/MDL descent is **a different carrier**: `ShiftCollapseChainMDLCompatibility` must be mapped into the history dynamics with explicit transition and observation preservation. In fact, `globalStrictReversalRankImpossible` proves that a strict rank drop on every step of microscopic reversal is impossible (a fixed history is present). Thus the steelman permits irreversible effective **quotient semigroup** dynamics but not a fictitious strictly decreasing rank on time reversal itself.

The required mathematics is a **physical chosen state** `omega_*` and metric `g(omega_*)` for which an independently computed cone, dimension estimator, isotropy, unique time-axis and observed arrow select a one-time/three-space causal geometry. The exact continuum selector is still open; `LargePosetContinuumLorentz31`, `Signature31FromIntrinsicShellForcing`, `CausalForcesLorentz31` and the earlier dashifine numerical tests are donors. The selected positive future direction is distinct from the overall (3,1) versus (1,3) metric-sign convention. `SameMetricTSFVKK` already proves conditional transport of the **very same four-axis quadratic** into the selected KK 4D metric, but the actual physical inhabitant of its source fields remains to be built.

## 2. Five-dimensional candidate action and the 4D zero-mode theory

The strongest **candidate** physical action is an Einstein--Yang--Mills--matter effective action on a 5D Lorentzian product/compact circle domain, with one selected stress source:

```text
S_5[G,A,Psi] = integral_{M_4 x S^1} sqrt(-G) [
    (R_5 - 2 Lambda_5)/(2 kappa_5^2)
    - Tr(F_AB F^AB)/(4 g_5^2)
    + L_matter(Psi, G, A)
] d^4 x dy + S_boundary .
```

This is a **candidate EFT**, not a demonstrated UV-complete 5D QFT. The same `S_5`, and only source-pinned couplings and counterterms, determine the 4D metric/gauge sources and their stress. Use a KK metric ansatz (with explicitly chosen Einstein/Jordan frame and normalization)

```text
ds_5^2 = e^{-2 alpha phi} g_{mu nu} dx^mu dx^nu
       + e^{4 alpha phi} (dy + k B_mu dx^mu)^2 .
```

The zero-mode gauge field decomposition is `A_A -> (A_mu, Phi=A_y)`. Its 5D curvature yields a 4D Yang--Mills curvature plus a covariant scalar-derivative sector (and, when relevant, commutators/Higgs terms). The *gravitational* circle connection `B_mu`, the radion `phi`, and the *5D YM* scalar `Phi` are distinct fields. A pure-4D-YM truncation requires a consistent demonstration that each unwanted field is constrained, stabilized, decoupled, or explicitly retained. They cannot disappear because a six-plane calculation was embedded in a ten-plane carrier.

In a constant circle of circumference `L`, under zero-mode and canonical normalization and ignoring higher-loop thresholds:

```text
1/g_4^2 = L/g_5^2;   kappa_4^(-2) = L kappa_5^(-2).
```

The latter assumes an appropriate unwarped Einstein-frame reduction. The former is **tree-level matching only**. At energy much less than `1/L`, nonzero KK modes may be integrated out; their threshold corrections must be quantified. The 5D perturbative nonrenormalizability does not by itself invalidate the 4D *effective* YM sector. Conversely a 4D YM Clay theorem does not prove a 5D UV completion.

**Independent pure-YM / gravity decoupling test:** Clay's theorem is about a four-dimensional **pure Yang--Mills** quantum theory on its own, not simply a YM sector coupled to dynamical gravity or a light KK scalar. The steelman must separately prove that a selected decoupling limit (for example `kappa_4 -> 0` with the YM source and renormalization convention fixed) gives *the same pure 4D Wilson/Schwinger family* as the independent Clay construction. Only after this is established can the coupled gravity theory use the independent YM result as a source without claiming the gravity-coupled model itself is the Clay target. Quantitative control of radion/adjoint scalars, thresholds and backreaction is required.

The *Euclidean five-axis* Creutz lattice and this *Lorentzian compactified KK* system must stay typed as DIFFERENT constructions, as already proved by the Voyager dimension-fork finite classification. A 5D lattice phase transition is not a 5D continuum/KK theorem.

**New finite curvature accounting:** `YMClayFiveSectorBidiSteelmanExact.agda` explicitly enumerates ten 5D oriented planes, their six/three/one lower-axis subsets, and the cross-axis residue in each step. It proves `P_d=P_(d-1)+R_d` for d=3,4,5; and for nonnegative coefficient sums it proves `P_d=P_(d-1) => R_d=0`. An actual nonzero fifth-axis fixture has `P_5=1` and `P_4=0`, refuting automatic equal-action claims. Coefficients here are abstract Nat-valued plaquette costs, **not** a continuous physical Haar theory and **not** a raw 5D KK action. The current native SU(N) six-positive-plane, Wilson trace, C3 and Gibbs construction from #1444 is the physical source owner to which the finite accounting must be linked.

## 3. The nonperturbative 4D Yang--Mills / OS / mass-gap centre

The primary mathematical physics object remains a **standalone 4D Euclidean pure YM construction** over compact simple gauge group G. The selected finite Wilson family and counterterms are

```text
S_(4,a)[U] = beta(a) Sum_(x, mu<nu)
   (1 - (1/N) ReTr U_(mu nu)(x)) + S_counterterms(a,U)
```

with correct real compact-group link variables, normalized product Haar and gauge-invariant Wilson observables. The continuum Schwinger family must arise from a genuine *a -> 0* limit with compatible infinite-volume limits, OS positivity and nontriviality. The physical (3,1) theory is reconstructed on the **same selected** `H_OS`; Euclidean (4,0) and Lorentzian (3,1) Hodge-star square laws on 2-forms (+1 vs -1) are algebraic cross-checks, *not* the reconstruction map.

The expected nonperturbative dimensionful gap is set by dimensional transmutation, heuristically

```text
beta(g) = - b0 g^3/(16 pi^2) + O(g^5),
b0 = 11 C_A/3  (pure YM);
Lambda_YM ~ mu exp[-8 pi^2/(b0 g(mu)^2)] (one-loop convention).
```

A spectral theorem must show `spec(H_OS) subset {0} union [Delta,infinity)` with `Delta>0` uniform after the continuum AND infinite-volume limits, plus a physically nontrivial gauge-invariant Hilbert theory. The renormalization group/dimensional-transmutation equation alone does not prove this spectral claim.

**Live proof owners:** Bałaban's published stability and the original DASHI Round58/combined RG owners; `BalabanClayGate4CombinedRGUVIterationExact` (all-scale induction **conditional on true one-step analytic bounds**); `BalabanClayConcreteUVToMassGapDependencyExact` (conditional UV/continuum/OS/gap composition); Route-S #1440 `R320 -> R333`; Voyager #1444 six-plane Wilson/SU(N), finite Gibbs, and R443/R445 source bridge. The irreducible analytic leaves are genuine continuous SU(N) Haar/physical source, selected changing-cutoff R445 estimates, selected R320 source decay, physical OS `H_OS` spectral gap R333, and total group/nontriviality scope.

A proof of one-step RG stability plus an all-scale induction is **not** a mass-gap theorem. A large finite-box positive gap is **not** enough if its lower bound vanishes as box size diverges. Neither 3D nor 5D results waive these obligations.

## 4. Known 2D and partial 3D dynamics as independent backward consumers

**2D exact anchor.** In the scopes of Ashtekar--Lewandowski--Marolf--Mourão--Thiemann 1997 and other 2D YM sources, the full continuum Wilson-loop functional and Euclidean/Hamiltonian correspondence are known. On a simply connected planar simple-loop sector, with conventional normalized trace and Yang--Mills action normalization,

```text
  <W_R(gamma)> = exp[-(g_2^2 C_2(R)/2) Area(gamma)] .
```

Do not impose this simple formula on arbitrary self-intersecting loops, topologies or matter-coupled theories. A 4D->3D->2D compactification must reproduce the **correct 2D effective model**. Only after scalar and KK-mode truncation is justified can one demand coincidence with *pure 2D YM*. This makes 2D a **hard independently proved observable anchor**, not a shortcut to 4D existence.

**3D partial anchor.** Chandra--Chevyrev--Hairer--Shen (Inventiones Mathematicae 2024) prove a local renormalized stochastic YM--Higgs flow on gauge-orbit space. Chevyrev--Shen (ARMA, January 2026) prove uniqueness of a gauge-covariant mass renormalization. The 2D renormalized Yang--Mills Langevin invariant-measure theorem (Chevyrev--Shen, 2026) is a distinct, stronger 2D equilibrium result. These results independently test the *3D stochastic sector's* counterterms, gauge orbit and Wilson-loop behaviour, but they do NOT prove a global 3D stationary theory or the 4D Clay theory.

If `M_d x S^1_L` is reduced by a consistent zero-mode ansatz, the naive tree-level relation is `g_(d)^2 = g_(d+1)^2 / L`. Threshold effects and retained adjoint scalars must be accounted for; simply setting an arbitrary `A_y` to zero is not a proof.

## 5. Exotic gravity must be a single positive-G source-derived sector

The strongest repository-supported *candidate* is not a universal negative Newton constant. Use **one** metric-dependent quantum effective action `W[g,A,history]` and the local renormalized stress

```text
 T_eff(mu,nu) = -(2/sqrt(-g)) delta W/delta g^(mu,nu)
 G_(mu,nu) + Lambda g_(mu,nu) = 8 pi G_N T_eff(mu,nu),
 G_N > 0.
```

For FLRW homogeneous perfect-fluid regimes (and the stated GR/units conventions),

```text
 ddot(a)/a = -(4 pi G_N/3) (rho+3p) + Lambda/3.
```

Defocusing/accelerated expansion can occur through `rho+3p<0` or positive `Lambda`; a negative trace alone is insufficient to establish the needed active stress, nor does local outward acceleration imply a propagating TT gravitational wave. Energy conservation, quantum energy constraints, regular geometry, and observational bounds must all be maintained.

This directly reuses the *source-first* physical owners:
- #1120 `CMP119AntigravityLocalCWightmanDirectStressGeometryExact`, `AntigravitySameStateFourChannelDiscriminatorExact`; the preferred source is Local-C/Wightman typed stress, with actual normalization and apparatus scale outstanding;
- #1132 quantum birthmark/history/entropy-density to effective stress sign: Eq.(2.23) needs `N_V>0` and `N_ERB>=0` as selected source inequalities. Memory alone is not stress, nor is entropy density a law of gravitation;
- #1045 `AntigravityStrongestConditionalTheoremExact` distinguishes counterfactual negative-G fingerprints, material-effective sign hypotheses and unmanufactured empirical receipts;
- #1284 `AntigravityTOENonPromotionBridgeExact` proves non-promotion of negative trace, component-wise stress matches, gravitational waves and anomalies;
- #1241 same-action KK/E6/radion/stress and independent Earth-physics consumer steelman.

A *real* gravity prediction must be generated from the **same stress-derived metric** for weight/support, free fall, clocks and optical propagation; matched controls, physical unit scale and independent replication remain required. This is not an antigravity-device claim.

## 6. Formal BIDI: the consumer square and the permitted equality

The meaningful equality is **selected observable equality**, not "identical dynamics in every dimension". For a legitimate joint sector `s`, observable `O`, exact reduction `R` and selected reconstruction `OS`:

```text
 O( OS( YM_4^Euclidean(s) ) )
   = O( YM_4^(3,1)(s) )

 O( Red_S1( KK_5(s) ) )
   = O( YM_4^(3,1)(s) ) + eps_(O,KK)(s)

 O( Red_S1( YM_d(s) ) )
   = O( YM_(d-1)^(with scalars)(s) ) + eps_(O,d)(s)
```

The first equality requires selected OS axioms, analytic continuation and same `H_OS`. The second and third may have explicit low-energy, finite-radius, threshold and regulator errors and must not be made exact without their hypotheses. The 2D sector can act as a positive reference test; 3D local stochastic theorems are scoped partial references. Only matched common observables and couplings may be compared.

There is **no** generic demand that a pure 5D Euclidean Wilson system equals a Lorentzian 5D KK gravity theory. Likewise no equality between lattice UV scale, Markov stochastic time and the emergent observer's timelike coordinate.

The new `MatchedEuclideanGaugeTower` carries only selected adjacent observable equalities and proves their composition `matchedFiveToTwo`. It is a *conditional* transport theorem, paired with concrete finite curvature residual no-go laws. The existing `SameMetricTSFVKK` independently carries the physical 3+1 time/orientation weld. No fake global correspondence is inserted.

## 7. Strongest alternative steelman and falsifiers

**Independent conventional steelman:** 3+1 physical spacetime and causal orientation are empirical premises. Pure 4D Yang--Mills is defined through its Euclidean lattice-to-continuum constructive programme and OS reconstruction; KK remains an optional EFT with heavy modes and radion; vacuum energy/quantum stress may cause repulsive behaviour within ordinary positive-G Einstein dynamics. This alternative predicts all established low-dimensional results **without** claiming that an information-loss mechanism derives spacetime or solves the Clay gap.

DASHI wins only if it supplies **additional independently checked derivations and predictions**.

1. Finite history/filtration pressure state must give a physically selected, nondegenerate, dimension-4 Lorentz cone and positive-energy time orientation **without hard-coded signature, 4 axes or metric signs**.
2. The true selected metric must be **identical** through observer arrow, OS analytic continuation, KK reduction, and stress-energy variation. A matching label, component count or synthetic trajectory is inadequate.
3. The 4D physical SU(N) measure must have compact continuous Haar, true regulator/volume limits, nontrivial OS reconstruction and **uniform** gap. Positive finite-volume gaps or all-scale UV bounds alone fail.
4. Every claimed d->d-1 reduction must preserve all curvature/matter/scalar/Kaluza--Klein sectors or establish explicit zero/decoupling/threshold bounds. The 5D 10-plane finite no-go detects one lost class.
5. 2D planar Wilson area laws must be reproduced in the pure-2D admissible limit; 3D counterterms and gauge covariance must match their proven sectors. Failure is a genuine BIDI refutation.
6. Gravitational claims must conserve stress and pass a single-source four-channel metric test. A universal sign-flipped G that fails weak-field tests is not rescued by an exotic matter label.
7. Must quantify scale-order/noncommutation: `a->0`, `volume->infinity`, `L->0`, `stochastic_time->infinity` and `OS` cannot be swapped without a theorem.

## 8. Exact mathematical dependency cut

- **A / micro -> arrow -> metric:** source-native transition/filtration weld to shift/MDL; independent physical cone, dimension selection, metric calibration; inhabit `SameMetricTSFVKK`.
- **B / Yang--Mills Clay:** true R443 compact physical Haar and 4D literal selected Wilson; varying-cutoff R445 selected measure/tails; R320 CMP116 selected decay; R333 same-reconstructed-Hamiltonian positive uniform spectral gap and nontriviality.
- **C / 5D -> 4D:** one actual selected compactified action, radion/gauge/adjoint scalar content, fixed coupling conventions, source/stress/metric variation; controlled KK thresholds and known-test checks.
- **D / 4D -> 3D -> 2D:** selected compactifications with scalar sectors; Wilson observable algebra matches, lower-D 2D exact anchor and 3D local stochastic sector precisely scoped.
- **E / gravity / history:** actual Local-C/Wightman source variation, Eq.(2.23) sign inequalities if that branch is used, renormalization/scale, same metric four-channel predictions, observational calibration.

**Proof statuses:** the new ten-plane finite algebra, no-go and conditional transport are SOURCE-WRITTEN on PR #1460. Agda kernel acceptance is NOT verified. The UV/OS, selected KK, physical arrow and gravity production cuts remain uninhabited. No scientific breakthrough or future publication is claimed.

## 9. Attribution

- Yang--Mills: C. N. Yang and R. Mills; Wilson lattice and renormalization; Tadeusz Bałaban's original complete RG papers; Jaffe--Witten Clay statement.
- Euclidean/Lorentzian reconstruction: Konrad Osterwalder and Robert Schrader; standard Lorentz/Sylvester/Hodge differential geometry.
- 2D rigorous gauge theory: Abhay Ashtekar, Jerzy Lewandowski, Donald Marolf, José Mourão and Thomas Thiemann (1997).
- 3D renormalized stochastic YM--Higgs: Ajay Chandra, Ilya Chevyrev, Martin Hairer and Hao Shen (2024); Ilya Chevyrev and Hao Shen (2026). 2D Langevin invariant measure also Chevyrev and Shen (2026).
- KK field decomposition: Theodor Kaluza and Oskar Klein, with modern normalization/consistent truncation sources retained.
- Two-state vector framework: Yakir Aharonov, Peter Bergmann, Joel Lebowitz, and later Aharonov and Vaidman. `dashiQ/PHYSICS_TARGETS.md` retains original DASHI lossy-projection/MDL arrow priority.
- Positive-G gravity/defocusing: Einstein/Raychaudhuri and original quantum stress/renormalization authors; Jacobson/Verlinde remain distinct conditional traditions and are not equated.
- Existing DASHI original Agda/Lean finite theorem and proof owners retain their proofs. This addendum owns only the cross-sector proposed theorem, exact finite curvature accounting, falsifiers and source attribution map.

## External source calibration

- Clay Millennium Yang--Mills: https://www.claymath.org/millennium/yang-mills-the-maths-gap/
- Ashtekar et al. 1997 two-dimensional pure SU(N) Yang--Mills: https://doi.org/10.1063/1.532146
- Chandra et al. 2024 3D stochastic YMH: https://doi.org/10.1007/s00222-024-01264-2
- Chevyrev--Shen 2026 3D gauge-covariant renormalisation uniqueness: https://doi.org/10.1007/s00205-025-02163-3
- Chevyrev--Shen 2026 invariant measure of 2D YM Langevin: https://doi.org/10.1002/cpa.70043
