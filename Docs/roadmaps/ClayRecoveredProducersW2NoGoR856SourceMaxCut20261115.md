# Clay × TOE: recovered original producers, falsified routes and exact remaining maximum cut
**15 November 2026.** Primary destination: [Agda Clay #1499](https://github.com/chboishabba/dashi_agda/pull/1499); Lean native donor [#108](https://github.com/chboishabba/dashi_lean4/pull/108); TOE front-end [Agda #1393](https://github.com/chboishabba/dashi_agda/pull/1393). No donor PR merged to master. Source Git blobs are retained without changing their original mathematical authorship. No newly solved Millennium problem is asserted.

## A. Significant corrections from older PRs

### NS.B: unconditional R734/R735 W2 is *false*, not simply OPEN

Primary original countermodel owner [Agda #1271](https://github.com/chboishabba/dashi_agda/pull/1271), source:
`Docs/research/ns_r734_pure_plus_physical_w2_no_go_20261027.md`,
`tests/test_ns_r734_pure_plus_physical_w2_no_go.py`,
`NSTriadKNR650AugmentedCriticalWeightedNormalFormRound734Exact.agda`.

For classical projected 3D periodic Navier–Stokes at the literal cutoff N=2,
take the real six-mode divergence-free initial field with positive helical projectors at
p=(1,0,0), q=(0,1,2), k=(1,1,2) and negative conjugate modes.
The exact original dyadic weight gives
$$
X(0)=8,\quad D(0)=36,\quad
P(0)=\frac{5+\sqrt5-\sqrt{30}}{10}>\frac3{20}.
$$
At amplitude a=512 and viscosity ν=1:
$$
X'(0)=a^2(aP(0)-72)>a^2(24/5)>0.
$$
The mixed positive/negative initial work and its first derivative vanish. The R734/W2 residual derivative is therefore positive for every δ>0. Smooth finite-dimensional Galerkin ODE and continuity give a short T>0 where **unrestricted R734 W2 fails**. This refutes a particular auxiliary inequality on actual original physical data, **not** the NSE solution/regularity claim.

The retained correct conditional R735 compiler W1+W2→critical barrier is not a general theorem, since one premise is false on some admissible source data. Do not task a theorem search with `originalR406R98PositiveMarginStrictSurplus` or `originalR736W2AllData` as if the prior universal conclusion were achievable. The repaired route uses Waleffe 1992 helical calculus and the original R92/R102 identities:
$$
X_{\mathrm{dyadic}}=H_{\mathrm{signed}}+
2M_{\mathrm{negative}}+R_{\mathrm{weight\ defect}},\qquad
R_{\mathrm{weight\ defect}}=
\sum_m (w_m-|m|)(e_m^++e_m^-).
$$
R734 now carries original Agda ring proofs of the finite rational algebra; transporting the actual irrational |m| and nonlinear tangent into the physical source remains OPEN. The source also retains the valid small-H1 residence/late-time analysis and its limitation: it does not control arbitrary-large-data early/middle critical work.

**Replacement NS.B physical producer targets (not previously proved):**
- `originalR734ActualHelicalDyadicDefectSameSource`: same Fourier cutoff, real/complex conversion, exact curl eigenvalues, and dyadic w versus |m| (W/F).
- `originalR734NegativeHelicityAndDefectSignedProductionBound`: noncircular cutoff-uniform signed physical production, rather than false universal W2 (N).
- `originalR736W1OriginalWeightedWorkPayment`: source W1 on actual dynamics (N).
- `originalNSBContinuationFromValidSignedBarrier`: an actually true combined critical barrier and uniform continuation (N).
The original R666/R598 bad-collar equivalence and R657 pure-frequency-sign no-go remain valid negative controls; there is no third automatic positive-margin theorem.

### NS.A: q-gain is already mathematical source, only physical identity + integration remain

Existing Golden owners:
`NSWholeSpaceR3DirectionalSecondMomentQGainExact.directionalSquareBelowNormProduct`,
`NSWholeSpaceR3PhysicalQBudgetCompilerExact.secondMomentCarriesRadialQ`,
`NSWholeSpaceR3CanonicalProjectedQBudgetExact.canonicalProjectedInputsBuildRadialBudget`,
`NSWholeSpacePhysicalMajorantDominationProducerExact.physicalMajorantDomination`.
These already prove the Lagrange/Cauchy q factor, conditional projected q×q budget and domination compiler. Lean #11 additionally proves fixed-output L²×L²→L¹ and bounded multiplier preservation.

**Exact missing physical instances:** (A1) selected signed second-moment scalar equals the directional square on the same Fourier interaction; (A2) selected physical Gram scalar equals the projected-cell energy and continuous FTC produces the derivative slot; (A3) the low/high physical convolution envelopes are actually integrable on the same Euclidean trajectory, with radial/Fubini and finite-energy continuation. A generic directional-square bound does not identify an arbitrary physical scalar. Existing `clayPromotion=false` and no new uniform regularity.

### NS R853/R854/R855/R856: exact source maximal affine headroom

Original R829 selected constants:
$$
r_0=-\frac{28273644}{125},\quad
L=391309593930357307785216,\quad
T=\frac{226189}{3938540454339300631433585885184}.
$$
Since L,T>0, for any scalar multiplier a≥0,
$$
r_0+aLT<0\iff
a<\frac{-r_0}{LT}=\frac{284574905427456}{28273625}
\approx10065030.76374027.
$$
For the integrated affine envelope,
$$
r_0T+\tfrac12 bLT^2<0\iff
b<\frac{-2r_0}{LT}=\frac{569149810854912}{28273625}
\approx20130061.52748.
$$
**Optimal integer safe coefficients are 10065030 and 20130061; the next consecutive integer yields a positive affine quantity in both cases.** Exact rational SymPy checks have PASS receipts. Source-written Agda R856 four strict neighboring inequalities and Lean `nsR856LargestPointwiseCapNegative`, `nsR856LargestIntegratedAffineNegative`, and a conditional real-time consumer are included in their canonical rollups. This is an optimal scalar bound for the fixed original r0,L,T, *not* an estimate on actual R853 r'(t). All such source-language typechecking and transitive axioms are still to be checked on Agda 2.9 and Lean 4.28.

The actual R71/R74 complete-real vector-field identification, Galerkin solution on fixed T, exact R853 observable on that solution, and any true derivative bound below the R856 scalar cutoff remain the live B/short-time physical premises. R855 and R856 avoid an unnecessarily sharp R828 Lipschitz constant but cannot create the real flow.

### YM: physically useful finite Gibbs locality from #1503 R445 prior art

Published mathematical principle: finite-volume Gibbs/Markov-field conditioning; source original Wilson normalized Haar/plaquette action. For an interior X, exterior Y, a finite product-reference law whose action splits as S(x,y)=S_touch(x,y_near)+S_out(y) has conditional density
$$
K(x\mid y)=
\frac{\exp[-S_{\mathrm{touch}}(x,y_{\mathrm{near}})]}
{\displaystyle\int \exp[-S_{\mathrm{touch}}(x',y_{\mathrm{near}})]\,
d\mu_X(x')}.
$$
The exterior-only `exp(-S_out(y))` cancels, so changing a far exterior link outside every plaquette meeting X leaves the **bare local conditional** kernel identical. No independence of the outside marginal is needed. A finite model exact SymPy/Fraction test checks 32 such far changes, with nonzero near influences, and 729 exact positive Gibbs reweightings confirming the existing sharp likelihood-ratio bound.

Lean #108 source-written `Synthesis.YMFiniteRangeGibbsExteriorCancellationExact` proves the normalized *finite-sum* version (source status only, kernel pending). This is **not** the SU(N) compact-Haar version nor the blocked effective Wilson conditional. The physical identity of the actual coarse F19 bare plaquette incidence, normalized Haar, finite coupling and locality radius must be welded; the blocked effective action has long-range polymer corrections. No claim of cutoff-uniform TV, nontrivial continuum or YM mass gap follows from exact cancellation of distant bare terms.

The larger historical donor chain is **already on the Clay rollup**: Agda `YMClayR445OneLocalTVThreeMomentsSourceWeldExact`, `YMClayRouteSH1DirectSelectedMarkedDecayExact`, `YMClayRouteSH1ModeSelectedContinuumUpperExact`, `YMClayDirectSourceOSMassGapFrontierExact`; Lean `Welds.YMSourceClusteringGap`, `Welds.YMClayAssembly`, `Welds.YMVacuumGapBackwardBounds`. **Do not request a new spectral-gap implication.** The real donor is an actual physical selected T5 R320 mixed-log response `DirectSelectedT5MarkedDecayPayment`, OR a valid interacting R445 conditional-kernel mismatch/summable coupling, plus same-source continuum/OS. The exact original f9e/OAI YM A7/A8 carrier transports remain independent formal verification.

### P vs NP: 172 missing PR #1129 source files now *actually coalesced*

GitHub tree-object import into Agda #1499 from [Agda PR #1129](https://github.com/chboishabba/dashi_agda/pull/1129), commit `5a5d1de6bd649a1e5d18c8d420449b5d9240308a`: 172 changed `DASHI/Mathematics/Complexity/` source files previously absent, with zero existing-path conflicts and original exact Git blob SHAs. This includes `PNotEqualsNPResourceClosingBudgetNecessityExact`, `PNotEqualsNPCodedLiteralResourceCompilerAnchoredNoGoExact`, `PNotEqualsNPStandardMachineMaxCutClosureExact`, streaming Cook-Levin/bit-code, concrete finite-TM simulation and quotation/clock structure. Source admission **does not imply kernel checks or positive lower bounds**.

Crucial already-existing `PNotEqualsNPQ1TerminalSemanticsDecisionFailureExact` proves Q1 opposite-terminal semantics are extensionally an actual SAT decision failure; the resource self-quotation work includes a no-go for positive fixed Cook budget. Neither is a construction of `UniversalPolynomialSATDecisionFailure`. The universal forall-decider/exists-formula lower bound remains independent OPEN; no fixed-instance forall-decider quantifier swap.

Other original Karp-21 F1/F2/F3/F4/G2/G3/G4 and actual OAI SAT primitive bit/clock transports remain source/kernel/implementation gates, not a universal P≠NP proof.

## Donor source attribution, verified content identity and exact acceptance

- PR #1271 W2 countermodel research and Python test imported verbatim; R734 full older theorem-owner blob `74877d3c783c3f9e7634c4c521536ce99197e067` restored, R735 current conditional compiler retained with explicit physical counterexample warning. Donor R735 comment is now also in current Clay root.
- PR #1129 172 blobs staged atomically with their original file paths. No donor commit rewrote legacy primary-source authorship.
- Existing Agda #1503 R445 local-TV three-moment source is identical in Clay (blob `9e97eac7cd2e2de1989e699b3e53fc98d77578e3`); existing Lean #7 source-clustering and assembly are byte-identical in #108. Do not recopy those.
- Agda `scripts/check_clay_source_r855_wilson_locality_20261115.py` reports 729 exact finite Gibbs cases, 32 far conditional comparisons, two positive near controls, four R856 strict neighboring bounds, and a q-slot identity negative control. SymPy 1.14.0 local independent receipt passed. Historical original W2 donor test contains 12 exact tests; an independent local six-mode source replay returned PASS.
- Source/verification separation: user runtime has no Agda/Lean/Lake/Nix and cannot clone GitHub. **No actual new kernel acceptance**; source modules may need elaboration fixes. All direct C/D OpenAI NS claims still need exact pinned f9e Lean external project and independent physical source review.

## Revised physical research priority (never assume a target in its own premise)

1. **NS.B first:** stop universal R734 W2; try the true R92/R102 helical signed source + negative-helicity production + dyadic defect on the actual R408 trajectory, while retaining original R736 W1. A universal proof is not obtained from the falsified inequality.
2. **NS.A:** produce the true selected second-moment directional identity, actual source low/high envelope and Fubini for one trajectory before any all-data continuation.
3. **YM:** either the original R320 direct selected mixed-log response shell bound or the true R445 blocked-effective/bare-local conditional mismatch and polymer influence *with physical uniform constants*. Then exact OAI E1/same-H identity and continuum mass gap; stop duplicating conditional gap compilers.
4. **P≠NP:** exact original bit implementation/clock and OpenAI #SAT machine source/bit transport; separately universal lower-bound theorem. The #1129 negative controls prevent a circular self-quotation shortcut.
5. **Verification:** kernel-check Golden Agda 2.9, Lean 4.28, OAI YM 4.32, NS 4.34.0-rc2 and SAT 4.34.1 with their respective pins; audit all transitive axioms and physical hypotheses. Never promote source-written or SymPy testing to a Millennium proof.
