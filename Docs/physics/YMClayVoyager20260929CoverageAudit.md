# Voyager 2026 Yang–Mills coverage and Clay non-promotion audit

Date: 2026-11-01. Video: Voyager, *How Close Are We To Proving Yang-Mills and Mass Gap?*, 2026-09-29, https://www.youtube.com/watch?v=0EP_t9yuBiQ . Source is the supplied timestamped transcript, **secondary educational narration**, not mathematical authority.

This audit is **stacked on** Agda PR #1440 (Route-S R320→R333 and R445→native P2), starting head `6e9bcb01fd95ed935ee2e40ff7326df7df575f6c`, not a competing theorem owner. The golden module `DASHI/Physics/YangMills/YMClayVoyager2026CoverageExact.agda` encodes the chapter/scientific-sector/receipt map and two actual reuse theorem exports. Invariant 3D stochastic measure, Donaldson moduli, and four-dimensional Clay acceptance are not proved by this audit.

## Chapter-by-chapter exact crosswalk

Status legend: **F** = reusable source-written finite theorem or algebra; **C** = conditional compiler requiring physical input; **R** = typed receipt/physical proposal, not theorem; **X** = external research, *not imported as an Agda theorem*; **H** = historical context; **OPEN** = required mathematical/source work remains.

| Video time | Video claim / mathematical core | Reuse-first in-repo Agda owner or primary source | Status and exact remaining obligation |
|---|---|---|---|
| 00:48 Landau arrest | Landau, Kapitza, prison, later zero-charge pessimism | Biography: external historical claims; no mathematical primitive | H; distinguish Landau's 1950s QED concern from 4D non-Abelian YM. No proof claim from biography |
| 03:11 Landau pole | QED screening; positive perturbative UV beta, potential Landau pole / zero-charge | `DASHI/Physics/Laws/StandardModelLawBoundary.agda`; `BalabanClayOneLoopFlowRemainderExact.agda` | R; QED running and full nonperturbative QED triviality are different; the perturbative pole is not a proof of inconsistency or a YM obstruction |
| 06:04 asymptotic freedom | For pure SU(N), one-loop `mu dg/dmu = -11N g^3/(3*16*pi^2)+O(g^5)`; the full SU(N) + N_f fundamental-Dirac-flavour coefficient is `-(11N-2N_f)g^3/(3*16*pi^2)` | Gross–Wilczek PRL 30 (1973) 1343, DOI 10.1103/PhysRevLett.30.1343; Politzer PRL 30 (1973) 1346, DOI 10.1103/PhysRevLett.30.1346; `BalabanClayOneLoopFlowRemainderExact`, `BalabanClayGate4PrimaryBetaFiniteDifferenceExact` | F for an ordered-field one-loop *conditional step*, R for physical coefficient and higher-order bounds; not an unconditional nonperturbative YM construction |
| 10:37 two Clay demands | 4D nontrivial quantum pure YM on R4 for each compact simple gauge group; positive Hamiltonian spectral mass gap | Jaffe–Witten official Clay problem; `YMClayDirectSourceOSMassGapFrontierExact`, `BalabanOSMassGapClosure`, `YMClayFullPhysicalFormalismExact` | C/OPEN: actual selected continuum theory, OS axioms, vacuum nontriviality and same physical H_OS spectrum |
| 13:43 Wilson's magnets | Blocking/RG, scale-dependent couplings, critical correlation lengths | `BalabanClayOneLoopFlowRemainderExact`, `BalabanRGTOERegression`, `BalabanDyadicTerminalScaleExact` | F/C; finite-scale RG is not automatically an a→0 limit |
| 17:31 lattice gauge | Sites/edges, local G transformations, parallel transport, class-function Wilson loops, Euclidean lattice weights | `CompactLieLatticeGauge` proves path-holonomy covariance and closed-loop class-function gauge invariance; `BalabanLiteralRationalSU2WilsonBoundedAlgebraExact` proves literal rational SU(2) unit boundedness | F, *distinct finite carriers*. Physical Haar SU(2)/SU(3), Wick continuation, selected trace-to-measure, OS reflection positivity all require faithful same-object attachments |
| 21:28 strong confinement | Wilson loop W(R,T) ~ exp(-sigma R T); `V(R) = -lim_(T→infty) (1/T) log W(R,T) ~ sigma R` | Wilson, *Confinement of Quarks*, PRD 10 (1974) 2445, DOI 10.1103/PhysRevD.10.2445; `CarrierAreaLawTheoremReceipt`, `StrongCouplingExpansionReceipt` | R/OPEN: specify positivity, rectangle time limit, physical transfer operator, finite-to-continuum uniform string tension. External-heavy-quark area law is NOT identical to pure YM vacuum gap |
| 24:51 strong-vs-weak phase | Lattice strong coupling g large vs continuum asymptotically weak g(a)→0; a phase boundary could intervene | `BalabanSZZStrongCouplingDecisionExact`, `YMUniversalityClassReceipt` | F for selected SU(2) lattice normalisation and threshold decision; OPEN for physical path along a→0 with no transition and nonperturbative universality |
| 28:02 Creutz simulations | Monte Carlo: 5D SU(2) and 4D compact Abelian models show phase change, 4D SU(2) not observed; later fixed string tension study | Creutz PRL 43 (1979) 553, DOI 10.1103/PhysRevLett.43.553; **the separate fixed-string-tension 10^4-site paper is PRD 21 (1980) 2308**, DOI 10.1103/PhysRevD.21.2308 | X; computational measurements and finite parameter scans cannot prove absence of any phase boundary, a limit measure, or the physical mass gap |
| 30:15 continuum | `a → 0` with `xi_lattice=xi_physical/a → ∞`; dimensional transmutation produces scale `Lambda` while bare coupling →0 | `BalabanClayT5MassScaleDimensionExact`, `BalabanClayT5PhysicalMassTransportExact`, `BalabanClayT5PhysicalMeasureGramContinuityExact`; `YMClayLiteralWilsonP2NativeMeasureExact` | C/OPEN: precise same-source running `g(a)`, tightness/limits, regulator independence, OS axioms, nontriviality and four-dimensional Euclidean/rotational covariance |
| 33:26 Balaban / MRS | Finite-volume UV estimates versus unbounded spatial volume/IR; fixed IR cutoff does not discharge thermodynamic limit | Bałaban CMP 109 (1987), CMP 116 (1988); Magnen–Rivasseau–Sénéor CMP 155 (1993), DOI 10.1007/BF02097397; R320/R445/R333 | C/OPEN: MRS state a *basis for rigorous Schwinger-function construction* with fixed infrared cutoff, trivial topology and regularized axial gauge; do not silently claim all Clay conditions |
| 36:09 dimension | Polarisation count `d-2` (local free massless modes under usual assumptions); `[g]=(4-d)/2`; 2D/3D superrenormalizability vs 4D marginal bare coupling | `DASHI/Physics/Foundations/ParameterScaleTaxonomyExact.agda`, `BalabanClayT5MassScaleDimensionExact` | R; these are perturbative dimensional counts, not existence, gauge-orbit regularity or mass-gap results |
| 37:43 Parisi–Wu | Stochastic quantisation: formal Langevin `dA_s = -grad S(A_s) ds + noise`, with gauge covariance and counterterms; invariant law is required to identify the Euclidean measure | Parisi–Wu (1981); `CompactLieBiInvariantSkewLangevinExact`, `BalabanLangevinAnchoredInfluenceRound268Exact` | F for finite compact-Lie geometric cancellation; X/OPEN for renormalised continuum stochastic flow, same-law/stationarity and global stochastic time |
| 40:32 Hairer and 2024 3D | Regularity structures for local-in-stochastic-time YM–Higgs on gauge orbit state spaces, potential finite-time blow-up | Chandra–Chevyrev–Hairer–Shen, *Invent. Math.* 237 (2024) 541–696, DOI 10.1007/s00222-024-01264-2 | X; genuine externally proved **3D YM–Higgs local flow**; neither global invariant 3D YM probability measure nor 4D pure YM Clay |
| 43:15 January 2026 uniqueness | Unique gauge-covariant mass renormalisation/counterterm, controlled via regularised Wilson loops and short-time expansions | Chevyrev–Shen, *Arch. Rational Mech. Anal.* 250 (2026) 11, DOI 10.1007/s00205-025-02163-3 | X; not the uniqueness of a 4D YM quantum theory, nor proof of an equilibrium measure; no same-object transport to R445 |
| 43:31 instantons/Donaldson | 4D Hodge F=F^+ + F^- and ASD/SD instanton moduli distinguish smooth 4-manifolds; Freedman–Donaldson–Casson/Gompf lead to exotic R4 | `LieGaugeTheoryParity`, `YangMillsFieldEquationReceipt` and Hodge sources are *adjacent*, not an instanton-moduli theorem; original Donaldson 1983/Freedman 1982; Gompf 1989 survey | X/OPEN: classical elliptic PDE, moduli compactness/transversality, topological vs smooth comparison, and exotic-R4 theorem require distinct owners. Do not infer 4D quantum mass gap from classical instantons |

Note: 2026 Chevyrev–Shen also establish **invariance of the known 2D YM measure** for the renormalised 2D Langevin dynamic (CPAM, first published 26 March 2026); valuable as a *same-dimensional* stochastic identification template, **not** 3D/4D transfer.

## Formal max-cut, with quantified same-object conditions

Let `a` be lattice spacing and `L` the physical box size. Let `mu_(a,L)` be a genuine selected gauge-field probability law on one observable algebra, `W_C` its literal Wilson-loop functions, and `H_OS` the Hamiltonian of its eventual reflection-positive infinite-volume continuum Euclidean theory. The correct semantic chain is:

1. **Finite algebra:** class-function holonomy gauge invariance; literal bounded Wilson products and identity; finite reflection positivity where available. These are *not* full continuum axioms.
2. **Selected physical measure:** construct `mu_(a,L)`, its action and bounded-moment estimates on the *same* loop algebra. For the native R445→P2 route this is the specific remaining nontrivial source payment.
3. **UV:** prove a→0 convergence/tightness at fixed L, including nontriviality and regularisation independence (or explicitly state what is and is not proved).
4. **IR:** prove L→∞ with *uniform*, compatible estimates and Euclidean symmetry/OS reconstruction on a single limiting algebra; control interchange of limits if used.
5. **Mass gap:** for one actual reconstructed self-adjoint H_OS, prove `spec(H_OS) intersect (0,Delta) = empty` and positive Delta with vacuum excluded from the excited spectrum. Finite boxes may individually have `Delta_L > 0` while `inf_L Delta_L = 0`.
6. **Clay group/target:** demonstrate the actual compact-simple-group scope, nontrivial quantum YM and official statement equivalence. A conditional R333 type is not automatically a Clay result.

An elementary countermodel to the invalid finite→uniform step is `Delta_L = 1/L` for `L = 1,2,...`. Every finite volume has positive gap, but no volume-independent `Delta > 0` exists. The new generic Agda theorem formalises **the valid forward direction only**: a uniform positive bound plus monotonicity implies pointwise positivity. A rational instance / constructive countermodel in the exact energy scalar remains a separate kernel-level improvement.

### New source-written Agda boundary

`YMClayVoyager2026CoverageExact`:
- enumerates each semantic chapter with its **scientific sector**, actual repository owner/source and precise unsettled boundary;
- reexports the native **configuration-dependent rational SU(2) literal Wilson pointwise bound**, rather than adding a surrogate constant quaternion;
- proves `nativeP2NeedsNoSupportDistance` from the actual P2 producer, so distance/time remains a separate P1 concern;
- proves `routeSStillNotClay` from the current authoritative Route-S owner;
- gives `UniformGap` and the valid generic `uniformGapImpliesFinitePositivity` implication;
- separates a finite-time stochastic Markov flow from the *strictly stronger* requirement for all stochastic times, an invariant distribution and same-flow law. `globalFromInvariantMeasure` only extracts a required hypothesis; it does **not** create a 3D stationary measure.

This is a genuine integration/crosswalk, not a kernel-verified claim in this connector-only run.

## Pareto next cuts (do not widen to an unrelated programme)

**P0 — native P2 physical source:** populate R445's genuine selected four-dimensional continuum bound/moment realization, including literal observable/measure identity. Do not spend another proof on the already owned finite rational loop bound.

**P1 — direct Route-S spectral identification:** selected H1 source inequality on literal CMP116/119 Wilson physics; physical R333 time/Wilson/limit closure; prove selected covariance operator spectrum equals the *actual* reconstructed H_OS spectrum. Keep a uniform positive physical Delta.

**P2 — regulator and infinite-volume limits:** UV/IR same-family commute or chosen iterated limit with stability, OS axioms and nontriviality; universality and compact simple group scope.

**P3 — stochastic BIDI donor (separate lane):** import **as external source** 2024 local 3D YMH and 2026 uniqueness, then express global-time, gauge-orbit invariant-law and same-Wilson-observable interfaces. Compare 2D known invariant-measure theorem. Never treat stochastic time as a fourth physical spacetime coordinate.

**P4 — Donaldson/classical 4D donor (separate lane):** reuse current Hodge/curvature owners for a 4D Hodge-star eigenbundle, ASD/SD condition, instanton-moduli sources and smooth-structure nonpromotion. No physical mass-gap promotion.

## Attribution and verification ledger

Original science: Landau/Pomeranchuk (historical perturbative QED concern); Gross–Wilczek and Politzer (1973 asymptotic freedom); Wilson (1974 lattice gauge / 1982 RG recognition); Creutz (1979/1980 simulation); Bałaban (1985–1988 multiscale); Magnen–Rivasseau–Sénéor (1993 fixed IR); Parisi–Wu (1981 stochastic quantisation); Hairer (regularity structures), Chandra/Chevyrev/Hairer/Shen (2024 3D local YMH); Chevyrev–Shen (2026 3D counterterm uniqueness/2D invariant measure); Donaldson, Freedman, Casson and Gompf (smooth four-manifold results); Jaffe–Witten (Clay specification). Voyager is credited for the curated video, not for these theorems.

DASHI independently owns *its own* Agda proof expressions and source-to-consumer routing. Ibrahim / Monster-3B / broader geometry provenance is unchanged; no synthetic or analogous identity is upgraded to physical same-object authority.

Validation status: **source-written; exact-branch readback pending; no Agda binary/kernel/CI here; no proof of Clay acceptance.** Do not describe this audit module as Agda-kernel-checked merely because it has `--safe`.


### 1 November classical Hodge completion (finite Euclidean basis only)

Source-written Agda `DASHI/Physics/YangMills/YMClayVoyagerR4HodgeBasisExact.agda` now provides a nontrivial new finite *four-dimensional* classical theorem donor distinct from the pre-existing selected 2D Hodge lower-candidate: six oriented orthonormal two-form labels `e01,e02,e03,e12,e13,e23`, signed star images `*e01=e23, *e02=-e13, *e03=e12` and reverses, a sign flip involution, and twelve exact signed-basis `*²=+1` equations. This uses the **Euclidean** four-dimensional orientation; Lorentzian four-dimensional Hodge on real two-forms has `*²=-1` under the usual signature convention. The resulting algebra does **not** supply a metric connection/curvature, linear 2-form extension, `F^±` projectors, instanton moduli, Donaldson smooth classification or quantum theory. It is source-written, not Agda kernel-checked.

### Physical interpretation corrections

The video occasionally compresses distinct statements. Euclidean Wick rotation gives formal weights `exp(-S_E/hbar)` under suitable analytic assumptions; it does **not** alone prove a positive gauge-invariant measure or OS reflection positivity. The original four-dimensional Clay problem is about **nontrivial quantum pure Yang-Mills**, not the existence of arbitrary four-dimensional quantum field theories (free fields are mathematically well-defined). Similarly pure YM glueballs/observable excitations, QCD with quarks, and static external-quark confinement are not definitionally the same object. A lattice Wilson loop's normalized trace being bounded is not yet the theorem that its continuum expectation obeys the correct large-distance rate.


## 1 November — requested full cross-domain symmetry follow-up

The requested deeper source read is in [YMClayVoyagerCrossDomainSymmetryMaxCut20261101.md](YMClayVoyagerCrossDomainSymmetryMaxCut20261101.md), with exact module/PR paths for complex and imaginary `J²=-1`, SO2/SO3/Spin, 3+1 signature source/reconstruction status, C3 CMP119 physical field/stress, 27→729→19683 coarse/fine refinement, actual vs analogous Wilson holonomy, Markov kernel vs Markov inequality, 2D/3D/4D/5D comparison, KK/EM5, QCD/E6/Casimir/GRQFT and proposed same-`H_OS` spectral ζ bridge. The video itself does **not** mention zeta.

New finite/source-typed Agda `YMClayVoyagerImaginaryC3DimensionBidiExact` proves signed-axis quarter turn square=antipodal, order four, C3 order three and the sharp no-equivariant-map result between the specific free three-cycle and quarter-turn four-cycle. It does not forbid a 120° C3 subgroup of physical SO2 or become a complex analytical field by itself. Actual complex pair/unit belongs to the older `ConcreteComplex` owner.

New `YMClayVoyagerDimensionSignatureForkExact` distinguishes 2D/3D/4D/5D YM coupling mass exponent `(4-d)/2`, Creutz 5D Euclidean lattice versus dynamical KK 4+S1 versus 3D artificial stochastic time, and 4D Euclidean versus Lorentzian 3+1 as different model constructors. Full KK source/action/radion/EM/gauge/spectral compatibility remains a typed uninhabited input.

The most important older **already-real** C3 owner is `BalabanC3MonsterEquivarianceAuditExact`, which itself reuses `CMP119FlatSide4SpatialC3FieldCovarianceExact` on the literal side-four SU2 bond field and plaquette curls, plus classical curvature and stress. It marks physical nonlinear generated-action same-object continuation and C3 on *every* intermediate recovery carrier as OPEN. Do **not** replace it with an arbitrary C3 phase chart. Use `BalabanWilsonTransferBlockingExact` for the selected OS pullback compatibility theorem. Separately #1249 proves a genuine finite 27/729/19683 path-graph gauge-covariant projection result with negative controls, **not yet this continuum YM object**.

The `dashifine` signature experiments are real, but the current Agda orbit-profile unique-31 proof includes a **signature tag in its profile** and is conditional on the observed profile; it is not an independent physical derivation. Remove the tag and prove objective physical signature discrimination before promotion.

This corrects the earlier completeness claim: **topic coverage is now much broader, but full use of existing symmetry for the selected 4D physical theory is definitely not finished.**
