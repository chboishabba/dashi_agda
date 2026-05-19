# Physics Recovery Ledger

This ledger records the current repo-native recovery status for the main
physics targets a serious reader will ask about. The statuses use the same
claim ladder as the rest of the physics docs:

- `proved`
- `bridge`
- `packaging`
- `empirical`
- `speculative`

The classification below is about the ordinary physics target, not only about
whether some internal record or adapter exists.

## Origin traceability status

- Owner doc:
  `Docs/OriginTraceabilityLedger.md`.
- Current repo status: `bridge/governance`
- Strongest current evidence:
  the core-spine bridge modules connect triadic algebra, ternary carrier,
  agreement ultrametric, contraction-certificate interfaces, and the CRT/J
  scalar identity; the minimal-credible and Stage C packages give bounded
  consumers over the canonical closure route.
- Corrected stale claim:
  `DASHI.Physics.Closure.AtomicChemistryRecoveryTheorem` exists locally. The
  remaining issue is not absence; it is that the module explicitly remains a
  bounded atom/chemistry interpretation carrier with open gates.
- Missing theorem:
  a theorem-owned origin receipt proving that a concrete carrier/map/fixed
  point/certificate predicts the empirical and chemistry-facing surfaces.
- Nearest promotion step:
  add a narrow origin receipt for `MinimalCrediblePhysicsClosureShiftInstance`,
  then separately promote empirical adequacy, convergence-rate dynamics, and
  atomic chemistry relaxation only when their theorem ingredients are present.

## Boundary examples: antifascistic systems, three-body, music

- Owner doc:
  `Docs/AntifascisticBoundaryAndMusic.md`.
  Music target detail:
  `Docs/MusicalAttractorTheorem.md`.
- Current repo status: `bridge/exploratory`
- Strongest current evidence:
  `AntiFascistSystem`, `FascisticSystem`, and `Fascism_Tests` expose the
  intended invertible-versus-contracting interface split; `DASHI.Physics.ThreeBody.*`
  already carries a theorem-thin boundary/predictability namespace; and the
  music lane has an executable MDL basin toy over `(Z/12Z)^n` plus a named
  exploratory `K_music` / `L_music` attractor target.
- Safe interpretation:
  exact carrier dynamics can be antifascistic while coarse observables behave
  fascistically after projection. The three-body lane is the clearest current
  natural example of that split.
- Missing theorem:
  a concrete derived incompatibility theorem for a physical Hamiltonian
  carrier, a solved three-body theorem, or a music-theoretic consonance law.
- Nearest promotion step:
  keep these as examples/bridges unless a module names the carrier, map,
  observable projection, MDL/entropy functional, and certificate.
  For music specifically, the prose target now names those fields; the
  remaining promotion step is a checked Agda island with finite `Z/12Z`
  case analysis and explicit scale-validity assumptions.

## 1. Natural dynamics law

- Ordinary physics meaning: a non-engineered evolution law with clear physical
  interpretation, rather than a bounded carrier cycle or post-selected update.
- Owner modules:
  `DASHI.Physics.Closure.CanonicalDynamicsLawTheorem`,
  `DASHI.Physics.DashiDynamics`,
  `DASHI.Physics.DashiDynamicsShiftInstance`,
  `DASHI.Physics.PressureHamiltonJacobiGap`,
  `DASHI.Physics.PressureGradientFlowGap`.
- Current repo status: `bridge`
- Strongest current evidence:
  `CanonicalDynamicsLawTheorem.agda` packages a theorem-bearing dynamics status
  surface and names propagation, causal admissibility, monotone quantity, and
  continuum-law slots; `DashiDynamicsShiftInstance.agda` gives a real bounded
  inhabitant with monotone density/action proxies and least-action-style local
  witnesses.
- Missing theorem: a realization-independent, non-engineered dynamics law that
  explains why the current law is physically natural rather than selected from
  the current shift-side carrier.
- Nearest promotion step: lift the current bounded law out of the canonical
  shift/constraint inhabitant into an abstract dynamics theorem whose
  admissibility, cone transport, and MDL-style monotonicity are not tied to
  one canonical live family.

## 2. Conserved physical quantity

- Ordinary physics meaning: a quantity with clear physical interpretation that
  is preserved or evolves lawfully enough to count as charge, action, or
  another serious invariant.
- Owner modules:
  `DASHI.Physics.Closure.AbstractGaugeMatterBundle`,
  `DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance`,
  `DASHI.Physics.Closure.CanonicalClosureCoarseObservable`,
  `DASHI.Physics.Closure.CanonicalClosureFibreFields`,
  `DASHI.Physics.Closure.ShiftContractCoarseObservable`.
- Current repo status: `bridge`
- Strongest current evidence:
  the abstract bundle has a real `ConservedObservableWitness`; the canonical
  abstract instance exports a preserved coarse charge
  `Gauge × basinLabel × mdlLevel × motifClass × eigenShadow`; the broader
  docs and fibre modules now separate descending coarse observables from richer
  fibre data rather than treating every Hecke/eigen channel as the next honest
  conserved quantity.
- Missing theorem: a conserved quantity with ordinary physics meaning, not only
  a theorem-bearing coarse observable package on the current quotient/fibre
  surfaces.
- Nearest promotion step: keep the current coarse quotient fixed, then promote
  one defended physical observable from the fibre/control layer into a theorem
  that survives the canonical closure law on more than the present bounded
  carrier.

## 3. Continuum limit

- Ordinary physics meaning: a theorem that the discrete closure/dynamics story
  converges to a genuine continuum carrier with preserved observables and cone
  structure.
- Owner modules:
  `DASHI.Physics.Closure.AbstractGaugeMatterBundle`,
  `DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance`,
  `DASHI.Physics.Closure.CanonicalDynamicsLawTheorem`,
  `DASHI.Physics.Toy.ScalarContinuum`.
- Current repo status: `bridge`
- Strongest current evidence:
  `AbstractGaugeMatterBundle.agda` now has an explicit `ContinuumWitness`
  carrying a limit carrier, scaling map, limit observable, limit cone, and
  MDL-compatibility obligations; `CanonicalAbstractGaugeMatterInstance.agda`
  inhabits that surface with the first honest quotient-like limit carrier.
- Missing theorem: convergence from the discrete closure path to a nontrivial
  continuum field/carrier, rather than a repackaged finite observable with the
  gauge wrapper stripped away.
- Nearest promotion step: replace the current quotient-like canonical limit
  inhabitant with a stronger limit carrier and prove preserved cone/observable
  behavior under scaling, not only compatibility by construction.

## 4. Realization-independent theorem

- Ordinary physics meaning: the same recovery story should hold across more
  than one admissible realization, not only on the canonical shift instance.
- Owner modules:
  `DASHI.Physics.Closure.PhysicsClosureRealizationIndependenceTheorem`,
  `DASHI.Physics.Closure.AbstractGaugeMatterBundle`,
  `DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance`,
  `DASHI.Physics.Closure.RGObservableInvariance`.
- Current repo status: `bridge`
- Strongest current evidence:
  `PhysicsClosureRealizationIndependenceTheorem.agda` already proves a narrow
  realization-independence statement by contrasting the canonical shift witness
  with a B4-backed witness; the bundle layer now exports
  `ObservableRGOffsetUniversality` and `ProjectionDeltaCompatibility`, and the
  canonical bundle instance inhabits those abstractions;
  `ShiftContractProjectionDeltaCompatibility.agda` now lands the first honest
  noncanonical `ProjectionDeltaCompatibility` inhabitant on the broader live
  `ShiftContractState` carrier.
- Missing theorem: a broad abstract recovery theorem whose main hypotheses are
  not still canonically inhabited only on the current bundle/shift family.
- Nearest promotion step: keep the abstraction layer fixed and land a second
  genuinely noncanonical or less shift-RG-dependent inhabitant of the
  transported projection/delta and recovery surfaces, so the theorem is no
  longer effectively tied to one live family plus one structural comparison
  witness.

## 5. Gauge/matter recovery

- Ordinary physics meaning: the core formalism should recover gauge sectors,
  matter content, and stable observables strongly enough that a physicist would
  accept the story as more than analogy.
- Owner modules:
  `DASHI.Physics.Closure.AbstractGaugeMatterBundle`,
  `DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance`,
  `DASHI.Physics.Closure.KnownLimitsFullMatterGaugeTheorem`,
  `DASHI.Physics.Closure.CanonicalConstraintGaugePackage`.
- Current repo status: `bridge`
- Strongest current evidence:
  `AbstractGaugeMatterBundle.agda` contains a real
  `GaugeMatterRecoveryTheorem`; the canonical instance now uses a
  closure-derived law and carries transported projection/Δ witnesses,
  conserved/coarse observables, continuum slots, and a theorem field
  `gauge-recovered` targeting `SU3×SU2×U1`.
- Missing theorem: physically serious matter/gauge recovery that is not only an
  abstract theorem on the canonical package plus transported shift-side
  observables.
- Nearest promotion step: widen the current canonical bundle inhabitant away
  from the live shift family while simultaneously strengthening the conserved
  and continuum witnesses so the gauge/matter theorem is not just structurally
  correct but physically interpretable.

## 6. GR/QFT regime recovery

- Ordinary physics meaning: recovery strong enough that the formal core
  reproduces the right gravitational and quantum-field regimes, not merely
  notation-compatible adapters.
- Owner modules:
  `DASHI.Physics.Closure.KnownLimitsGRBridgeTheorem`,
  `DASHI.Physics.Closure.KnownLimitsQFTBridgeTheorem`,
  `DASHI.Physics.GR`,
  `DASHI.Physics.QFT`,
  `DASHI.Physics.Closure.ContractionSignatureToSpinDiracBridgeTheorem`,
  `DASHI.Physics.Closure.CliffordToEvenWaveLiftBridgeTheorem`.
- Current repo status: `bridge`
- Strongest current evidence:
  both known-limits bridge theorems are real and theorem-bearing; the GR side
  carries a canonical adapter and `grRecovered ≡ grLikeTheoremBacked`; the QFT
  side carries a canonical adapter, spin/Dirac and Clifford/even-wave bridge
  surfaces, and `qftRecovered ≡ qftLikeTheoremBacked`.
- Missing theorem: full regime recovery rather than disciplined
  known-limits-facing translation and bridge bundles.
- Nearest promotion step: keep the known-limits theorem bundles explicit, but
  connect them to stronger dynamics, continuum, and gauge/matter witnesses so
  the recovery story is not only adapter-level and bridge-level.

## 7. Atom / quantum / wave correspondence

- Ordinary physics meaning: recovery of quantum-mechanical and atomic-scale
  structure such as wave evolution, energy levels, spectra, scattering, and
  chemistry in the right limits.
- Owner modules:
  `DASHI.Physics.SchrodingerGap`,
  `DASHI.Physics.SchrodingerGapShiftInstance`,
  `DASHI.Physics.SchrodingerAssumedTheorem`,
  `DASHI.Physics.Closure.PhotonuclearEmpiricalValidationSummary`,
  `DASHI.Physics.OrbitProfileComputed`,
  `DASHI.Physics.Signature31FromShiftOrbitProfile`,
  `DASHI.Physics.Closure.SyntheticRealizationWitness`,
  `DASHI.Physics.Closure.KnownLimitsRecoveredWaveRegimeTheorem`,
  `DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservablesTheorem`.
- Current repo status: `packaging`
- Strongest current evidence:
  the repo already has three distinct strengths on this lane:
  `SchrodingerGap.agda` and `SchrodingerGapShiftInstance.agda` give honest
  bounded wave/Schrodinger packaging with explicit non-claim boundaries;
  `OrbitProfileComputed.agda`, `Signature31FromShiftOrbitProfile.agda`, and
  `SyntheticRealizationWitness.agda` give real shell/orbit/profile and
  synthetic-shell witness structure; and the known-limits wave ladder now
  reaches recovered wave regime and recovered wave observables theorem
  surfaces. The photonuclear empirical lane remains the nearest current
  contact with measured scattering-like reality.
- Missing theorem: any derivation of Schrödinger dynamics, atomic spectra,
  many-body matter, or chemistry from the canonical closure core.
- Nearest promotion step: move from bounded proxy packaging to a wave/continuum
  theorem that connects the existing dynamics, shell/profile invariants, and
  known-limits wave bridges to a nontrivial quantum/atomic carrier, instead of
  only naming witness slots, finite witnesses, and assumed forms.

## Current read

- Strongest repo-native progress is on theorem-bearing bridge structure:
  closure spine, realization contrast, gauge/matter abstraction, and
  known-limits GR/QFT bundles.
- The biggest remaining deficit is still physical recovery rather than formal
  vocabulary: natural law, conserved quantity, continuum behavior, and
  atom-scale quantum recovery are not yet promoted to the same level as the
  closure spine.
