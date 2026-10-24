# Neutrino / IceCube Nobel 2026 — attribution-first max-cut (24 October 2026)

## Decision and scope

The 2026 Nobel Physics prize was awarded to Francis Halzen for decisive
contributions to IceCube and the discovery of high-energy astrophysical
neutrinos.  This observation programme is **not** a derivation of neutrino
masses, PMNS parameters, Majorana self-conjugacy, or any DASHI 369/C3
mechanism.  Distinguish physical detections from algebraic analogies.

This cut fixes an already source-written, testable **1/31** neutrino
mass-splitting prediction to a versioned dataset and confronts it with
the actual published normal-ordering intervals.  It intentionally does
not make the physical prediction true by stipulation.

## Prior-art ownership (reuse instead of inventing a parallel ontology)

- `DASHI/Physics/Closure/FactorVecFalsifiablePredictionLanes.agda`:
  `NeutrinoMixingRatioLane`, `prime31Ratio`, and
  `canonicalNeutrinoMassSplittingRatio`.  The candidate
  Delta m21² / Delta m31² = 1/31 is *an existing lane*, whose
  `predictionInCurrentWindow` is **a field demanded of any inhabitant**,
  not an independently established empirical fit.
- `DASHI/Physics/QFT/MuonNeutrinoIsolationReceipt.agda` and
  `DASHI/Physics/Closure/MuonNeutrinoIsolationReceipt.agda`:
  coprime level-11 vs candidate quark levels 3,4,7; explicitly *not*
  a physical neutrino or physical Yukawa theorem.
- `DASHI/Physics/Laws/StandardModelLawBoundary.agda`:
  `YukawaFlavourLaw.pmnsMatrix` and open
  `StandardModelOpenObligations.neutrinoMassMechanism`.
- `DASHI/Promotion/StandardModelHiggsYukawaParameterFrontier.agda`:
  both Dirac Yukawa and Majorana operator remain separate choices,
  requiring diagonalization, authority, calibration and phase conventions.
- `DASHI/Physics/CondensedMatter/MajoranaB4BraidExact.agda` and
  `MajoranaParityQubitExact.agda`: finite braid/qubit mathematics,
  NOT evidence for Majorana neutrinos.  Likewise C3/369 cyclic
  structures do not derive three active neutrino flavours.
- PR #1238 (diamond optics) provides a typed experimental-calibration
  separation pattern.  PR #1240 (VERID) preserves world-model
  experimental-authority gating.  No dependency is fabricated.
- `DASHI/Constants/Registry.agda` has PDG flavour/neutrino authority
  slots, not an automatically calibrated global oscillation fit.

## Distinct source roots and their roles

1. Royal Swedish Academy of Sciences, press release, 6 October 2026:
   https://www.kva.se/en/news/the-nobel-prize-in-physics-2026/
   **Role:** award and original institutional attribution, NOT an
   experimental table.
2. NuFIT **6.1 (2025)**, three-neutrino analysis based on data available
   in November 2025:
   https://www.nu-fit.org/?q=node%2F309
   Primary parameter table:
   https://www.nu-fit.org/sites/default/files/v61.tbl-parameters.pdf
   **Role:** versioned global-fit best fits and marginal 3-sigma
   intervals.  Its published analysis is not newly derived here.
   Convention: Delta m3l² = Delta m31² for normal ordering, but
   Delta m3l² = Delta m32² for inverted ordering.
3. IceCube Collaboration, IceTracks-DR2, released 21 May 2026,
   DOI: https://doi.org/10.7910/DVN/MMIIZA ;
   release index: https://icecube.wisc.edu/science/data-releases/
   **Role:** 2008–2022 candidate *track-event, source-search* data,
   with detector response/background and nuisance analysis necessary.
   No event-level reanalysis was executed in this cut.
4. Earlier 2015 Nobel for neutrino-oscillation discovery is independent
   historical evidence for nonzero neutrino masses; 2026 recognition is
   principally neutrino astronomy and its observational instrumentation.
   Neither identifies the Dirac vs Majorana mass mechanism.

## Concrete quantitative finding (no fit performed)

NuFIT 6.1 / NO / IC24 with Super-Kamiokande atmospheric:

| Observable | Best fit | Published marginal 3-sigma range |
| --- | --- | --- |
| Delta m21² [10^-5 eV²] | 7.537 | 7.236–7.823 |
| Delta m31² [10^-3 eV²] | 2.511 | 2.450–2.576 |

No source values are *derived* by DASHI.  Treat data citation and
normal-ordering selection as indispensable premises.

- Parameter-free candidate: `1/31 = 0.0322580645161...`
- Reported best-fit ratio: `7.537 / 251.1 = 0.0300159299084...`
- The componentwise Cartesian-rectangle upper ratio:
  `7.823 / 245.0 = 0.0319306122449...`
- Exact integer certificate: `31 * 7823 = 242513 < 245000`;
  gap `2487` in the cross-product numerator; therefore
  `1/31 > 7823/245000`.
- Hence **the exact 1/31 normal-ordering candidate is incompatible
  with the Cartesian product of the published individually profiled 1D 3-sigma
  parameter intervals**.  This is *not* a separately calculated
  correlated confidence level, 2D 3-sigma region or hypothesis-test p-value.
  In particular, one cannot simply retain
  `NeutrinoMixingRatioLane.predictionInCurrentWindow` for this
  convention/version without an actual widened or differently defined
  acceptance criterion.
- The inverted-ordering column is not directly the same denominator:
  `Delta m31² = Delta m32² + Delta m21²`, with negative
  `Delta m32²`.  The **signed** ratio is then negative, while an
  absolute-magnitude hypothesis is a distinct candidate and is not
  ruled out merely by the wide projected IO interval rectangle.
  No inverted-ordering chi-square has been computed here.
- This tests the pre-existing **literal** ratio, not an unspecified
  discretization-error escape hatch.  An allowed tolerance must be
  pre-registered and physically motivated, not adjusted after inspecting
  the data.

## Source-written proof and regression artifacts

`DASHI/Physics/QFT/NeutrinoIceCubeMaxCutExact.agda`:

- imports the **canonical existing** FactorVec neutrino-ratio interface;
- shows integer cross-product and natural-comparison exclusion against
  the source-specific normal-ordering interval rectangle;
- constructs an exact two-flavour **maximal-mixing four-phase toy**
  with `appearanceNumSq + survivalNumSq = 4`, phase-zero no
  appearance, phase-pi full appearance, and order-four phase cycles;
- introduces a typed but **uninhabited** physical-promotion boundary
  and a separate IceCube detector-response/likelihood interface.
  Neither constitutes a real three-flavour PMNS model or a detector
  calibration.

`tests/test_neutrino_icecube_maxcut.py` independently checks
fractions, the normal-ordering exclusion, the inverted-ordering
convention, and the toy probability normalization.

### Acceptance / verification

```sh
python -m unittest discover -s tests -p 'test_neutrino_icecube_maxcut.py' -v
agda -i . DASHI/Physics/QFT/NeutrinoIceCubeMaxCutExact.agda
```

GitHub connector writes are **source-written**, not a compiler receipt.
Do **not** claim kernel certification, empirical exclusion significance
beyond the interval comparison, or an IceCube data reanalysis without
executing and recording those jobs.  Do not rely on CI as a substitute
for a successful exact-head kernel check.

## Prioritised max-cut frontier

**P0 (model validity):** Revise/annotate the owner-side
`NeutrinoMixingRatioLane` acceptance protocol so it cannot silently
treat a demanded `predictionInCurrentWindow` field as a measured
successful no-fit test.  Version the NuFIT ordering, reference
denominator, calibration, interval family, and uncertainty.  Preserve
`prime31Ratio` as a **falsifiable candidate**, not a validated value.

**P1 (higher-value mathematical donor):** instantiate a genuine
3x3 complex unitary PMNS and
`P(alpha->beta; L,E)=|sum_i U(beta,i)exp(-i m_i^2 L/2E)
conj(U(alpha,i))|²`; prove normalization and rephasing invariance,
with ordering/units, vacuum vs matter Hamiltonians, source flavour
mixtures and identity in the same object.  The existing finite
two-flavour toy is a calibration of the proof *shape*, not a substitute.

**P2 (empirical same-object payment):** use IceCube DeepCore
oscillation samples / published likelihood and separately the
IceTracks-DR2 source-search events, with their original event
reconstruction, effective areas, atmospheric background,
point-spread functions, exposure and nuisance likelihoods.
Do not combine DR2 with superseded DR1 events or mistake source
detections for mass-parameter measurements.  Resolve published
covariances/chi-square grids before numerical exclusion significance.

**P3 (hypothesis discrimination):** Dirac vs Majorana requires
lepton-number-violating signatures such as neutrinoless double-beta
decay (with nuclear matrix-element and mechanism assumptions).
Seesaw mass, leptogenesis, sterile states and C3/369-sector proposals
must produce observable counterfactuals before physical promotion.
Majorana *zero-mode braiding* is not the same empirical question.

**P4 (instrument and multimessenger):** separate source-association
evidence, Cherenkov detector model, atmospheric-neutrino background,
astrophysical flux and multimessenger coincidence windows.  Publish
versioned negative/null results alongside successes.

### Outcome

Exact *finite* identity/inequality plus reusable audit interfaces;
source-authored programme-level rebuttal of the literal NO
`1/31` candidate; pending kernel and independent numerical runner
receipts; **no new neutrino-sector physical theorem**.


## 2026-10-24 continuation: source-v2 correction and genuine 3-flavour control

### Corrected experimental source version — operationally consequential

The original IceTracks-DR2 event release is **not identical** to the
later corrected response version.  IceCube SkyLLH v26.1.0 (9 September
2026) makes **IceTracks-DR2-v2** the current default and documents
two corrections to the v1 instrument-response functions:

1. IC86 highest Monte Carlo true-energy bin had extended past simulated
   log10(E/GeV)=8.7, artificially lowering the binned effective area;
   v2 stops the bin at 8.7.
2. The sin(declination) smearing matrices used IC40 bin boundaries for
   all seasons rather than the correct season-specific boundaries;
   v2 restores per-season binning.

Primary source: IceCube/SkyLLH v26.1.0 release, full original
changelog and developer statements:
https://github.com/icecube/skyllh/releases/tag/v26.1.0

Associated documentation: https://icecube.github.io/skyllh/v26.1.0/html/tutorials/index.html

**Do not pool v1 events with v2 response files** or assume v1-derived
test statistics remain valid under the corrected IRFs.  This correction
affects IceCube **source-search inference**, not the NuFIT 6.1 mass-fit
parameters on which the earlier NO inequality was calculated.  A
numerical publication-quality source likelihood has not been run.

### Primary-root attribution: authority is role-specific

| Root | Distinct attributed author/institution | Role | What it does **not** prove |
| --- | --- | --- | --- |
| Nobel Physics 2026 official press release, https://www.nobelprize.org/prizes/physics/2026/press-release/ | Royal Swedish Academy / Nobel official 6 Oct 2026 | Formal award citation, recognizes **Francis Halzen** for decisive IceCube contributions | Sole experimental authorship, PMNS parameters or source-specific point-source significance |
| IceTracks-DR2, https://arxiv.org/abs/2605.19040 | R. Abbasi **et al.**, IceCube Collaboration, dated May 2026 | Primary collective observational/data-method paper and benchmark | Any novel DASHI claim or mass-generation model |
| DR2-v2 SkyLLH release above | IceCube/SkyLLH maintainers, Sept 2026 | Authoritative software/IRF *correction history* | New independent astrophysical detections or physical flavour results |
| NuFIT 6.1 2025 published parameter table | NuFIT global-fit researchers | Versioned mass and mixing fit (independent of DR2 point-source likelihood) | Theory derivation, independently new raw observations, correlated exclusion significance from marginal endpoints |
| DASHI FactorVec original owner module | Repository authors and Git commit provenance | Source-written proposed **1/31** discrete arithmetic hypothesis | Empirical success, priority over NuFIT, verified physical source |
| New DASHI C4 and three-flavour finite modules | This PR; derived illustrative finite constructions | Algebraic controls, proposed Agda proofs | Real PMNS entries, measured mass scales, actual Majorana neutrino nature |

Press retellings of the Nobel announcement do **not** count as new
independent award witnesses.  The IceCube data release, its analysis
software, and the arXiv preprint are separately dated artifacts but
not three independent observations.  NuFIT's reuse of experimental
measurements likewise must not be counted as a second detector.
Published source claims, numerical reproductions, source-written Agda,
compiler-checked Agda, detector calibrations and confirmed physical
predictions are separate evidence statuses.

### Mathematical advance and exact boundary

`DASHI/Physics/QFT/NeutrinoThreeFlavourFiniteExact.agda` constructs

```
Utoy = [[1, 2, 2], [2, 1, -2], [2, -2, 1]] / 3
D = diag(d1, d2, d3), with di in {1, i, -1, -i}
A = Utoy D Utoy^T
P(alpha -> beta) = |A[beta,alpha]|^2.
```

The integer matrix has `M M^T = 9 I`.  Since the
complex phase elements all have modulus 1, the exact **mathematical**
consequence is `sum_beta P(alpha -> beta)=1`.

It includes 192 closed Agda reflexivity clauses (3 input flavours
x 4^3 phase triples) and an explicit nontrivial channel:

```
(d1,d2,d3)=(1,i,-i)
P(e -> e) = 1/81
P(e -> mu) = 40/81
P(e -> tau) = 40/81
```

The 192 cases and Gram identity were **independently checked by local
Python integer enumeration**.  They are **source-written Agda**, not
presently kernel-certified.  The integer matrix is a fully specified
rational orthogonal *toy mixer*, not the physical PMNS matrix.
The toy C4 phase discretisation does not imply that physical phases
are quantised to 90 degrees; continuous unitary evolution, including
matter effects, remains a separate theorem target.

`tests/test_neutrino_three_flavour_bridge.py` adds an independent
numeric implementation of the standard PDG 3x3 **complex** PMNS
parametrisation, with published NuFIT NO best-fit inputs, and tests
vacuum mixing, three-flavour normalization, zero-distance,
common-mass-shift invariance, flavour and mass-state rephasing, CP
conjugation in vacuum, exact 192-case C4 enumerations and the
mass-ordering/source-type guards.  These are model-identity and
consistency controls, **not empirical fits**.  No NuFIT likelihood was
downloaded or minimized.  The input `delta_CP=212 deg` is a
fit-dependent NO best-fit input rather than a precision determination.

C4 should not be promoted to C3/369 or a balanced-ternary rule.
The mathematical toy has ordinary additive *canonical* zero; an
optional signed-zero information carrier cannot be equated to two
different zero probabilities or to antineutrino states without an
explicit observable quotient and phase-sensitive experiment.
RH/NS/YM formal developments are possible computational donors only,
not automatically the same physical object or evidence.

### Ordered remaining cuts and acceptance

- **R0 (mathematical certification):** run Agda 2.9 exact-head
  check of *both* `NeutrinoIceCubeMaxCutExact.agda` and
  `NeutrinoThreeFlavourFiniteExact.agda`; save kernel stdout,
  version, branch SHA; address exact errors, not another receipt.
- **R1 (continuous physical PMNS):** replace C4 with complex
  unit-circle phases on all baselines/energies and prove
  `U†U=I`, `Σ_beta |A|²=1`, row/column rephasing invariance,
  a `U->U*` antineutrino operation and matter-Hamiltonian
  dependence in a continuous-real formal library.  Do not insert
  these as unproven fields and then call them constructed.
- **R2 (correlated global fit):** fetch versioned NuFIT
  two-dimensional Δχ² grids or official likelihood and calculate
  actual Δχ² for the predeclared same-convention `1/31`
  hypothesis, profiling nuisance parameters.  Independent interval
  exclusion is **not** a chi-square/dof or p-value.
- **R3 (IceCube source inference):** pin SkyLLH v26.1.0 and DR2-v2
  calibrated IRFs, original observations and point-source
  background/response, run an original-vs-reproduction benchmark;
  do not conflate this with DeepCore oscillation event samples.
- **R4 (Dirac/Majorana):** encode lepton-number-violating amplitude
  and source-specific neutrinoless double-beta-decay nuclear
  matrix-element uncertainty, separating mechanism assumptions from
  observed decay constraints; never use the condensed-matter Majorana
  braid as an empirical neutrino witness.

Run locally:

```sh
python -m unittest discover -s tests -p 'test_neutrino*maxcut.py' -v
python -m unittest discover -s tests -p 'test_neutrino_three_flavour_bridge.py' -v
agda -i . DASHI/Physics/QFT/NeutrinoIceCubeMaxCutExact.agda
agda -i . DASHI/Physics/QFT/NeutrinoThreeFlavourFiniteExact.agda
```

Status: repository source and GitHub connector read-back can be
verified remotely.  The old five unit tests were rerun locally and
passed.  Independent numerical C4 and PMNS algebra checks were
performed locally; the *new committed nine-test suite itself* and
Agda kernel compilation have not been executed as GitHub branch files
in this runtime.  No evidence grade is inflated to PASS on that basis.


### Exact inverted-ordering interpretation control (subsequent cut)

The **absolute-magnitude** `1/31` ratio is not even
componentwise excluded by the *inverted* NuFIT 6.1 intervals.  Take
the exact integer witness, all in units of 10^-8 eV²:

```
Delta m21² = +7600      in [7236,7822]
Delta m32² = -243200    with |Delta m32²| in [242100,254700]
Delta m31² = -235600    since Delta m31² = Delta m32² + Delta m21²
|Delta m21² / Delta m31²| = 7600/235600 = 1/31
Delta m21² / Delta m31² = -1/31   (signed)
```

The two component values are in the individual 3σ marginal
intervals, but there is **no assertion** that the pair lies in a
correlated 3σ joint region.  This counterexample blocks an
overgeneralized statement that every order/convention falsifies
`1/31`.  NuFIT's preferred ordering and independent model selection
remain separate matters.

### Physical CP discriminator (new numeric regression)

The continuous-complex PDG PMNS regression additionally checks the
vacuum neutrino-versus-antineutrino appearance asymmetry

```
P(nu_alpha->nu_beta) - P(anti-nu_alpha->anti-nu_beta)
 = 4 * sum_{i>j} Im[c_i conj(c_j)] sin[phi_i - phi_j],
c_i = U(beta,i) conj(U(alpha,i)).
```

For supplied NuFIT 6.1 NO *best-fit parameters* and the illustrative
vacuum point L=1300 km, E=2.5 GeV, the muon-to-electron channel
difference is about +0.01416008.  Independent numerical paths
matched within 4e-17.  The choice of baseline and energy is a
simulation fixture; **no measured CP asymmetry, experimental
sensitivity, matter-corrected event rate or discovery significance**
has been derived here.  In particular matter-induced ν/anti-ν
asymmetries must be modelled separately before detector comparisons.
Majorana column phases cancel from these vacuum oscillation
probabilities; lepton-number-violation remains an independent
observable target.

### Statistical interpretation correction

A `3σ` *one-parameter profile interval* (customarily
`Δχ²≤9`) and a `3σ` *two-parameter joint confidence contour*
do **not** generally use the same `Δχ²` threshold.
Therefore the Cartesian product of the two published NuFIT marginal
intervals is **not** a calibrated two-dimensional 3σ confidence
region, and its boundaries do not justify a free-standing claim
of `>3σ` global significance or a calculated p-value.
The exact comparison `1/31 > 7823/245000` remains correct as
an interval statement, and the IO signed/magnitude witness remains
correct as a Cartesian-interval existence statement.  The actual
correlated significance is still an open NuFIT-grid calculation.

## 2026-10-24 max-cut round 3 — C3/zeta/zero existing prior-art recovery

### Why the `1,i,-i` choice must not become canonical

The initial four-phase finite proof in this PR used the **Cartesian**
C4-phase tuple `(1,i,-i)`.  That was a valid finite
interference *fixture*, but the repository already owns a stronger
native symmetric ternary construction.

**Native C3 owner graph, in precedence order:**

1. `DASHI/Reasoning/RelationalTernaryPhaseGeometry.agda`:
   `EisensteinWave`, `rootOne`, `rootOmega`,
   `rootOmegaSquared`, `normE`, `ternaryRootsCancel`,
   `ternarySymmetricIntensityIsZero`; symmetric alternatives
   **0, 2π/3, 4π/3**, distinct from the ordered C4 half-circle.
2. `DASHI/Moonshine/C3CyclotomicAmplitudeAlgebraExact.agda`:
   rational **Q(ζ3)**, norms, conjugation, root identities.
   Original mathematics attributed to L. C. Washington,
   *Introduction to Cyclotomic Fields*, 2nd ed., 1997;
   DOI 10.1007/978-1-4612-1934-7.
3. `DASHI/Moonshine/Monster3BCyclotomicLinearAlgebraExact.agda`:
   existing exact **1+ζ+ζ²=0** and additive/multiplicative algebra.
4. `DASHI/Moonshine/C3FourierConjugationExact.agda`:
   original roots/finite characters attributed to Terras (1999)
   and Serre (1977); characters
   `[1,1,1], [1,ζ,ζ²], [1,ζ²,ζ]`.
5. `DASHI/Biology/Physical/C3CubeCyclotomicFourierExact.agda`:
   an already-defined exact **27-site C3³ transform and inverse**.
   No need to build another 27-site Fourier object.
6. `DASHI/Algebra/Quantum/QutritMatrixGates.agda` and
   `DASHI/Algebra/Quantum/OrdinaryComplexQutrit.agda`:
   actual abstract 3x3 complex-star-semirings and qutrit gates
   with normative Fourier authority boundaries.
7. `DASHI/Moonshine/Monster369ZetaSameObjectWeldExact.agda`:
   selected cyclotomic scalar on literal VOA/3B model is already
   the same named *scalar* but not a source-independent equality
   between neutrino mass eigenstates, Monster eigenspaces,
   geometrical sites or IceCube events.
8. `DASHI/Moonshine/Base369Monster3BRepresentationBidiSearchRound5Exact.agda`:
   explicitly keeps `zeroIsFourthEigenphase = false`.
   This is a particularly important negative prior-art receipt.

### Exactly what `ζ, ζ², 0` means

The three *unit phases* are **1, ζ, ζ²**, all with squared norm
one, and `1+ζ+ζ²=0`.  The resulting **additive** amplitude zero
has squared norm zero.  It is NOT the third physical neutrino mass,
a fourth phase, a negative zero probability, or an arbitrary
spin/charge label.  The phase-zero *angle* is represented by the
multiplicative **identity 1**, which is not additive zero.  A
signed-zero bookkeeping carrier may retain history, but the
Born-probability quotient sends all zero amplitudes to nonnegative
zero intensity.

### Newly contributed exact C3 interference donor

`DASHI/Physics/QFT/NeutrinoC3CyclotomicPriorArtBridgeExact.agda`:

- Imports the **actual existing** `C3.C3Phase` symbolic phase type,
  `RelationalTernaryPhaseGeometry.EisensteinWave` exact arithmetic
  and the earlier three-flavour mixer.
- Exhibits the literal symbolic-to-Eisenstein phase identification
  and `1+ζ+ζ²=0`, root norm one vs zero norm zero.
- Computes amplitudes `A_beta_alpha = sum_i M_ai M_bi ζ^(ki)`,
  divided by `9`; their squared norms divide by `81`.
- Exhausts all **3 source flavours × 3³ phase triples = 81** exact
  integral identities `Σ_beta |A_beta_alpha|²=81` for the
  previously supplied **toy** mixer `M/3`.
- Gives the nontrivial `(1,ζ,ζ²)` witness:
  `[P(e->e),P(e->μ),P(e->τ)] = [9,36,36]/81` =
  `[1/9,4/9,4/9]`.  Its conjugate input swaps ζ and ζ²
  without affecting these probabilities for the real toy mixer.
- Encodes the C3 Fourier character-entry norms
  `|F_ab|²=1`; this normalized matrix would have
  `|U_e3|²=1/3`.  The earlier rational toy `M/3`
  instead has `|U_e3|²=4/9`.  Neither is the measured PMNS
  matrix; both exceed the loose `sin²θ13<0.03` empirical screen.
  The source comparison is NuFIT 6.1 IC24+SK, for which
  `sin²θ13≈0.0225`.  This is an **algebraic model-screening no-go**,
  not a confidence-level computation.
- Proves a conditional **3-divisibility obstruction**:
  because `p³=1` for every p in C3, any phase-valued
  homomorphism obeying `f(t)=f(t/3)^3` has image only `1`.
  Real additive propagation time is 3-divisible.
  Thus nontrivial C3-valued oscillation phases cannot represent
  all continuous `L/E` propagation with nonzero mass splittings.
  Discrete samples, internal symmetries, broken residual symmetry,
  continuous U(1) completion and C3-equivariant **selection**
  remain possible hypotheses, not settled physics.

**Independent executed arithmetic** (2026-10-24): Python integer
enumeration completed 81/81 conservation cases and 9/9 C3 character
inner products; also reproduced `[9,36,36]`,
`1+ζ+ζ²=0`, `1/3` and `4/9` reactor entries, and
`p³=1` for all three phases.  This is NOT Agda kernel verification.
The committed `tests/test_neutrino_c3_cyclotomic_bridge.py` contains
eight tests, but the exact committed script has not yet been run by a
local checked-out GitHub branch; do not label that as executed.

### Literature source roots and claim roles

| Dated original root | Who originated the relevant claim | Appropriate use; prohibited promotion |
| --- | --- | --- |
| Altarelli & Feruglio (2005), **Tri-Bimaximal Neutrino Mixing from Discrete Symmetry in Extra Dimensions**, arXiv:hep-ph/0504165 / Nucl. Phys. B 720 (2005) 64 | Named paper authors | A4 flavour model with scalar alignment and corrections; no claim of exactly observed θ13=0 today |
| Altarelli & Feruglio (2006), **Tri-Bimaximal Neutrino Mixing, A4 and the Modular Symmetry**, arXiv:hep-ph/0512103 / Nucl. Phys. B 741 (2006) 215 | Named paper authors | Model-specific A4 sectors and explicit symmetry breaking; not guaranteed new mass spectrum |
| Altarelli & Feruglio (2010), **Discrete Flavor Symmetries and Models of Neutrino Mixing**, Rev. Mod. Phys. 82, 2701, DOI 10.1103/RevModPhys.82.2701 | Named review authors; synthesis of prior original models | Broad prior art; re-tellings are not independent original proof roots |
| Ma & Wegman (2011), **Nonzero theta13 for neutrino mixing in the context of A4 symmetry**, PRL 107 061803 / DOI 10.1103/PhysRevLett.107.061803 | Named paper authors | Post-ideal correction to original A4 flavour patterns; source-specific model and parameter constraints |
| Walter Grimus (2013), **Discrete symmetries, roots of unity, and lepton mixing**, arXiv:1301.0495 | Named paper author | Vanishing-sum and residual-symmetry group theory directly relevant to ζ cancellation; not a claim that any C3 Fourier matrix is observed |
| NuFIT 6.1 (2025) plus Esteban et al. JHEP 12 (2024) 216 | NuFIT global-fit collaboration | Physical PMNS mixing targets, measured θ13 and χ² authority (separate from detector event source) |
| Bari group **2026.a Preliminary**, as of 15 Oct 2026, https://global-nu.org/results.html | Bari global-analysis team | Contemporary independent **analysis** useful as adversarial comparison; preliminary, no full χ² data release yet; does NOT add an independent experimental detector or supersede NuFIT automatically |

Links:
https://arxiv.org/abs/hep-ph/0504165
https://arxiv.org/abs/hep-ph/0512103
https://arxiv.org/abs/1301.0495
https://doi.org/10.1103/PhysRevLett.107.061803
https://doi.org/10.1103/RevModPhys.82.2701
https://www.nu-fit.org/?q=node%2F309
https://global-nu.org/data.html

### Reset Pareto research roadmap after this recovery

**P0 (now paid at source level):** exact original C3/Eisenstein
representation recognition, 81/81 three-flavour conservation case
definitions, physical reactor **counterexample to naive F3 and M/3
identifications**, and the C3-continuous-time divisibility
obstruction.  This corrects the prior overindexing on C4 phases.

**P1 (highest-value remaining formal theorem):** actual exact-head
Agda compile of the imported C3, QFT and probability owner chain;
then construct the **continuous complex** (or suitably completed
rational-cyclotomic) PMNS plus individual charged-lepton/neutrino mass
matrices and their residual symmetry actions on the **same** lepton
space.  A single C3 set or character chart is not enough.

**P2 (highest-value empirical discriminator):** choose a *specific*
A4/S4 modular/residual model, derive full nontrivial
`U_e3`, `θ12`, `θ23`, `δCP` and mass splittings with physical
sources, then compare with versioned NuFIT profiles or the published
Bari likelihood when available.  Avoid overfitting and post-hoc
extra operators; register model parameters and priors beforehand.

**P3:** keep the weak-interaction neutrino source, charged-current
production/detection, continuous propagation and detector likelihood
separate but linked by real same-object spectral/operator maps.
IceTracks-DR2-v2 is source astronomy, whereas DeepCore/JUNO/T2K
oscillation fits are the appropriate mixing tests.

**P4:** only after the same-lepton-action construction, ask whether
the Monster/3B/C3, qutrit, or 27-hypervoxel representations induce
the physical flavour-sector mass operator.  Without actual
intertwining, those are donors and potential no-go targets, not
physics derivations.

## 2026-10-24 empirical discovery: IceCube three-flavour composition as a real consumer

### Original primary experimental source (not a secondary Nobel retelling)

**IceCube Collaboration (R. Abbasi et al.),**
"Characterization of the Three-Flavor Composition of Cosmic Neutrinos
with IceCube," *Physical Review Letters* **137**, 081002, published
18 August 2026, DOI **10.1103/vntd-m133**:
https://doi.org/10.1103/vntd-m133

Using **11.4 years of IceCube data**, the collaboration reports
the best-fit *Earthly flux* flavour fractions
`(f_e,f_mu,f_tau)=(0.30,0.37,0.33)`, with asymmetric and substantial
uncertainties, in an analysis spanning about 5 TeV–10 PeV.
Its result finds all three flavours present above the 90% confidence
threshold; source composition is consistent with pion-decay origin,
while pure-neutron-decay production is disfavoured under the assumed
analysis model, with posterior probability `2.7×10^-5`.
Those are the **collaboration's** statistical conclusions, **not**
new significance calculations produced by DASHI.

This is a **different primary analysis/sample/likelihood** from the
IceTracks-DR2-v2 public point-source dataset, NuFIT's
oscillation parameter fit, and the 2026 Nobel award.  It must not
be treated as four independent source detections merely because the
press coverage and data releases have separate URLs.

### Exact high-energy long-baseline phase averaging

Over astronomical distances, under standard incoherent vacuum
propagation with three stable neutrinos:

```
Pbar(alpha,beta) = Σ_i |U(alpha,i)|² |U(beta,i)|²
f_earth(beta) = Σ_alpha f_source(alpha) Pbar(alpha,beta)
```

`DASHI/Physics/QFT/NeutrinoC3AstrophysicalFlavorNoGoExact.agda`
constructs both finite mixing examples by **reusing** the Fourier
entry and rational mixer owners, and deriving their incoherent
oscillation transfer from the literal algebraic entries.

**Flat C3 Fourier** `U=F3/sqrt(3)`:

```
Pbar_F = (1/3) [[1,1,1],
                [1,1,1],
                [1,1,1]]
```

This matrix has rank one, annihilates the two-dimensional
source-contrast subspace, and produces the same Earth mixture
`(1/3,1/3,1/3)` for all normalized source mixtures.
In particular, the normalized **pion** `(1:2:0)` and pure
**neutron** `(1:0:0)` source ratios become exactly identical.
This is a **source-identifiability no-go for FLAVOUR FRACTIONS ALONE**
under that fixed mixing matrix and the stated phase-averaging
assumptions—not a claim that a specific IceCube likelihood has
measured or excluded F3 by itself.  Reactor mixing independently
rules out the naive Fourier matrix.

**Earlier rational toy** `U=M/3`:

```
Pbar_M = (1/27) [[11, 8, 8],
                 [8, 11, 8],
                 [8, 8, 11]]
        = (8J+3I)/27
pion_earth    = (9,10,8)/27
neutron_earth = (11,8,8)/27
```

The old rational toy retains one ninth of source flavour contrast,
but its reactor `|U_e3|²=4/9` is incompatible with observations;
therefore **neither** toy is an acceptable physical PMNS
candidate.  Agreement of a selected toy pion fraction with a
single observed best-fit coordinate is NOT a fit.

**Continuous complex PMNS numerical benchmark** using the declared
NuFIT 6.1 NO best-fit angle/CP input choices in
`tests/test_neutrino_three_flavour_bridge.py` gives:

| Source flavour at emission | Calculated Earth e | Calculated Earth μ | Calculated Earth τ |
| --- | ---: | ---: | ---: |
| Pion decay (1:2:0) | 0.32634 | 0.34322 | 0.33044 |
| Neutron decay (1:0:0) | 0.54815 | 0.21543 | 0.23642 |
| IceCube published best fit (Earth only, not a source model) | 0.30 | 0.37 | 0.33 |

These are **newly computed deterministic model predictions using
existing published mixing inputs**, not new measurements.
No astrophysical source spectra, energy-dependent detector response,
production branching uncertainty, neutrino/antineutrino ratio,
classification systematics, or posterior has been constructed here;
therefore **do not infer significance** or claim a replication of
the collaboration's exclusion.  The physical benchmark
`Pbar` is a mathematical consumer of accepted PMNS data, not a
proof of mass eigenstate mechanism or C3/Monster identity.

### New tests and exact status

`tests/test_neutrino_c3_cyclotomic_bridge.py` contains:
81-case exact C3 conservation, 9-case exact Fourier character
orthogonality, sum-zero versus nonzero unit phases, source-mixing
no-go and detector screening.  Newly added
`tests/test_neutrino_three_flavour_bridge.py` includes the
physical PMNS phase-averaged pion/neutron source benchmarks.

Independent Python arithmetic was executed for **81 C3 identities,
9 Fourier orthogonality checks and both source propagators**, including
their exact rational Earth fractions.  A separate Python calculation
executed the standard three-flavour PMNS benchmark and produced the
six Earth fractions recorded above.  These are **independent
computational validations**.  The exact GitHub branch files and all
Agda modules remain **kernel-pending**, and the freshly committed
test files do not have a direct exact-file test-run receipt yet.
Use these commands on the head branch:

```sh
python -m unittest discover -s tests -p 'test_neutrino_c3_cyclotomic_bridge.py' -v
python -m unittest discover -s tests -p 'test_neutrino_three_flavour_bridge.py' -v
agda -i . DASHI/Physics/QFT/NeutrinoC3CyclotomicPriorArtBridgeExact.agda
agda -i . DASHI/Physics/QFT/NeutrinoC3AstrophysicalFlavorNoGoExact.agda
```

### Roadmap re-ranking: 2026 high-value independent constraints

**P0 paid at source-written/exact arithmetic level:** C3 phase reuse,
additive-zero versus phase identity, source-conditioned 81-case
probability normalization, strict same-phase but different-mixer
countermodels, 3-divisibility obstruction to continuous C3-only
propagation, and exact decohered source-information rank-one no-go.
The 2026 IceCube paper is now registered under its
**original collaboration authorship** as a consumer.

**P1 physical necessity:** continuous 3x3 PMNS must be derived from
the **charged-lepton diagonalization and neutrino mass eigenbasis**
on the same lepton Hilbert space; the differing residual actions
and their symmetry breaking must genuinely reproduce non-flat
`|U_e3|²`, nonmaximal mixings, CP convention and mass splittings.
Simply tagging three cube sites or 3B eigenvalues electron/muon/tau
is insufficient.

**P2 empirical source fits:** reproduce the original IceCube 2026
three-flavour likelihood or a properly released event-level sample,
including track/cascade/double-cascade classifications, energy
selection, detection efficiencies and all reported nuisance
parameters, then profile pion/neutron counterfactuals.  DR2-v2
point-source IRFs are **not a substitute** for that experiment's
flavour-classification likelihood.

**P3 parameter tension:** NuFIT correlated Δχ² for the original
`1/31` ratio (with exact ordering/convention), plus registration
of possible A4/S4 residual-family mass-texture models and
held-out observables.  No post-hoc free counterterms to rescue a
failed literal ratio.

**P4 terminal same-object decision:** require a literal
spectral/operator intertwiner from the repo's 3B/C3/qutrit/729
action to a physical lepton flavour Hamiltonian with source,
propagation and detection and a discriminating observation.
Until then the native C3 work is an excellent mathematical donor,
not an empirical derivation of neutrino dynamics.
