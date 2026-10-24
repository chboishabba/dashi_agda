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

## 2026-10-24 max-cut round 4 — same-object lepton mass operators, finite-group obstruction

### Original scholarly authority and reuse ownership

**Separate dated original scholarly roots**:

- Renato M. Fonseca and Walter Grimus, "Classification of lepton mixing
  matrices from finite residual symmetries," *JHEP* **09** (2014) 033,
  DOI https://doi.org/10.1007/JHEP09(2014)033 ;
  preprint https://arxiv.org/abs/1405.3678.
  Their result concerns which **finite-group** charged-lepton and
  Majorana-neutrino residual symmetries can determine mixing, and
  uses root-of-unity sums.  It does **not** claim that an arbitrary
  orthogonal mixing matrix generates a finite flavour group.
- Claudia Hagedorn and Johannes König, "Lepton and quark mixing from a
  stepwise breaking of flavor and CP," *Phys. Rev. D* **100**
  (2019) 075036,
  https://doi.org/10.1103/PhysRevD.100.075036 .
  Their stepwise residual breaking and CP analysis is substantive
  physical model-building prior art, not attributable to DASHI.
- A. Giarnetti, S. Marciano, D. Meloni, "Constraining the Neutrino
  Mixing Matrix via Single-Sector Charged-Lepton Rotations in the
  JUNO Precision Era," *Symmetry* **18** (2026) 954,
  https://doi.org/10.3390/sym18060954 .
  Their 2026 study uses NuFIT 6.1 and highlights precision/sector
  corrections; cite original named authors, not a broad QFT slogan.
- Lawrence C. Washington, *Introduction to Cyclotomic Fields*,
  2nd ed. (1997): cyclotomic field integer arithmetic,
  including \\(\\mathcal O_{\\mathbb Q(\\zeta_3)}
  =\\mathbb Z[\\zeta_3]\\).
  Standard theorem: finite-order complex matrices have root-of-unity
  eigenvalues, hence algebraic-integer traces.  These are original
  general mathematical results, NOT newly proved by the present PR.
- NuFIT 6.1 (November 2025 data freeze) is the empirical global-fit
  **input authority**, including JUNO-related updates.  The IceCube
  2026 source flavour measurement remains a distinct experimental root.

Existing actual repository donors: `TriadicDepthOneCharacters`,
`RelationalTernaryPhaseGeometry`, `C3CyclotomicAmplitudeAlgebraExact`,
`NeutrinoC3CyclotomicPriorArtBridgeExact`, the original
`StandardModelLawBoundary`, and the earlier QFT finite-mixer modules.
No new 3-cycle representation, signed-zero species or 27-site ontology
is introduced.

### Concrete new same-lepton-space model (NOT parameter-free)

`DASHI/Physics/QFT/NeutrinoSameLeptonMassOperatorRationalExact.agda`
uses one flavour coordinate space `{electron,muon,tau}`.
Its **rational reconstruction choices** are the Pythagorean pairs:

```
(s12,c12) = (161/289, 240/289)
(s13,c13) = (240/1609, 1591/1609)
(s23,c23) = (20/29, 21/29)
U = R23 R13 R12    with δ_CP=0
M = D U;   D = 13,485,029
M = [[ 11073360,  7428379, 2011440],
     [ -6592029,  7336560, 9195980],
     [  3971380, -8534640, 9655779]]
```

Exact integer calculations:

```
M M^T = M^T M = D² I
D² = 181846007130841

H_charged = diag(1,4,9)                (ARBITRARY dimensionless masses)
H_neutral = M diag(0,7537,251100) M^T / D²
H_neutral U = U diag(0,7537,251100).
```

Neutrino eigenvalues are **source-selected mass-squared
differences** in units 10^-8 eV², with *arbitrary common offset zero*.
They are NOT independently derived absolute neutrino masses, Yukawa
couplings, or a mass-generation theory.  The charged-lepton
eigenvalues `1,4,9` are simply arbitrary distinguishable
labels, NOT the observed masses.  The construction has
`[H_charged,H_neutral]_(e,mu)=-15166183339406582640/D² ≠ 0`,
so it genuinely exhibits a noncommuting eigenbasis pair on one
specified space.

The charged-lepton residual `T=diag(1,ζ,ζ²)` is sourced from the
existing canonical C3 phase module and preserves diagonal
`H_charged`.  The neutrino residuals

```
S1=U diag( 1,-1,-1) U^T
S2=U diag(-1, 1,-1) U^T
S3=U diag(-1,-1, 1) U^T
```

satisfy `S1²=S2²=I`, `S1 S2=S3`, and commute with
`H_neutral`, using this same `U` and same flavour labels.
They are **constructed from U**, so their existence cannot
independently explain why nature chooses those U entries.
A neutral *mass-squared* operator does not determine Dirac versus
Majorana status; a genuine Majorana mass matrix has a separate
congruence condition `S^T M_nu S=M_nu`.

Local exact-rational and source-derived BigInt checks show

```
sin²theta12 = 0.3103530849
sin²theta13 = 0.0222489948
sin²theta23 = 0.4756242568
J_CP = 0        (real matrix)
```

These angles were *selected post hoc* to approximate NuFIT 6.1,
not derived from C3.  CP=0 is a clear omitted physical feature
compared with the supplied nonzero `deltaCP=212°` global-fit
best-fit input; no statement of CP=0 exclusion confidence is made.

### Important algebraic-number-theory new no-go: generated group is infinite

The finite-order/trace-integrality test proves a stronger
mathematical claim for **THIS ONE exact rational reconstruction**.

With `T=diag(1,ζ,ζ²)` and
`S1=U diag(1,-1,-1) U^T`, the product `TS1` has

```
tr(TS1) = a + b ζ
a = 213694885170400 / 181846007130841 ≈ 1.1751420256
b =  55365974464882 / 181846007130841 ≈ 0.3044662643
```

The `ζ²=-1-ζ` identity was used to obtain those coefficients.
An **independent exact BigInt evaluation of the committed Agda
`M` entries** verified the full residual matrices and trace
numerators.  `NeutrinoC3FiniteResidualTraceObstructionExact.agda`
now records these numerator computations and exact integer interval
checks `1<a<2`, `0<b<1`.

The classical deductive chain is:

1. If `TS1` had finite order, all of its eigenvalues would be roots
   of unity, so `tr(TS1)` would be an algebraic integer.
2. `tr(TS1)∈Q(ζ)`; the algebraic integers of `Q(ζ)` are
   `Z[ζ]`, with **integer** coefficients in the basis `1,ζ`.
3. But `a∈(1,2)` is **not an integer**.  Hence this exact
   `tr(TS1)` is not an algebraic integer.
4. So `TS1` has **infinite order**, hence
   `<T,S1>` is an **infinite group**.

This is a valid conditional-on-standard-number-theory mathematical
deduction about the **explicit rational example**, not an Agda
kernel proof of the general integrality theorem, not an empirical
theory of particle masses and not an impossibility theorem for
*all* finite flavour groups.  It is an adversarial counterexample to
the shortcut "charged Z3 + neutral Klein => finite flavour group".
Original finite-group model classifications retain their full scope.

### Independent exact-head source-validation receipt

The GitHub connector returned the literal committed Agda source
blob `1fc22e949a107f639a5e91e44f2db16a29a6cd0a`
for `NeutrinoSameLeptonMassOperatorRationalExact.agda`.
An **independent JavaScript BigInt exact evaluator**, parsing
the nine `mixNum` definitions from that returned source,
computed:

- 9/9 row and 9/9 column Gram equalities;
- 9/9 eigenvector equations for the chosen mass-squared operator;
- operator symmetry and off-diagonal witness;
- both involution-square identities;
- `S1*S2=D²*S3` and commutation of S1 and S2 with Hnu;
- trace coefficients and the exact denominator above.

Each comparison returned `true`.  The original Python/SymPy
calculation independently agreed on the integer values.
This is **source-executed arithmetic verification**, NOT
a run of the Agda compiler, and not a run of the committed new
Python test file.  It must not be reported as kernel-certified.

The committed Python file
`tests/test_neutrino_same_lepton_rational.py`
contains exact Fraction controls of the same statements, the
CP-zero construction and the infinite-group trace obstruction.
It has not been executed from the exact branch in this runtime.

### Updated Pareto max-cut deliverables (do not reopen paid toy work)

**R0 exact-head kernel payment**:
```sh
agda -i . DASHI/Physics/QFT/NeutrinoIceCubeMaxCutExact.agda
agda -i . DASHI/Physics/QFT/NeutrinoThreeFlavourFiniteExact.agda
agda -i . DASHI/Physics/QFT/NeutrinoC3CyclotomicPriorArtBridgeExact.agda
agda -i . DASHI/Physics/QFT/NeutrinoC3AstrophysicalFlavorNoGoExact.agda
agda -i . DASHI/Physics/QFT/NeutrinoSameLeptonMassOperatorRationalExact.agda
agda -i . DASHI/Physics/QFT/NeutrinoC3FiniteResidualTraceObstructionExact.agda
python -m unittest discover -s tests -p 'test_neutrino*.py' -v
```
Collect exact Agda version, branch SHA, input source SHAs, stdout
and exit code; no missing result should be silently promoted.

**R1 actual finite flavour dynamics**: instead of reconstructing
`S` *from* fitted `U`, choose a source-specific finite group
representation and residual breaking, then **derive** the mass
texture and mixing, including nonzero theta13, the CP phase and
a neutrino mass-squared ratio before looking at the empirical fit.
The trace obstruction rules out the exact rational reconstruction's
literal finite closure and provides a sharp check on new candidates.

**R2 physically continuous action**: construct the complex 3x3
same-lepton-space PMNS with genuine charged-current production,
continuous `L/E` propagation, material effects and physical
detector response.  The current Agda matrix is rational and CP-even,
although the earlier Python PDG numerical bridge can calculate
CP-odd vacuum observables.

**R3 model-to-data same-object comparison**: obtain versioned NuFIT
published correlated Δχ² grids and their re-use licence, then test
literal `1/31` NO and IO conventions and any pre-registered texture
models.  The previous NO *marginal* interval comparison was valid but
is NOT a 2D confidence-level fit.

**R4 high-energy flavour verification**: use IceCube Collaboration
PRL 137, 081002 (2026), original event/topology-level flavour
likelihood and nuisance parameters; source pion/neutron hypothesis
posteriors, not a loose Euclidean distance to the published best-fit
triplet.  IceTracks-DR2-v2 is a separate point-source dataset.

**R5 Monster/369 only on an actual consumer**: require a literal
equivariant map of the physical lepton mass operators into any
C3/3B/VOA/729 model, preserving spectrum, charged-current
couplings, symmetries and observable predictions.  Otherwise
reuse the cyclotomic scalar as mathematics, not an identification.

### Further Pareto contraction: Galois-trace obstruction needs less machinery

A stronger (and shorter) proof of the same **specific** infinite-group
conclusion uses the original `C3CyclotomicAmplitudeAlgebraExact.trace`
already in DASHI.  For `z=a+bζ` in `Q(ζ)`, the field trace is

```
Tr_{Q(ζ)/Q}(z) = z + conjugate(z) = 2a-b.
a = 213694885170400/181846007130841
b = 55365974464882/181846007130841

2a-b = 372023795875918/181846007130841
     = 2 + 8331781614236/181846007130841
     ∈ (2,3).
```

If `TS1` had finite order, its eigenvalues would be roots of
unity and `z=tr(TS1)` would be an algebraic integer.  The
field trace of an algebraic integer is an integer.  Since its
computed field trace lies strictly between the consecutive integers
2 and 3, `TS1` cannot have finite order.  Hence the group generated
by `T,S1` is infinite.  This route does **not** require the
stronger full ring-of-integers classification
`O_{Q(ζ)}=Z[ζ]` as a separate hypothesis.

`NeutrinoC3FiniteResidualTraceObstructionExact.agda` now
records the source-derived `2A-B=372023795875918` and both
strict bound comparisons.  The committed Python regression
`test_galois_trace_noninteger_stronger_finite_order_no_go`
independently reconstructs the coefficient from the exact rational
residual S1 and checks nonintegrality.

**Proof-status separation:** exact numerators and rational
inequalities are source-written Agda + independently evaluated
integer calculations; the general theorem "finite order =>
algebraic-integer trace => integral Galois trace" has **not yet
been formalized or kernel-verified in this repo**.  The mathematical
paper-and-pencil consequence follows from those standard
number-theory facts, and the original literature is attributed.
It is an obstruction only for the specific rational
reconstruction, NOT a new impossibility proof for all finite
flavour symmetries.

The new rational reconstruction is also **CP-even**:
`jarlskogImaginaryPartIsZero` is source-written in the same-lepton
module, and `commutatorElectronMuonNonzero` displays the genuine
charged/neutral mass-basis difference.  Thus the current model
pays a nontrivial same-space operator calculation while keeping
the separate physical CP requirement explicitly unpaid.

### Ownership/no-duplication rule

Do not make a new `C3`, `Z[ζ]`, 27-site hypervoxel,
bounded evidence database, proof authority system, or new
"neutrino zero" species for this direction.  The exact
bounded reconstruction is a **consumer** of the original phase
algebra and an **adversarial countermodel** against extrapolating
any compatible `Z3` plus `Z2×Z2` residuals to a finite
group.  Original IceCube observational authorship and global-fit
parameter provenance remain separate from these new calculations.

## 24 October 2026 max-cut round 5 — RECOVERY of existing CP-violating sector

### Corrected prior-art verdict: CP algebra and Jarlskog already existed

The previous roadmap statement that "the CP-violating sector is absent"
was overly broad.  Source inspection on the repository's base
`master` found these original owner modules and their actual scope:

| Existing source file | Owned prior art | Negative/promotional scope |
| --- | --- | --- |
| `DASHI/Physics/Closure/CPPhaseStructuralOriginReceipt.agda` | Atkin–Lehner `w7` action on the CM `D=-7` point, `arctan(sqrt(7))` structural CP candidate | `physicalCPPhasePromoted=false`, Yukawa eigenbasis and physical CP authority missing |
| `DASHI/Physics/Closure/CPPhaseFromArcTanSqrt7Receipt.agda` | One-loop-corrected candidate phase `1.1596 rad` | diagnostic only; physical CP and CKM promotion false |
| `DASHI/Physics/Closure/CKMGateAbRetirementReceipt.agda` | Experimental tension and isogeny audit of pure CM CKM angle | pure `arctan(sqrt(7))` physical CKM-angle claim **retired** after 5.4σ HFLAV 2023 comparison |
| `DASHI/Physics/Closure/HeckeCharacterPhaseReceipt.agda` | Nontrivial `p=29` Hecke character CP-phase diagnostic | wrong physical phase comparison, no phase authority, physical promotion false |
| `DASHI/Physics/Closure/Y13ComplexEntryReceipt.agda` | Complex `Y_{13}` Yukawa texture entry with phase candidate | `y13PhysicalValue=false` and `physicalCKMPromoted=false` |
| `DASHI/Physics/Closure/JarlskogDiagnosticAnalysis.agda` | Jarlskog invariant diagnostic and error budget | 11.26× CKM target overshoot and unresolved eigenbasis; `physicalCPDerived=false` |
| `DASHI/Physics/Closure/CKMPredictionFrontierReceipt.agda` | Genuine symbolic CKM/Jarlskog requirements | no physical numeric phase or Jarlskog derived |
| `DASHI/Moonshine/C3CyclotomicAmplitudeAlgebraExact.agda` | Exact `Q(ζ3)` multiplication, conjugation and norm | valid universal complex-phase donor, *not* itself a leptonic mass operator |

The new lepton CP route **imports** the canonical CKM phase/Jarlskog
receipts, explicitly preserving their promotion-false proof fields.
It also reuses the SAME `Q(ζ3)` scalar owner rather than reconstructing
a phase ring.  A CKM-specific Hecke phase is **not** mapped to a
physical PMNS phase by shared notation or modular analogy.

### New exact complex same-lepton-space construction

`DASHI/Physics/QFT/NeutrinoExistingCPSectorLeptonBridgeExact.agda`:

- Uses already-selected Pythagorean rational sine/cosine fixtures
  `(161/289,240/289)`, `(240/1609,1591/1609)`,
  `(20/29,21/29)`.  These are **post-hoc near-data inputs**.
- Replaces the previous real `δ=0` operator with the standard
  three-flavour PDG complex matrix `U=R23 R13(δ) R12`, where
  **`exp(+iδ)=ζ3`** and `exp(-iδ)=ζ3²`.  This is an
  intentionally fixed, testable **δ=120° toy branch**, NOT a
  first-principles angle selection or a transported CKM phase.
- Gives **9 closed row- and 9 closed column-unitarity proof clauses**
  over the existing rational cyclotomic algebra.
- Builds `Hν=U diag(0,7537,251100) U†` on the SAME chosen
  lepton flavour basis (mass-squared units 10^-8 eV²), with 9
  corresponding exact eigenvector clauses.
- Defines the rephasing-invariant quartet
  `Q=U_e1 U_mu2 conj(U_e2) conj(U_mu1)` and proves its exact
  cyclotomic ζ coefficient:
  ```
  coeff_ζ(Q) = 9859116742272000/292590225473523169
             ≈ 0.03369598805
  Im_C(Q)    = sqrt(3)/2 * coeff_ζ(Q)
             ≈ +0.029181581660378.
  ```
  The ordinary-complex imaginary part requires the standard
  analytic embedding `ζ=-1/2+i*sqrt(3)/2`.  The rational
  cyclotomic coefficient and its nonzero status are exact algebraic
  facts in the selected model.  CP conjugation `ζ↔ζ²` flips its
  sign while keeping the mixing angles fixed.
- The source explicitly imports the original CKM diagnostics and
  demonstrates their `false` promotion flags, retaining the
  quark/lepton same-object boundary.

**Source-written** proofs are not described as Agda-kernel verified.
Independent Python `Fraction` evaluation of the exact `Q(ζ)`
operations passed **9/9 row unitarity, 9/9 neutral eigen equations,
exact quartet coefficient and conjugation sign**, using the
independently specified original mixing formulas.

### Full CP-sensitive weak-basis invariant, not merely a phase label

`DASHI/Physics/QFT/NeutrinoExistingCPMassCommutatorExact.agda`
defines the **same-space** charged and neutral squared-mass
commutator for `H_l=diag(1,4,9)` (**arbitrary illustrative masses**,
not empirical charged lepton mass inputs):

```
C = [H_l,H_nu] = H_l H_nu - H_nu H_l
Tr(C³) = 3(C_eμ C_μτ C_τe + C_eτ C_τμ C_μe)
```

This yields an exact nonzero CP-odd cyclotomic value:

```
coeff_ζ(Tr(C³))
 = 3272103619391689547963065344000000
   /292590225473523169

coeff_ζ(Tr(C³))/coeff_ζ(Q)
 = 331886081170152000
 = 6 * (charged mass-difference product)
     * (neutrino mass²-difference product)
```

It is **pure imaginary** after embedding in ordinary `C`;
complex conjugation flips its sign.  This explicitly links
CP violation to a noncommuting *pair of mass operators* rather
than merely assigning a complex character to a state.

Historical priority belongs to **Cecilia Jarlskog**:
*Phys. Rev. Lett.* **55**, 1039 (1985),
https://doi.org/10.1103/PhysRevLett.55.1039
and *Phys. Rev. D* **35**, 1685 (1987),
https://doi.org/10.1103/PhysRevD.35.1685.
Our new computation is an **example/consumer** of that standard
invariant, not discovery of the CP test or a physics measurement.

### Adversarial finite-group check still fails WITH CP violation

`DASHI/Physics/QFT/NeutrinoExistingCPFiniteResidualNoGoExact.agda`
uses the same charged `T=diag(1,ζ,ζ²)` and neutrino
`S1=U diag(1,-1,-1)U†=2|u1><u1|-I`.  The field trace
of `tr(TS1)` can be reduced to

```
Tr_{Q(ζ)/Q}(tr(TS1))
 = 3 S1_ee + 1
 = 6 |U_e1|² - 2
 = 442358853598/216225930001
 ∈ (2,3).
```

It is **unchanged** from the earlier real `δ=0` example
because `U_e1=c12 c13` is fixed, despite the new nonzero J.
The standard finite-order/algebraic-integrality theorem consequently
makes `TS1` infinite-order **for this chosen exact model**.
Hence a nonzero Jarlskog does NOT by itself construct a finite
group selecting the mixing angles.  Only the explicit arithmetic
has source-written Agda proofs; the number-theory theorem itself
remains an external mathematical input awaiting an Agda authority.

### IceCube: a stronger CP-identifiability no-go

`DASHI/Physics/QFT/NeutrinoExistingCPAstroConjugationNoGoExact.agda`
reuses the **existing**
`C3CyclotomicAmplitudeAlgebraExact.normConjugationInvariant`
theorem to establish

```
Pbar_ab(U) = Σ_i |U_ai|² |U_bi|² = Pbar_ab(conj(U))
f_earth(U,source) = f_earth(conj(U),source)
```

for **every** rational source flux triple, even though
`J(U)=-J(conj(U)) != 0`.  Thus the CP-conjugate
`δ=+120°/-120°` models are **exactly degenerate** in
standard long-baseline **phase-averaged vacuum** flavour
composition.  IceCube's PRL 137 (2026) 081002 arrival-flavour
measurement, however valuable for source models, cannot *by itself*
resolve that CP-odd sign under the stated standard approximations.
An actual matter, energy-dependent, or coherent CP-sensitive
observable is needed.  No event-likelihood work has been performed.

Independent Fraction calculation gives for pion source `(1:2:0)`
`(.331059,.337086,.331855)`; pure neutron source `(1:0:0)`
`(.547260,.222958,.229782)`, identical for complex-conjugate U.
These model ratios differ from the independently computed
`NuFIT central δ=212°` benchmark, as expected: they are
**not derived empirical PMNS predictions**.

### Source updates (specific CP observational root)

- PDG 2025 neutrino mixing review explicitly defines the
  leptonic Jarlskog rephasing invariant, discusses CP-phase
  uncertainties by ordering and separates it from Majorana phases:
  https://pdg.lbl.gov/2025/reviews/rpp2025-rev-neutrino-mixing.pdf
- NuFIT 6.1 (2025), data files and global CP dependence:
  https://www.nu-fit.org/?q=node%2F309
- T2K **15 September 2026** original experiment update
  https://t2k-experiment.org/publications/results-from-the-t2k-experiment-on-neutrino-mixing-including-a-new-far-detector-muon-like-sample/
  reports a normal-ordering best-fit `δ_CP=-2.18 rad` with
  strong uncertainties.  This is independent original experimental
  source context; no broad CP discovery is inferred here.
- Vladimir Tello, "*Strong CP phase and the PMNS phase in Dirac
  left-right symmetry*", accepted by *Physical Review D*
  **19 October 2026**, https://doi.org/10.1103/mmvw-gcct ,
  develops conditional CKM/QCD–PMNS **theory-specific**
  correlations under generalized parity and a leptonic reality
  constraint.  Interesting for *conditional* same-object
  cross-sector work, but none of those physical assumptions has
  been built or shown to hold in DASHI.  It does not license
  direct equality of a Hecke CKM phase and a neutrino phase.

### Refined max-cut priority

**Paid mathematically at source/integer-execution level:** existing
complex-phase and CKM CP owners recovered; nonzero lepton-sector
Jarlskog quartet; actual complex Hermitian neutral mass-squared
operator diagonalized by selected U; nonzero CP-odd mass-commutator
cubic trace; persistent finite-group no-go; all-source phase-averaged
CP-conjugation degeneracy.  Retain the 2026 original IceCube,
T2K, NuFIT and PDG authorities separately.

**Open R0:** exact-head Agda compiler/typechecking of
`NeutrinoExistingCPSectorLeptonBridgeExact.agda`,
`NeutrinoExistingCPMassCommutatorExact.agda`,
`NeutrinoExistingCPFiniteResidualNoGoExact.agda`,
`NeutrinoExistingCPAstroConjugationNoGoExact.agda`;
run checked-out `test_neutrino_existing_cp_sector_bridge.py`.
Any claimed `solve []` proof is SOURCE-WRITTEN until kernel receipt.

**Open R1:** choose a **specific** residual/CP transformation and
finite flavour-group representation *before* fitting U, derive
the complex weak-basis mass operators and PMNS nonzero J with
bounded parameters; the chosen 120° phase is a model hypothesis,
not a consequence of C3 alone.  Test the finite-group trace
obstruction and any residual breaking.

**Open R2:** physical charged lepton Yukawas, weak charged-current
production/detection, continuous vacuum and matter propagation,
including neutrino vs antineutrino asymmetry; numerical CP-odd
invariant by itself does not imply an observed effect.

**Open R3:** official NuFIT6.1 correlated `χ²`/CP and
T2K+NOvA likelihoods, preserving source/non-overlap; profile all
phases/orderings and any parameter-free candidate.  Never fit an
unversioned `δ=120°` to a 2026 best-fit point by assertion.

**Open R4:** IceCube PRL 2026 arrival flavour likelihood is
CP-sign-blind under standard vacuum averaging, so prioritize
CP-sensitive beam data for the leptonic invariant; keep
IceTracks-DR2-v2 source-location dataset as its separate consumer.

### Source-verified CP round evidence receipt

Independent *exact-source* V8 BigInt/Fraction-style rational computation
on the branch read-back (no network source substitution) is preserved
at

`logs/research/neutrino_existing_cp_maxcut_exact_source_receipt_20261024.json`.

This receipt binds the exact GitHub **blob SHAs** for the four newly
added Agda modules and the Python test.  It extracts the **six**
rational mixing inputs from the Agda source; independently evaluates
15 exact algebraic checks, including:

- complex row/column unitarity of `U` and mass-squared diagonalization;
- nonzero `Q(ζ)` Jarlskog coefficient and sign under conjugation;
- actual cubic charged/neutral squared-mass commutator trace
  and its `331886081170152000` proportionality factor;
- the nonintegral C3 residual finite-group Galois trace in `(2,3)`;
- all 9 original Born norm-conjugation identities; phase-averaged
  CP invariance follows algebraically from those identities, not
  an independently acquired astrophysical data set;
- four original CKM CP/nonpromotion-owner imports are visible.

**PASS** exact-source rational arithmetic; **NOT RUN** Agda kernel,
checked-out Python tests, NuFIT official correlated likelihood,
T2K original CP profile reanalysis, IceCube event likelihood,
and the abstract number-theory finite-order trace theorem in Agda.
The receipt deliberately does not elevate a source-written
`solve []` clause to a kernel typecheck.

**What is now genuinely solved:** the mathematical existence of
a nonzero complex leptonic CP-odd invariant on the SAME explicit
charged/neutral operator example, and two discriminating mathematical
no-go results (infinite selected residual group; IceCube phase-average
blindness to CP-conjugation sign).

**What is not solved:** predicting the physical PMNS CP phase from
DASHI C3/Monster/Hecke, finding a finite group whose actual lepton
residual action selects the observed mixing, physical lepton
masses/Yukawas, or reproducing experimental CP-violation likelihoods.

## 24 October 2026 — max-cut: horned-sphere infinite order versus neutrino residual infinite order

### Correct source object and attribution

Sibling <https://github.com/chboishabba/dashi_agda/pull/1244>
is a different, not-yet-merged PR whose genuine prior art had been
overlooked in the previous lepton-flavour roadmaps.

Original classical source: **J. W. Alexander (1924)**,
the horned sphere; **Allen Hatcher**, *Algebraic Topology*,
Example 2B.2, pp.170–172, owns the direct-limit free-group
commutator construction of the horned exterior.  Hatcher's
nontrivial group is locally free and **perfect**, and is
**torsion-free** because every nonidentity element comes from a
nonidentity free-group element that survives an injective tower
map.  In particular a selected meridian `m` has
`m^n != 1` for all positive integers n, although it is
itself an iterated commutator at arbitrarily deep levels.

**N. W. Riebe (1968)** provides related but *different*
horned-sphere constructions and A5 representation prior art;
Riebe's examples must not be conflated with Hatcher's
abstract perfect group or counted as independent observations
of the same physical system.

The three-C3-labelled copy construction is explicitly a new
DASHI group `G = G_A * G_A * G_A`, and its geometric
boundary-connected-sum/exterior identification remains
uncertified by the geometric kernel.  The C3 rotation
`r` satisfies `r^3=id` in `Aut(G)` and defines an exact
order-three class in `Out(G)` under its group-theoretic
noninnerness argument.  It is **not an internal order-three
element of the torsion-free G**.  The semidirect
extension `G ⋊_r C3`, in contrast, *does* include an
internal rotation element of order three.

Because `G` is perfect, all Abelian characters
`G → U(1)` and `G → C3` vanish, even though
the nonabelian quotient `G → A5³` and the
external rotation are nontrivial.  Three matching phase
labels cannot create a nontrivial horned-loop-to-PMNS
Abelian character.

### Important bug found AND fixed upstream in PR #1244

Two A5 quotient probes selected the first nonidentity
commutator of a pair generating A5.  An independent finite
permutation audit found that the *original selected root*
was `(2,1,3,0,4)`, which has **order three**.
This invalidated the VOA probe's asserted `order(root)==5`
and made its selected `m^5` kernel witness unsupported.
The general compatible finite A5 quotient remained valid,
but the claimed particular fifth-power witness required
correction.

Both owner-side scripts were fixed to require a
generating commutator of **order five**, selecting

```
g=(2,0,3,4,1)
a=(0,1,3,4,2)
b=(2,3,0,1,4)
[a,b]=g; <a,b>=A5; g^5=1.
```

An upstream regression
`tests/test_alexander_horned_c3_a5_order_selection.py`
now asserts the two source scripts choose the **same**
order-five root. The corrected files were read back from
GitHub branch `alexander-horned-c3-equivariant-20261024`;
their full committed Python script and Agda/Lean kernel
suites have not been rerun.  The independent original
order-three and corrected order-five finite permutation
calculations **were** executed and passed locally.

### Sharp new cross-PR no-descent: fifth powers do not match

The selected quotient actor sees `q(m)=g` with
`g^5=1`.  The selected nonzero-CP neutrino residual
operator is

```
T=diag(1,ζ,ζ²)
S1=U diag(1,-1,-1) U†
A=T S1
```

Here the post-hoc `U` and its CP phase `120°`
are inherited from the **same** exact lepton toy model
within PR #1247, not observed horned topology.

Independent local `Fraction` arithmetic using
`Q(ζ)`, `ζ²=-1-ζ`, computed `A^5`
without floating-point approximation.  Its `(e,e)`
entry in ordinary complex numbers is approximately

```
(A^5)_ee = 0.3402566114304599 - 0.11598500790728489 i
```

so **`(TS1)^5 != I`** exactly.  The full exact
rational `(1,ζ)` coordinates and source blob SHAs
are preserved in
`logs/research/neutrino_horned_fifth_power_cross_pr_receipt_20261024.json`.

The source-written conditional theorem
`DASHI/Physics/QFT/NeutrinoHornedExteriorFifthPowerNoGoExact.agda`
proves a mathematically genuine group-homomorphism fact:
for any actor-to-matrix homomorphism, a source actor's
fifth-power identity propagates to its matrix image.
Consequently, the **selected** finite `A5³` quotient
meridian cannot map to `TS1`, because that would force
`(TS1)^5=I`.  This is sharper and more constructive
than merely invoking the nonintegral Galois trace.

`tests/test_neutrino_horned_fifth_power_bridge.py`
is the corresponding source-written exact Python regression,
pinning the corrected root and the `TS1^5` witness.
It has not received an exact-head committed test-run receipt.

### What the cross-PR result does and does not establish

It **establishes** three compatible, different kinds of order:

1. Infinite-order loops in torsion-free `G`.
2. An order-three **outer automorphism** and finite
   `A5³ ⋊ C3` actor that can forget nontrivial powers.
3. An infinite-order **matrix** operator `TS1` from
   the constructed, CP-nonzero lepton Hamiltonian.

It **excludes** the specific claim that our currently
constructed finite `A5³` VOA actor transports its
order-five quotient meridian to this particular `TS1`.

It **does not exclude** a different, infinite-image,
nonabelian representation `G → SU(3)` or another lepton
Hilbert-space action.  Such a construction would have to
provide: compatible images for *every* commutator
refinement `m_w=[m_(w0),m_(w1)]` on one group action;
actual C3 **semidirect-equivariant** transport
`ρ(r(g))=Tρ(g)T^-1`;
an appropriately defined physical lepton
Hamiltonian/charged-current coupling; and a measured
discriminator.  It cannot bypass perfectness with a
scalar `G→C3` map, nor get physical mass predictions
from group element order alone.

The original Hatcher group, three-copy geometric
realisation, `A5³` finite quotient, VOA action,
lepton PMNS matrix and astrophysical observation
must remain separately attributed to their actual
mathematical, source-written, kernel and experimental
authorities.

### Pareto cuts paid, next gates

**Paid:** original horned topology and group owners
recovered; independent source-root distinction with Riebe;
contradictory A5 root-order assertion discovered and
fixed on **its owner branch**; exact fifth-power
matrix witness; consumer-side conditional Agda no-descent;
source-bound cross-PR evidence receipt; both roadmaps updated.

**Open:** exact-head Agda/Python and Lean kernel jobs on
both branches; genuine geometric `π1` isomorphism of
the three-copy wild exterior; actual nonabelian
`G→SU3` compatible commutator-tower action if worth
pursuing; real, calibrated charged-current neutrino
physical model; correlated NuFIT/T2K/IceCube data fits.
Finite VOA versus V-natural and Monster recognition
are separate downstream questions—not entitlements
from a shared (C3) glyph.

Run on their respective checked-out branch heads:

```sh
# Horned owner PR #1244
python3 scripts/alexander_horned_c3_a5_probe.py
python3 scripts/alexander_horned_c3_voa_a5_action_probe.py
python3 -m unittest discover -s tests -p 'test_alexander_horned_c3_a5_order_selection.py' -v

# Neutrino CP consumer PR #1247
python3 -m unittest discover -s tests -p 'test_neutrino_horned_fifth_power_bridge.py' -v
agda -i . DASHI/Physics/QFT/NeutrinoHornedExteriorFifthPowerNoGoExact.agda
```

## 24 October 2026 — breakthrough / positive horned-SU(3) infinite-image representation

### Prior impasse resolved, but *physical* prediction does NOT follow

Earlier: a selected horned-source meridian `m` has
infinite order, but the selected finite `A5³`
quotient sends `m` to an order-five element and
therefore cannot send its quotient meridian to the
CP-nonzero lepton residual `A=TS1` with `A^5!=I`.
That finite-quotient no-go is still valid.

**New positive mathematical result:**
Original theorem by **Morikuni Gotô**,
*A Theorem on compact semi-simple groups*,
*J. Math. Soc. Japan* **1** (1949), 270–272,
https://doi.org/10.2969/jmsj/00130270 :
every element of SU(3), a connected compact semisimple
Lie group, is a single group commutator.

Hatcher's original *Algebraic Topology* Example 2B.2
defines the Hatcher horn exterior abstract group as
an injective direct limit of free groups with
`x_w ↦ [x_w0,x_w1]`.
An arbitrary chosen `A∈SU(3)` admits a commutator
factorization `A=[X,Y]` by Gotô.
Choose new pairs recursively for *all* descendants.
Each stage assignment is compatible with the actual
Hatcher generator substitution, so the group colimit
universal property supplies an honest
`rho_A:G_A→SU(3)` with `rho_A(m)=A`.
This is NOT a map through the finite A5³ quotient.

More constructively, choose
`A=V diag(λ0,λ1,λ2)V†`
with determinant 1, `P` the determinant-one
3-cycle permutation matrix, and `D` diagonal
with eigenvalues proportional to
`(1,1/λ1,λ0)`; then
`[P,D]=diag(λ0,λ1,λ2)`, and
`[V P V†,V D V†]=A`.
Normalize `det(D)=1` by a common cube-root phase.
This formula makes the classical Gotô SU(3) case
explicit rather than merely assuming surjectivity.

### The chosen CP-nonzero neutrino operator is an exact SU(3) input

**New** `NeutrinoHornedSU3RootExact.agda` reuses
`NeutrinoExistingCPSectorLeptonBridgeExact` and
the canonical Q(ζ3) algebra:

```
U = PDG-type selected complex 3x3 PMNS fixture, δ=+120deg
T = diag(1,ζ,ζ²),                   T³=I
S1 = 2 |u1><u1| - I
A = T S1
```

The new source expresses all **18** two-sided
unitarity clauses and an explicit 3×3 determinant
formula `det(A)=1` over exact Q(ζ3).
Separate independent Python **Fraction** arithmetic
verified, on precisely the same six rational angles:

```
U U†=I; U†U=I
S1†=S1; S1²=I; det(S1)=1
A A†=I; A†A=I; det(A)=1
A^5 != I
Tr_{Q(ζ)/Q}(tr(A))
 = 442358853598/216225930001
 ∈ (2,3).
```

The trace and algebraic-integer theorem from the
earlier PR work imply `A` has **infinite order**;
the exact fifth-power calculation is an
independent bounded witness. Thus
`rho_A(G_A)` is infinite. Since `G_A`
is perfect, its nontrivial image is **perfect
and nonabelian**. No conflict with the previously
proved absence of nontrivial Abelian
`G_A→U(1)` characters.

### Same 3D complex space and exact threefold symmetry

For the new three-root abstract free-product
`G=G_A * G_A * G_A` used in horned **PR #1244**,
assign to factor `j` the conjugate representation

```
rho_j(g) = T^j rho_A(g) T^{-j}.
```

Because `T³=1` this intertwines the
cyclic factor rotation `r` and the target
inner action `Ad_T`.
The semidirect product homomorphism is

```
R : G ⋊ C3 -> SU(3)
R(g,j)=rho(g) T^j
R(r)=T
R(m_(0,empty))=A=TS1.
```

In particular the image **contains S1=T^-1 A**,
as well as T, and is infinite and nonabelian.

That is a genuine positive **abstract group
representation existence** construction, not
merely same cardinality, a braid permutation
shadow or a finite quotient.
The fact that the C3 rotation is *outer in
the source* but acts by conjugation in
ambient SU(3) is not a contradiction:
outer-ness is relative to the *source group*;
the target representation need not preserve it.

Existing original mathematical source owners,
not the new analysis, retain authorship of
the group-colimit universal property,
Gotô commutator theorem, and standard Jarlskog
CP invariant.

### Critical discriminator: mathematically too universal

The horned representation can send its chosen
meridian to **EVERY A∈SU(3)**, not just the
120-degree leptonic matrix. Therefore the
existence result has **no ability by itself**
to select a real-world CP phase, neutrino mass
ratio or mixing angles.  It solves only an
**existence/interface impasse**, NOT physical
neutrino or Monster/VOA identity.

A genuinely predictive follow-on would require
source-specific and independently motivated
selection constraints: a geometric connection or
holonomy choice, regularity/energy functional,
actual lepton Yukawa/mass textures, a charged-current
map, an action preserving the right physics, and
a measured likelihood discriminator. A flat
SU(3) representation, if eventually realized on
a verified smooth horned complement, is not by
itself a Yang–Mills/Einstein/PMNS dynamics model.

### Code locations and independent finite checks

**Existing horned owner PR #1244:**

- `DASHI/Mathematics/Topology/AlexanderHornedC3CompactCommutatorRepresentationExact.agda`
  imports the native HornAddress/Word, constructs
  recursive commutator images at *every* finite
  address, proves word-expansion compatibility
  and C3 rotational equivariance conditional
  on a supplied commutator section and target
  automorphism. Source-written Agda.
- `scripts/alexander_horned_c3_su3_constructive_probe.py`
  computes the explicit Schur-spectral SU(3)
  commutator factorization; no full test-run
  receipt of the **committed** script yet.
- `logs/research/alexander_horned_su3_goto_constructive_receipt_20261024.json`
  binds author/source roles, cross-PR blobs and
  independent numerical evidence.

**Neutrino target owner PR #1247:**

- `DASHI/Physics/QFT/NeutrinoHornedSU3RootExact.agda`
  source-writes 18 unitarity equalities and
  exact determinant-one of the chosen root.
- `tests/test_neutrino_horned_su3_positive_bridge.py`
  exact Q(ζ3) Fraction regression verifying
  determinant, unitary, CP quartet, finite
  powers and threefold equivariance (NOT YET
  run as an exact-head committed test).
- Existing CP, finite-order Galois trace,
  source likelihood, and negative A5 quotient
  modules remain unmodified and attributed.

The independent **locally executed** NumPy/SciPy
construction measured five levels, **31**
commutator parent relations and 32 leaves,
worst residual `4.99e-15`, max determinant
defect `2.56e-15`. A separate eight-level
run checked 255 parent relations and 256
leaves, worst residual `7.84e-15`. All
three conjugate sector root refinements
held to residual `<4.8e-15`.
The exact algebraic check of `A∈SU3`
used Python Fraction, not floats. No
claim about uniform all-depth numerical
error, closure/density, continuity of
the chosen section, or experimental data.

### Reprioritized paid/open boundary

**NOW PAID in ordinary mathematics:**
an infinite-image, nonabelian C3-equivariant
representation of the abstract 3-sector Hatcher
horn group into SU(3), with the *specific*
CP-odd selected neutrino `TS1` as a root
meridian image and T as its rotation generator.
This was previously an open existence question.

**STILL OPEN:**
exact-head Agda compilation of these new
source-written proofs; formal source-group
colimit/universal property and spectral/Gotô
theorem in Agda/Lean; exact-head committed
Python regression execution; the actual
wild 3-ball geometry / pi1 and flat-connection
selection; a literal physical lepton/charged
current operator intertwiner; finite-energy
dynamics and experimental PMNS CP/angle
likelihood comparisons. The mathematical
existence proof **does not predict** any of
the observed parameters.

Run on their respective branch heads:

```sh
# PR #1244
python3 scripts/alexander_horned_c3_su3_constructive_probe.py
agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3CompactCommutatorRepresentationExact.agda

# PR #1247
python3 -m unittest discover -s tests -p 'test_neutrino_horned_su3_positive_bridge.py' -v
agda -i . DASHI/Physics/QFT/NeutrinoHornedSU3RootExact.agda
```

## 24 October 2026 max-cut: the existing DASHI SU(3)/Lie-group stack WAS the owner

### Reuse-first audit results

The earlier phrase "construct a new SU(3) group and adjoint"
was an incorrect ownership assumption. The canonical base
repo already defines:

- `DASHI/Physics/YangMills/SUNMatrixCarrier.agda`:
  `CertifiedSUNMatrixTheory`, `IsSpecialUnitary`,
  `SUNMatrixElement`, `sunMatrixGroup`.
- `SUNMatrixLieAlgebra.agda`: traceless anti-Hermitian
  matrix Lie bracket `XY-YX`.
- `SUNMatrixLieGroup.agda`: group adjoint
  conjugation, exponential/logarithm authority.
- `SU3MatrixInstance.agda`: literal N=3 specialisation,
  dimension eight, `su3MatrixGroup`.
- `CompactLieGroupCore.agda`,
  `CompactLieGroupDerived.agda`:
  generic group and existing conjugation laws.
- `CompactLieAnalyticPackage.agda` and
  `CompactLieStandardAuthority.agda`:
  explicit **standardImported** topological/analytic
  authorities, not privately kernel-proven construction.
- `QutritMatrixGates.agda`:
  nine-cell `Matrix3`, qutrit phase/cycle gates,
  potential finite-matrix record donor; not yet
  certified as the SU3 carrier.

The necessary horn generator substitution is a **GROUP**
commutator `xyx^{-1}y^{-1}`, not the Lie-algebra
bracket `XY-YX`. Gotô (1949) applies to the former.
Separate later Lie-algebra results cannot substitute for it.

### Concrete new Lie-transport code

Sibling horn owner PR **#1244** now contains:

`DASHI/Physics/YangMills/CompactLieInnerC3Exact.agda`
with source-written proofs of the inverse-of-product,
composition-of-inner-conjugation and **T³=I ⇒ Ad_T³=id**,
reusing canonical `CompactLieGroupCore.Group` axioms.
`DASHI/Mathematics/Topology/AlexanderHornedC3SUNLieGroupReuseExact.agda`
uses original `CompactLieGroupDerived` to derive
conjugation-preservation of inversion and
group commutators, then binds the *existing*
`SU3.su3MatrixGroup` directly into the horned
recursive-address representation.  The imported
Gotô commutator section remains explicit.

This removes separately assumed algebraic laws
from the source horn representation rather than
reencoding them under a new symbol.

**Lepton owner PR #1247** now contains:

`DASHI/Physics/QFT/NeutrinoHornedSU3RootExact.agda`
supplemented with exact, nine-clause-per-identity
matrix evidence for
`T†T=TT†=I`, `det(T)=1`,
and `T³=I` using the literal existing
`Q(ζ3)` algebra.

`DASHI/Physics/QFT/NeutrinoExistingSUN3CarrierWeldExact.agda`
then consumes the actual YM
`CertifiedSUNMatrixTheory 3`,
not a shadow group. It **derives** rather than
assumes `IsSpecialUnitary(TS1)`,
`IsSpecialUnitary(T)`, and the
`Group`-valued `T³=I` law directly from
the existing 18+18+9 pointwise cyclotomic
root/rotation proofs, using transport lemmas
for matrix multiplication, dagger, determinant,
identity and scalar one.

### Exact status of the *last* concrete matrix gap

The weld is a **conditional** theorem:
`ExactLeptonSUN3Weld` is a record of

1. an existing certified matrix theory specifically
   for `Flavour→Flavour→Q(ζ3)`;
2. equations matching its operations with the
   explicit lepton `productMatrix`, adjoint,
   determinant, identity and one;
3. function-matrix extensionality to turn
   `∀a b, M a b=N a b` into `M=N`
   at the raw function matrix type.

None of those authority fields has been falsely
filled by a `refl` or fabricated from a
`Bool true` certificate. The repository's
generic `SU3MatrixInstance` gives the
**group assembly once supplied** matrix laws,
not an automatic concrete nine-cell Q(ζ3)
matrix realization.  Existing ternary finite
function owners explicitly distinguish pointwise
invariance from propositional function equality.
Alternatively, the actual nine-cell
`QutritMatrixGates.Matrix3` donor could remove
the function-extensionality need if full field,
matrix and group laws were certified on it.

**Independent local exact Fraction check PASS**:
`U†U=UU†=I`,
`S1†=S1`, `S1²=I`,
`A†A=AA†=I`,
`det(A)=1`,
`T†T=TT†=I`,
`det(T)=1`,
`T³=I`,
and `Ad_T³(A)=A`.
The 45 selected entry equalities for A and T
were independently confirmed using the
specific earlier rational angles and ζ coefficients.

**Separate independent finite adversary**:
A5 group of 60 elements, 60/60 commutator
section, 7,200 inner-conjugation identities,
five levels of group commutator horn
refinement under an order-three inner twist:
PASS exact finite permutation arithmetic.
This checks transfer identities, NOT global SU3
commutator-section existence, physical
leptonic CP or the full Agda source.

### Reduced max-cut roadmap

PAID MATHEMATICALLY (ordinary mathematics, sources
attributed): the original group-combinatorics,
the Gotô/Hatcher infinite-image existence result,
the source-selected lepton matrix A∈SU3,
and C3 conjugation-equivariant three-copy action.

PAID AT SOURCE-WRITTEN AGDA LEVEL ONLY:
canonical Group conjugation/inverse/C3
transport, horn adapter into the SAME original
SU3 carrier, 45 explicit cyclotomic target
matrix entries, and conditional proof
transport into `SUNMatrixElement`.

OPEN R0 KERNEL: compile source HEADs of
both PRs, run exact-head committed Python
tests, report version/exit/source hashes.
No Agda executable is present in the
available local execution container.

OPEN R1 CONCRETE MATRIX: fill the named
`ExactLeptonSUN3Weld` input using an existing
nine-cell qutrit matrix type (preferred if
closed) or a certified function matrix theory
with explicit extensionality. This is the
real remaining **algebraic same-object weld**.

OPEN R2 GLOBAL ANALYTIC: import/prove Gotô's
surjectivity and formalize the direct-limit
universal property in the Agda theorem stack.
The math is published, but the kernel socket
has no inhabitant in these new files.

OPEN R3 PHYSICAL: geometry π₁ of the
threefold wild complement and its selected
holonomy, physical lepton mass/Yukawa/charged
current dynamics and independent neutrino
CP/angle/data likelihood predictions.
Mathematical SU3 on flavour labels is
NOT a discovery of QCD colour gauge SU3,
and an arbitrary target element A has
no PMNS parameter-selection power.

Sources: Gotô 1949 DOI
10.2969/jmsj/00130270;
Hatcher *Algebraic Topology* Example 2B.2;
Malkoun and Nahlus, *Journal of Lie Theory*
**27** (2017), DOI 10.5802/jolt.980,
for the DIFFERENT Lie-algebra bracket result.
Existing Yang–Mills, C3/369, CKM, qutrit,
and neutrino source owners retain their
original authorship and theorem grades.

### New exact nontriviality discriminator: the C3 orbit is not collapsed

The chosen `T` has order exactly three, but that alone
would not imply the inner action `Ad_T` moves a
particular `SU3` state: a central element, or a
chosen `A` commuting with `T`, could have
`Ad_T(A)=A` even when `T³=1`.

The `NeutrinoHornedSU3RootExact.agda`
source now computes this exact CP-root witness:

```
A = T S1
(Ad_T(A) - A)_(e,mu)
  = (7429123333440 + 2394922626720*zeta)
      /6270551970029
  != 0.
```

The selected orbit has **exactly three** distinct
points once the group order-three law is transported:
`Ad_T³(A)=A` but `Ad_T(A)≠A`; an orbit
under C3 has size 1 or 3. This is an exact
mathematical group-action distinction,
NOT a measured CP-phase observable or a
proof of physical QCD color/flavour identity.

The committed
`tests/test_neutrino_horned_su3_positive_bridge.py`
now includes the exact two-coordinate Fraction
regression for this action. Independent local
Fraction calculation PASS; no claimed Agda
typecheck or exact-head committed test execution.

`logs/research/neutrino_canonical_sun3_matrix_weld_maxcut_20261024.json`
records the latest source/test blob SHAs and
the nonzero two-coordinate witness.

## 2026-10-24 final local-Python max-cut receipt (no CI)

**Verified by executing the exact GitHub Python source bytes**, not
merely reimplementing the arithmetic: the assistant read seven
pre-existing Python files plus the newly written symbolic one
from their original PR branches, reconstructed each locally and
matched its SHA-1 Git blob hash before execution.

`logs/research/neutrino_sun3_local_python_exact_head_receipt_20261024.json`
records all hashes, the Python version and precise tests. Results:

| Concrete local operation | Source-matched result |
| --- | --- |
| Horn A5 order-selector tests | 4/4 PASS |
| Horn compact-Lie group-reuse tests | 4/4 PASS |
| Leptonic exact cyclotomic CP/mass tests | 11/11 PASS |
| Neutrino CP-positive SU3 target tests | 7/7 PASS |
| Combined unittest run | **26/26 PASS** |
| Horn A5 stage script | PASS, 60/60 commutators |
| Horn c=0 finite VOA semidirect action | PASS, 4,000 deterministic cases |
| Horn SU3 spectral commutator probe (5 levels) | PASS, 31 parent relations; worst residual 4.985e-15 |
| Horn SU3 spectral probe (8 levels) | PASS, 255 parent relations; worst residual 7.837e-15 |
| New universal Q(zeta3) 3x3 SymPy symbolic algebra | **10/10 exact symbolic identities PASS** |

New code
`scripts/audit_neutrino_sun3_symbolic_matrix_laws.py`
uses **indeterminate 3x3 matrices over Q(ζ3)** with
`ζ²=-1-ζ` and symbolic polynomial expansion, verifying:

1. Scalar conjugation involutive;
2. Scalar conjugation multiplicative;
3. Left/right matrix identities;
4. Matrix associativity;
5. Dagger involutive;
6. Dagger reverses matrix products;
7. `det(A B)=det(A)det(B)`;
8. `det(A†)=conj(det(A))`;
9. `det(I)=1`.

The split left/right identity makes ten individually tested
boolean certificates. SymPy 1.14.0 reduces every coefficient
difference to the **zero polynomial**, not to an approximate
floating-point residual. This substantially validates the
general finite-matrix laws needed by the existing
`SUNMatrixCarrier.CertifiedSUNMatrixTheory` socket,
at **symbolic external verification grade** only.
Proofs in Agda and the actual function-backed
matrix extensionality or nine-cell record remain open.

Use the symbolic script as an efficient local computational
stand-in **rather than introducing CI**. The original
`CompactLieGroupCore`, `SUNMatrixCarrier`,
`SU3MatrixInstance`, `QutritMatrixGates.Matrix3`
and cyclotomic scalar owners remain authoritative.

**Closed here:** actual committed-script execution and
reproducible branch/blob attribution for the selected 26
cases; universal finite-matrix polynomial-law evidence.
**Open:** Agda typechecking, concrete typed
`ExactLeptonSUN3Weld` instance, imported global
Gotô/colimit proof, physically selected holonomy or
lepton interaction, experimental likelihoods.

## 2026-10-24 final steelman/phase-gate consolidation — supersedes physical C3 orbit promotion

**Decision owner:** `Docs/physics/HornedLeptonC3SteelmanPhaseGate20261024.md`,
with actual SHA-matched local test receipt
`logs/research/neutrino_horn_c3_steelman_phase_receipt_20261024.json`.

**Mathematical phase P2 PAID** (ordinary source-attributed Gotô/Hatcher
group existence, finite tested algebra); **Agda kernel P3 OPEN**;
**same-object wild geometry P3b OPEN**; **physical predictive dynamics
P4 UNSTARTED**; **original-data validation P5 OPEN**.

**Critical falsification of a potential physical claim:**
the exact threefold `Ad_T(A)` matrix orbit is nontrivial,
but `U↦TU` is charged-lepton *row rephasing*. Nine Born
entries, Jarlskog J, all vacuum oscillation probabilities,
decohered source flux and horn single-word Wilson characters
are unchanged. A nontrivial matrix/holonomy orbit is NOT three
physical generations and NOT a new oscillation signal.
The tested source `NeutrinoHornedC3RephasingNoGoExact.agda`
records nine Born clauses, 9 Hamiltonian covariance clauses,
exact CP quartet and character identities, still SOURCE-WRITTEN.

**Second field/analytic obstruction:** Gotô's theorem applies
to connected compact **SU3(C)**, not to the countable
`SU3(Q(zeta3))` subgroup of exact scalar matrices.
For diagonal `T`, one standard cyclic commutator recipe needs
a **ninth root of unity** to restore determinant one;
`Phi9(X)=X^6+X^3+1` is irreducible over Q of degree 6
versus degree 2 for Q(zeta3). This is a *recipe-specific*
field extension witness, NOT a theorem excluding every
rational cyclotomic commutator factorization.
The correct mathematical move is an exact
`Q(zeta3)→C` embedding followed by Gotô in ambient SU3(C).

**Actual local execution upgrade:** 36/36 selected cross-PR
Git-blob-matched tests PASS (prior 26 plus 7 new row-rephasing/
Wilson tests and 3 field-degree tests); 10/10 original symbolic
universal 3×3 Q(zeta3) laws PASS. No CI work, no Agda kernel,
NuFIT likelihood or physical-data claim.

**Next Pareto cut:** a source-specified gauge-invariant
interaction/holonomy discriminator, or explicitly retire
CP-generation physical promotion. Do not manufacture another
C3/Monster/KK analogue to pay a missing physical observable.
See decision register for deliverable owners and acceptance tests.

## 2026-10-24 maximal-return physical steelman: next payoff is regularity

**New decision owner:** `Docs/physics/HornedSU3ObservableRegularityParetoMaxCut20261024.md`.
This replaces the looser "construct one gauge-invariant
interaction" with three *discriminating* targets:
1. Prove actual uniform small-loop geometry, or find
   counterexample, and apply the conditional shrinking
   horn holonomy no-go \(\|U_{root}-I\|\le
   (2\epsilon_n)^{2^n}/2\). If a nontrivial root
   persists while \(\ell_n\to0\), a uniformly
   bounded, smoothly-extendible gauge connection
   on those loops cannot represent it.
2. Reuse the EXISTING `SUNWilsonClassFunction` as
   observable; selected toy \(W=TS1\) has
   \(P_+(0)=434928608401/648677790003\) for a
   specified unpolarized 50:50 SU3 two-arm
   interferometer, not physical neutrino data.
   A single loop on \(S^1\) can reproduce this
   EXACT signal; even an \(F_2\) commutator
   can mimic a finite-depth two-loop test.
   Horn specificity demands nested geometric source.
3. Investigate a renormalized Wilson-line potential
   from original Hosotani sources, not an invented
   minimum: classical \(F=0\) YM energy has a
   flat holonomy selection degeneracy. A vectorlike
   ring model gives a nonzero gauge-invariant
   heat-trace control; actual chiral lepton currents,
   anomaly, boundaries and source geometry remain
   open.

New Agda finite consumer `NeutrinoHornedWilsonInterferenceExact.agda`
records exact character and fringe; Python stand-ins
`tests/test_neutrino_horned_wilson_regularization.py` and
`scripts/check_neutrino_horned_wilson_spectral_selection.py`.
Horn owner #1244 contains
`scripts/alexander_horned_c3_su3_regularization_no_go_probe.py`.
Existing Wilson and B0.2 analytic owners remain canonical.
This neither retracts Gotô/Hatcher abstract existence nor
promotes a quantum experiment/Agda kernel certification.
