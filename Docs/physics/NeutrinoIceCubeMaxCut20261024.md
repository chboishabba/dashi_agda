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
- An over-generous componentwise rectangular upper ratio:
  `7.823 / 245.0 = 0.0319306122449...`
- Exact integer certificate: `31 * 7823 = 242513 < 245000`;
  gap `2487` in the cross-product numerator; therefore
  `1/31 > 7823/245000`.
- Hence **the exact 1/31 normal-ordering candidate is incompatible
  even with the Cartesian product of the published marginal 3-sigma
  parameter intervals**.  This is *not* a separately calculated
  correlated confidence level or hypothesis-test p-value.
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
