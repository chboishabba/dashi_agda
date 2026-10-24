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
