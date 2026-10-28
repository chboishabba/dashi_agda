# Kozyrev mirror: source cut, formal claim registry and test-readiness

**Status, 27 October 2026:** source registration and analysis tooling only.
No apparatus was built or measured. No human trial took place. No physical,
time-related, information-transfer or medical effect is verified.

## Referents and attribution

1. **Nikolai A. Kozyrev** developed historical physical-time hypotheses.
   Those hypotheses neither constitute a test of the later spiral enclosure
   nor imply a working clock or causal anomaly.
2. **Vlail P. Kaznacheev and Alexander V. Trofimov** are the named
   inventors of Russian patent **RU2122446C1**. Filed **1996-07-02**,
   published **1998-11-27**. Preserve them as design/claim owners.
   Primary patent: https://patents.google.com/patent/RU2122446C1/en
3. **Sergei V. Kozyrev** authored the independent mathematical result
   *Wavelet theory as p-adic spectral analysis* (2002),
   https://doi.org/10.4213/im381. The repo's Kozyrev wavelets and
   Vladimirov operators are **not** evidence for mirror effects.
4. **Kaznacheev** (2002) reports mirror-related consciousness claims:
   https://www.physics.socionic.info/index.php/physics/article/view/267
   **Kaznacheev and Trofimov** report distant-information effects:
   https://physics.socionic.info/index.php/physics/article/view/376
   These are **claiming sources**, not independently reproduced proofs.
5. **Broken Branch**, *The Honest Spiral* (2026-09-28) and
   *Does the mirror focus anything?* (2026-10), report bounded **2-D**
   toy-model studies:
   https://www.brokenbranch.dev/labs/as-seen-on-tv/honest-spiral/
   https://www.brokenbranch.dev/labs/as-seen-on-tv/does-the-mirror-focus/
   Credit the external simulation authors for their own code,
   controls, and claims. No data/code was copied into this repo.
   Their earlier alleged +19.05 spiral effect was corrected as an
   unstable-integrator artifact; steady equilibrium net twist was zero
   in the tested model. No three-dimensional apparatus verdict follows.

**Unresolved primary-source contradiction:** RU2122446C1 English *abstract*
lists 0.5 mm aluminium, while the translated patent description/claim
lists 1.5 mm. Both also include a proposed 50 cm focal distance.
Do not collapse the thickness discrepancy without inspecting original
claims/drawings and recording a reconciled edition, units and translation.
A patent is evidence of a described device and dated inventor attribution,
not of treatment efficacy.

## Related external PRs (cross-pollination, not appropriation)

- [benskamps/wormhole-playground #4](https://github.com/benskamps/wormhole-playground/pull/4):
  corrects an earlier spiral angular-momentum assertion to an unstable
  integrator artifact. Reuse the lesson: calibration, stability and
  conservation controls precede any extraordinary interpretation.
- [Lucent-Financial-Group/Zeta #1855](https://github.com/Lucent-Financial-Group/Zeta/pull/1855):
  records a distinct **Kozyrev Mirror / BFT immune-system** *governance
  analogy*, including a three-node threshold claim. It is not
  a physical experiment or an identity bridge. Retain the original
  PR author's ownership; do not promote shared terminology into
  the same apparatus, causal mechanism, mathematical object or result.
- [DavJ/padiclab #9](https://github.com/DavJ/padiclab/pull/9):
  Kozyrev *wavelets* and Vladimirov operators are mathematical prior
  art in a different domain, not a replicate of the mirror.

## Existing repository reuse

- Canonical theorem owner: `DASHI/Empirical/KozyrevMirrorClaimTesting.agda`.
- Existing promotion owner reused:
  `DASHI/Promotion/CrossDomainClaimPromotionBoundary.agda`.
- Existing quantitative prediction/holdout standard (not instantiated):
  `DASHI/Empirical/GRQuantumPredictionProtocol.agda`.
- Distinct mathematical precedent:
  `DASHI/Physics/Closure/GRVladimirovFrameDiagnosticReceipt.agda`.
- Canonical TOE imports:
  `DASHI/EverythingTOESymmetryResolved369.agda`,
  `DASHI/Unifier.agda`, and `DASHI/Unified/Everything.agda`.

The Agda module proves only **constructor non-identity** and reuses the
repository's **syntactic fail-closed non-promotion** receipt. It does
not prove a physical conservation law, absence of a phenomenon, an
experimental result, or clinical ineffectiveness.

## 2026-10-28 solar 10 m2 dual-objective source-to-wall momentum screen

**Source**: solar irradiance reference ASTM G-173 from National
Renewable Energy Laboratory (NREL/NLR); NASA Langley 2026 teaching
derivation of photon momentum flux as optical power divided by c.
These support classical physics, not any anomalous Kozyrev effect.
Source references:
https://www.nlr.gov/grid/solar-resource/spectra-am1.5
https://ntrs.nasa.gov/api/citations/20260000767/downloads/012026UIUC%20presentation%20sm.pdf

**New canonical first-bounce producer**:
`scripts/kozyrev_solar_bisolver.py`, using the **existing** shared
`kozyrev_geometry_optimizer.py` collision method and target scorer.
Tests `scripts/tests/test_kozyrev_solar_bisolver.py` and CI step
have been source-written. It is a first-bounce **two-score** model,
not an escaped-ray ledger or an optical wave solver.

At 10 m² projected collector area, a stipulated 1000 W/m² plane
irradiance supplies 10000 W. For 90% optical delivery, 9000 W arrives
at the receiver/spiral input (before local material losses). The
incoming photon momentum-rate scale is
`10000 / 299792458 = 33.3564 microN`, or
`9000 / 299792458 = 30.0208 microN` after the lens.
The 100%-reflective total reversal ceiling for that 10 kW external
beam is `2*10000/c = 66.7128 microN` for the full illuminated
device, *given one directed incident beam and outgoing direction
directly opposite*. Do not add this ceiling once per bounce.

At 5% *local* absorption after 90% collector efficiency, 450 W is
deposited locally. The 10 kW external collector is a high-power solar
concentrator and must never be illuminated while an occupant is in
or near the focal region. Serious eye, skin, ignition and thermal
hazards exist. A 0.5 m lever gives a **single-surface illustrative**
maximum torque scale `2*9000/c*0.5 = 30.0208 microN*m`; this is
**not** a proven bound for internal forces on individual surfaces,
whose local torque contributions may exceed the net system value
and cancel each other. Actual torque depends on an external
axis and entire angular momentum flux.

**Scoring distinction**:
- Focusing proxy: share of external first-bounce rays whose
  reflected direction intersects a selected central target.
- Wall momentum/torque proxy: signed change in incident ray
  linear and angular momentum at that bounce.
- Global device net force: incident minus escaped photon
  momentum plus any momentum crossing thermal/mechanical
  boundaries. This is **not** the same as local wall force and
  the producer does not claim this global result.
- Thermal source model for a human needs a real radiation
  spectrum and angular intensity plus temperature/exchange.
  "Biological energy" is not a separate demonstrated force.

**Critical negative result**: A short external-beam first-bounce
screen can show a nonzero wall momentum change while having
zero target capture. Focusing and wall impulse are not guaranteed
to increase together, and a high ray-count/impact-count is not a
gain mechanism. A multi-bounce score is accepted only if all rays
terminate or an explicit residual momentum/energy bound is paid.

**Next highest-alpha cut**: integrate curved plate profiles from
the 9-panel construction drawing, select directional external
input versus internal thermal human emission as separate
source coordinates, trace one ray until escape/absorption and
account for all boundaries, then compute two objective values
from the same completed path. Run a robust Pareto search over
source angle and source position, including lens efficiency,
alignment, material loss and the complete source/collector
recoil. No Agda kernel, physical experiment, anomalous torsion
or human benefit claimed by the newly written Python.

## 2026-10-28: Published geometry vs golden-ratio optimisation

### What primary and secondary evidence actually specifies

**Primary patent RU2122446C1** (Kaznacheev and Trofimov; filed
1996-07-02, published 1998-11-27):
https://patents.google.com/patent/RU2122446C1/en
describes polished aluminium alloy panels, up to 280 cm high,
120 cm wide, a reported focal distance of 50 cm from the working
surface, and cylindrical or spiral assemblies of 4/6 and 8–10 panels.
The abstract says 0.5 mm thickness; description/claim says 1.5 mm.
There is **no primary claim of a unique Archimedean differential
equation, golden ratio, optimum growth factor or precisely 1.5 turns**.

**Distinct original patent RU2141357C1** (Kaznacheev and
Shatarnin; filed 1997-02-03, published 1999-11-20):
https://patents.google.com/patent/RU2141357C1/en
is a **horizontal cylindrical** laser-containing enclosure with
different 1.5–2 mm thickness and at least 110 cm width/200 cm length.
Do **not** transfer its dimensions or laser apparatus into the original
vertical Kaznacheev–Trofimov spiral.

**Retrospective/institute-attributed 2020 description:**
https://al-flogiston.ru/zerkala-kozyreva-1/
states that clockwise/counterclockwise spirals were open for **1.5
turns**. This is a traceable later description, **not a demonstrated
engineering optimum** and not the original patent's formula.

**Secondary nine-sheet construction drawing:**
https://texnoved.ru/kak-sdelat-zerkalo-kozyreva-certeez/
depicts approximately 3200 mm outer / 2002 mm inner spans, nine
labelled sheets, 2800 mm height. It is useful for candidate
manufacturing coordinates but no drawing-source chain proves it is
the inventors' historical as-built device or fits an experimentally
validated 50 cm focus.

**Alternative self-published geometrical critique:**
https://www.alsuprun.com/files/Kozyrev-Mirror-Biotron.pdf
(argues central focusing of a full spiral is poor and proposes
individually positioned concave sectors). Its quoted 13–15% and
8× efficiency numbers are **the author's unreplicated claims**, not
ground truth. It directly motivates a **fourth search family**:
independent finite curved sectors, with their own optical solver and
constraint model; the initial optimiser below does **not yet
implement that family**.

The user's attached AI-search transcript proposes an Archimedean
spiral, exactly 1.5 turns and global `f=R/2`. Those statements
are hypotheses or secondary approximations, not proven unique
patent geometry. `f=R/2` is a *paraxial spherical/circular mirror*
relation, not an exact common-focus theorem for a spiral with
changing curvature. Source claims about "time energy" and unusual
medical or remote-information effects remain nonpromoted.

### Golden growth cannot fit a compact 1.5-turn spiral at normal inner radius

Let `phi=(1+sqrt(5))/2`. A **true golden logarithmic** spiral
increases radius by exactly `phi` every quarter turn.
There are **six quarter-turns in 1.5 turns**. Thus for
`r_inner = 0.75 m`:

```text
r_outer_true_golden = r_inner * phi^6 = 13.4582039325 m
r_outer_available  = 1.55 m (illustrative compact envelope)
required ratio     = phi^6 ~= 17.94427191
available ratio    = 1.55 / 0.75 ~= 2.06666667
```

A true golden spiral with that inner clearance would require a
very large outer radius, inconsistent with the *illustrative*
1.55 m boundary. A 'correction exponent' to fit 1.55 m is

```text
beta = log(r_outer/r_inner)/(6*log(phi))
     = 0.2514266987284
r(theta)= r_inner * phi^(beta * theta/(pi/2))
```

This simplification is exactly the **ordinary endpoint-matched
logarithmic spiral**. Golden phi mathematically cancels; it does
not uniquely pick the optimum. A curve based on a *normalised*
exponential `(exp(k t)-1)/(exp(k)-1)` with
`k=6 log(phi)` can fit both endpoints, but after that affine
normalisation it **is not** a true golden logarithmic spiral.

### Implemented candidate-screening optimiser (synthetic, SOURCE-WRITTEN)

File: `scripts/kozyrev_geometry_optimizer.py`.

Same frozen model across candidates:
- 2D 9-segment spiral, 1.5 turns, illustrative
  0.75/1.55 m inner/outer radial endpoints;
- three isotropic point sources at `(0.25,0)`, `(0.21,0.1)`,
  `(0.21,-0.1)` metres;
- one first-hit **lossless specular** bounce per ray; all
  unreflected rays count zero towards return;
- central circular receiver of radius 0.10 m;
- objective: **maximise the worst-case one-bounce receiver-hit
  fraction across those three source positions**;
- a small 55-candidate grid over log-profile shape `k`
  and sinusoidal endpoint-fixed correction `c`, with monotonic
  radial increments and total sheet-polyline length
  <= 110% of Archimedean reference; **not a global optimiser**;
- also stores `p_wall=p_in-p_out`, `L_z=x p_y-y p_x`,
  energy and momentum residuals, adopting the sign convention
  in existing `ContinuousSO3Torque369BridgeExact` and
  `TorqueTrialectic369Exact` without duplicating their proofs.

**Executed local Python 3.13.5**, 720 rays/source results:

| Candidate | Worst receiver-hit fraction | Mean fraction | Polyline length |
| --- | ---: | ---: | ---: |
| Archimedean `k=0,c=0` | 0.113889 | 0.114815 | 10.374 m |
| True compact logarithmic `k=ln(1.55/0.75),c=0` | 0.113889 | 0.116667 | 9.948 m |
| Golden-*indexed*, endpoint-normalised `k=6ln(phi),c=0` | 0.130556 | 0.132407 | 8.875 m |
| Grid-selected `k=4,c=0` | 0.136111 | 0.137037 | 8.489 m |

The selected `k=4` hits the **maximum k in this grid**.
A wider probe through `k=12` increased the *same toy objective*
to 0.147222 worst capture, so **no converged or real-world optimum**
is claimed. This is direct evidence that unconstrained optimisers
can reward pathological profile growth or source-specific geometry.
The example **does not enforce individual 1.2 m curved panel widths,
minimum human access/clearance, local curvature/stress, sheet joins,
true metal losses, polarization, temperature, airflow, acoustic
frequencies, occlusion beyond one bounce, equilibrium fluctuation–
dissipation, diffraction, or 3D wave fields**.

**Executed local check: five standard-library tests PASS**
(`scripts/tests/test_kozyrev_geometry_optimizer.py`):
true golden radius mismatch, radial endpoints/monotonicity,
simple reflection energy and impulse ledger, parity-odd wall
angular impulse when geometry and ray are both mirrored, and
explicit nonpromotion/optimisation contract. Source files are
committed to the PR, but GitHub Actions/Agda kernel are separate
receipts and are not claimed on this local execution alone.

```sh
python3 -m unittest discover -s scripts/tests \
  -p 'test_kozyrev_geometry_optimizer.py' -v
python3 scripts/kozyrev_geometry_optimizer.py --samples 720
python3 scripts/kozyrev_geometry_optimizer.py --panels 8 --turns 1.0
python3 scripts/kozyrev_geometry_optimizer.py --panels 10 --turns 1.5
```

### Updated Pareto/max-cut

P2-A now has two source-written and locally executed *synthetic*
consumers: (1) exact Fraction momentum/parity laws for a selected
toy polygon, and (2) a numerical geometry candidate screen whose
objective and limitations are explicitly logged.

**P2-B next:** selected **published** drawing digitisation with
as-built provenance; manufacturing constraints; calibratable
frequency-specific **Maxwell/acoustic** problem on the *same* mesh;
curved sections and a genuine sector comparator; convergence; robust
multisource/multifrequency Pareto set; full torque/energy flux ledger.
Only after P2-B could one claim an *ordinary-physics* optimiser
selected a useful physical apparatus, and only after measured same
device testing could it be called validated.

**P2-C/P4:** a separately sourced nonstandard field/coupling with
an observable distinct from all ordinary acoustic/EM/thermal
candidates. Existing torque/right-hand-rule math is mathematically
sound, but right-handedness itself is **not** a new torsion force.

**Attribution/ownership:** original patents: Kaznacheev–Trofimov,
Kaznacheev–Shatarnin. Retrospective institute narration and
third-party drawing: their own derivative origins. Sector critique:
its external author owns its analysis. Existing DASHI torque
theorems: original PR
[#1164](https://github.com/chboishabba/dashi_agda/pull/1164)
(merged), source modules `TorqueTrialectic369Exact`,
`OrientedThreeAxisBracket369Exact`,
`ContinuousSO3Torque369BridgeExact`,
`RightHandRule369Exact`. New 2D synthetic optimisation code:
PR #1404 only. Ibrahim/Monster 3B ownership remains fully
unchanged; analogy/character/count coincidence cannot promote a
same-object representation. No ESD edits or clinical result.

## P2 max-cut: exact apparatus inventory, synthetic classical null and executed tests

**Execution date: 27 October 2026. Status: SYNTHETIC CALCULATION EXECUTED;
real physical surface/operator/data NOT identified; Agda KERNEL UNVERIFIED.**

### Primary patent dimensions, with ambiguity preserved

The original Russian-language claims and translated text are available at
https://patents.google.com/patent/RU2122446C1/en
(Kaznacheev / Trofimov, filed 1996-07-02; published 1998-11-27).

| Physical input | Patent statement | Correct representation |
| --- | --- | --- |
| Material | Polished aluminium alloy | Alloy, conductivity, roughness and optical/acoustic response still **unmeasured** |
| Panel height | Up to 280 cm | **2800 mm upper bound**, not measured installed height |
| Panel width | 120 cm | **1200 mm stated nominal width** |
| Panel thickness | English abstract **0.5 mm**; specification/claims **1.5 mm** | Two alternative `PatentThicknessReading` values: **5/15 tenths of mm**, exact distinctness |
| Intended focus | 50 cm from working surface | **500 mm reported focus**, no specified wavelength, beam, curvature profile or reliable lens equation |
| Open cylindrical build | Four or six elements | `openCylinderFourPanels`, `openCylinderSixPanels` |
| Left-/right-handed spiral | Eight to ten elements | Explicit 8/9/10 `leftSpiral` and `rightSpiral` constructors |
| Optional powered platform | 1–3 m/min reported motion speed | **1000–3000 mm/min linear speed**. **Not RPM**; angular speed needs radius and axis |
| Drawings/assembly | 4 figures; concave plates, seams/fasteners | Need source drawing reconciliation and actual point-cloud/profile. No patent-to-mesh theorem claimed |

The Agda candidate now gives a finite `PhaseChartChoice` identity-vs-C3
rotation separating two unfixed coordinate placements under identical
metadata. This is a **chart-choice witness**, not a proof that two
physically distinct, equally focusing patent surfaces exist. A
`SelectedPatentCandidateSurface` must explicitly supply a point
carrier, phase-to-surface chart, material and provenance. Nothing in
this PR inhabits it with a measured Kozyrev apparatus.

### Executed, minimal existing-law discriminator (P2-A)

**Producer:** `scripts/kozyrev_mirror_classical_null.py`
(the script is an independent DASHI source-written toy based on standard
specular reflection and angular-momentum balance; **not copied from
Broken Branch**).

**Checker:** `scripts/tests/test_kozyrev_mirror_classical_null.py`.

This chooses an intentionally *synthetic* four-direction, widening
polygon, a horizontally reflected handedness pair, and a
constant-radius **diamond-shaped** control. It fires independent equal
direction/momentum rays at each segment **midpoint**. It assumes
specular, lossless reflection, neglects shadowing, and does not
trace rays between surfaces.

For an incident vector `d` and nonzero segment tangent `t`:

```text
d_out = 2 (d . t)/(t . t) t - d
p_wall = d - d_out
L_wall = midpoint_x * p_wall_y - midpoint_y * p_wall_x
```

Exact `fractions.Fraction` arithmetic verifies `|d_out|²=|d|²`
and `d_out+p_wall=d`. Reflection through the y-axis changes
`L_wall` sign when **both** the geometry and incident ray are
reflected. The term `L_wall` is a dimensionless fixture angular
**impulse proxy**, not physical `N·m` steady torque.

**Locally executed, exact committed-source content verified:** five
Python standard-library tests **PASS** and JSON report emitted.
The committed Python files were compared with the locally executed
copies using lengths and independent 32-bit polynomial checksums
(5435 / 2790 bytes; checksum 795084313 / 642951860 respectively).
Their local SHA-256 hashes are
`dfdb3ec0a681e81afa86c8e59a695ef3e2988fc386bc2d08e3952265b22ad700`
and
`73c4591547fb05b913448ca0329f4cab6528c0f2e08ac3224ba515a98b40a2d9`.

```sh
python3 -m unittest discover -s scripts/tests \
  -p 'test_kozyrev_mirror_classical_null.py' -v
python3 scripts/kozyrev_mirror_classical_null.py --json
```

Exact synthetic fixture result:
- 12 independent segment-midpoint rays;
- squared-direction conservation **true** for spiral, reflected spiral
  and constant-radius diamond control;
- wall momentum conservation **true**;
- chirality reflection anti-symmetry **true**;
- summed spiral wall angular impulse
  `-14836561284940776619812/411027158523357468998425`;
- reflected case has the exact opposite value;
- diamond control fixture sum **zero**.

**IMPORTANT NEGATIVE INTERPRETATION:** The nonzero fixture sum follows
from a chosen asymmetric source/ray assignment to a chosen toy polygon.
It does not assert spontaneous torque, driven-rotor behavior,
thermal-equilibrium work, 3D acoustic radiation, a calibrated
reflector, time anomaly or a torsion field. No model of temperature
or material dissipation appears. The reflected configuration also
reflects its **incoming wave direction**, as required by parity.

### Direct 2026 literature comparison and attribution

- **Original patent/inventors** (source geometry and alleged clinical
  effects only): https://patents.google.com/patent/RU2122446C1/en
- **Broken Branch, HI-1** (2026-09-28; *external 2-D wave calculation*):
  https://www.brokenbranch.dev/labs/as-seen-on-tv/honest-spiral/
  It reports ordinary reflection-induced outgoing angular momentum,
  vanishing equilibrium net torque in its model, and correction of
  an unstable integrator's apparent effect.
- **Broken Branch, HI-2** (2026-10-06; external acoustic rotor):
  https://www.brokenbranch.dev/labs/as-seen-on-tv/the-sound-windmill/
  Separates powered internal-source recoil, beam-driven weathervane,
  dissipative drive, equilibrium thermal nulls; four of its 16
  preregistered gates failed. Do **not** silently upgrade it to a
  fully passed independent replication.
- **Broken Branch, HI-12** (2026-10-06; external density-of-states/probe
  study): https://www.brokenbranch.dev/labs/as-seen-on-tv/does-the-mirror-focus/
  Ordinary scattering can alter local field energy without net power
  to an equal-temperature probe. One convergence gate failed on a
  control geometry. A bright local fluctuation is not total energy.
- **2026 spiral engineering comparison**:
  *Spiral tuning of wire-metamaterial cavity for a plasma haloscope*,
  *Phys. Rev. Applied* **25**, 024073 (2026),
  DOI https://doi.org/10.1103/n1hb-9d3p.
  Published spiral-wire cavity tuning is prior art for **ordinary**
  electromagnetic geometry control; it is neither a Kozyrev apparatus
  nor evidence of new gravitational torsion.

These are separate external authors, devices, codes and evidentiary
levels. Nothing is imported as theorem authority merely because a
simulation uses the word `spiral`. See the repository's
same-object/Monster/Ibrahim attribution rules.

### Pareto / snowball / Ibrahim check against latest PR work

Source-read comparisons were made with
[#1272](https://github.com/chboishabba/dashi_agda/pull/1272)
(Fourier-pixel same-device phase/inverse-identifiability),
[#1246](https://github.com/chboishabba/dashi_agda/pull/1246)
(Ferrocell classical control and inverse ambiguity),
[#1252](https://github.com/chboishabba/dashi_agda/pull/1252)
(psychotronics strongest-admissible local-mechanism steelman),
[#1241](https://github.com/chboishabba/dashi_agda/pull/1241)
(KK physical source-to-observable BIDI), and
[#1402](https://github.com/chboishabba/dashi_agda/pull/1402)
(current TOE source-owner/no-continuum-promotion convergence).
These PRs are separate **open** branches. Their methods are useful,
but no unmerged files or proofs are silently adopted.

The **existing master** Ibrahim owner is
`DASHI.Wikimedia.IbrahimSnowballAtomicClaimIntentExperimentAdequacyBidiExact`.
Its canonical chain is:

```text
user's claimed effect -> atomic assertion -> formal constructor
 -> measurable operationalisation -> actual test design
 -> selected consumer -> executed result
```

We apply its original-owner rule rather than create a second
Ibrahim/Monster or experiment adequacy ontology. The
`scripts/kozyrev_mirror_classical_null.py` consumer is **exactly**
*independent-ray conservation/parity under specular reflection of a
synthetic polygon*. It is **not** the patent focus, a 3D wave
boundary problem, an electromagnetic shield, a rotating platform
measurement, a remote-information claim, medical efficacy, or
geometric-torsion observation. Success for this consumer cannot
be reported as success for any of those downstream questions.

The second canonical owner
`DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact` already
aggregates the original source/author-preserving Pareto, snowball
and identity firewalls. This Kozyrev cut does **not** amend, fork,
re-own or import Monster 3B representation claims. The Ibrahim
Monster 3B priority and exact-character evidence boundaries remain
untouched; neither `S3` wreath alignment nor a shared `C3`
phase is a proof of the *same object*.

The next source-acquisition snowball, in order of information gain,
is **patent original diagrams and plate curvature**, **measured
sample/material**, **single accepted physical field operator and
observable**, **numerical method and convergence**, **independently
locked experimental protocol**, **a second operator's data**.
This ordering prevents cycling through generic spiral foundations.

### What P2-A closes and what P2-B still needs

**P2-A completed as executed synthetic fixture:** specular parity,
energy/momentum bookkeeping, a handedness control, patent dimension
alternatives, strict distinction between source geometry and sampled
polygon. The exact script files and tests were committed and read back.

**P2-B still OPEN:** digitised actual apparatus geometry or an
explicitly accepted hypothetical profile family; incident spectrum;
metal constitutive response; validated wave or electromagnetic
boundary-value solver on that **same** surface; mesh/timestep
convergence; field/probe observables; matched sham conditions;
calibrated SI uncertainties. Do not conflate mathematical conservation
under independently chosen rays with global equilibrium radiation.

**P2-C still OPEN:** falsification against a distinct proposed
geometric-torsion model. An equation relating spin source to
connection torsion and a source-to-detector coupling is needed.
Mechanical helical orientation does not supply that equation.

**P3–P6 remain gated:** a synthetic numerical test is not a real
preregistered bench test, independent replication or human efficacy
trial.

## Repository-wide spiral/wreath archaeology (2026-10-27)

Search was performed against current-master GitHub code and named pull
requests. **Conclusion:** do not invent a second spiral calculus, tree action,
C3 character, winding-state model, or physical torque law.

| Already-owned object | Exact source owner / known statement | Reuse limit |
| --- | --- | --- |
| Rooted ternary recursive wreath | `DASHI.Reasoning.TernaryPantsRecursiveWreathActionExact`; `inverseActsLeft`, `sampleInverseRoundTrip`, `actInjective` | Correct **finite tree action**, not a physical rotational actuation or profinite apparatus |
| Elementary wreath-style refinement | `DASHI.Physics.Common.FiniteWreathRefinementExact`; local transform + index permutation, involution | Finite two-site prototype, not measured spiral material |
| Rotation/reflection spiral history | `DASHI.Biology.DialecticalSheetSpiralExact`; `projectedReturnAfterFour`, `reflectionFlipsSpiralSense` | Sheet/history model, not millimetre-accurate sheet geometry |
| Helical mapped-cylinder action | `DASHI.Topology.HelicalWeaveMappingTorusExact`; `threeStepsReturnToSamePhase`, `threeStepsAdvanceProductionRound` | Three-phase monodromy, **not** the apparatus pitch, radius or material |
| Phase/winding projection | `DASHI.Biology.Physical.Harmonic369HelixLiftExact`; `sameCircularProjectionDifferentHistory`, `helicalHistoriesRemainDistinct` | Exact discrete history separation, not time-machine evidence |
| Log-polar spiral | `DASHI.Cognition.AnalyticLogPolarSpiralCompilerExact`; exponential/logarithmic radial correspondence under explicit input | Mathematical spiral shape; its affine rearrangement and real apparatus identification are conditional |
| Spiral-shaped finite vector field | `DASHI.Biology.FiniteTorusVectorWaveGeometryExact`; discrete curl/divergence signatures | Finite wave geometry; not acoustic or EM material scattering |
| Physical torque orientation | `DASHI.Physics.Foundations.TorqueTrialectic369Exact`; swap-involution, bracket orientation and Hodge/cross product consumers | Mechanics comparator; not a source of Einstein–Cartan torsion |
| Stationary-phase mirror/grating | `DASHI.Interop.StationaryPhaseMirrorGratingToyReceipt`; `mirrorFermatToySetup` | Selected **toy optical setup**, no intrinsic material reflection data |
| Maxwell conducting boundary | `DASHI.Physics.QuantumVacuum.PerfectConductorMaxwellSpectrumBidiExact`; `tangentialElectricZero`, `ConductingModeEigenproblem` | **Parallel plates**, not a solved curved spiral enclosure |
| Magnetic-helicity Fourier laws | `DASHI.Physics.Plasma.MHDMagneticHelicityHelicalWeightExact` | Existing fluid/plasma operator; not physical connection torsion |
| Source/promotion rules | `DASHI.Promotion.CrossDomainClaimPromotionBoundary` and `DASHI.Empirical.GRQuantumPredictionProtocol` | Existing provenance, preregistration and non-promotion owners |
| Calibrated helical screw frame | `DASHI.Biology.Physical.BDNACalibratedHelicalGeometryExact`; `HelicalFrame`, `composeHelical`, pitch/twist reference regression | **Existing physical-unit calibration pattern**, DNA values are not valid aluminium apparatus parameters |
| Ordered rigid-motion / SE(3) | `DASHI.Biology.Physical.BDNAStepSE3CompositionExact` and `DASHI.Geometry.RigidMotionSemidirectProductExact`; rigid-step product, associativity | Reuse the rigid-motion **group law** without carrying DNA chemistry or biological parameters |
| Observer-conditioned optical measurement | `DASHI.Physics.Textile.TextileOpticalTransportBridgeExact`; illumination, material calibration, transport and observer readout | Exact reusable **observation architecture**; textile fibre optical coefficients are not an aluminium BRDF |
| Generic physical EM coupling | `DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact` and `DASHI.Promotion.MaxwellExteriorCalculusAdapter` | Existing Maxwell field/method sockets; curved-metal validation remains apparatus-specific |
| Acoustic/RF phase network | `DASHI.Physics.Foundations.ResonantFlightAcoustomechanicalCrossPollinationExact` | Existing coupling roles; structural acoustic/RF equivalence is explicitly blocked |

The updated Kozyrev Agda owner **imports rather than copies** these
source modules. It directly reuses five theorem/proof values: finite wreath
involution, recursive wreath inverse, helical monodromy, spiral handedness
reflection, and winding-projection coincidence. It also names the
pre-existing optical toy and conducting-boundary categories. These
imports establish **source-native theorem availability**, not an
apparatus realisation.

### PR lineage, merge discipline

- [#425](https://github.com/chboishabba/dashi_agda/pull/425)
  (*ternary harmonic/wreath refinement*) and
  [#558](https://github.com/chboishabba/dashi_agda/pull/558)
  (*recursive S3 pants-tree action*) were **closed unmerged**.
  Their corresponding source-owner modules were nevertheless found on
  **current master**. Reuse the actual master blob, not the closed PR's
  merge status as a theorem receipt.
- [#1020](https://github.com/chboishabba/dashi_agda/pull/1020),
  *Klüver log-polar projection*, **merged**.
- [#1164](https://github.com/chboishabba/dashi_agda/pull/1164),
  *torque/right-hand-rule 369*, **merged**.
- [#1140](https://github.com/chboishabba/dashi_agda/pull/1140),
  *Ogg-prime Fourier winding*, **open**. Do not conflate its arithmetic
  winding with physical spiral rotations, and do not import an unmerged
  theorem as current-master authority.
- [#1249](https://github.com/chboishabba/dashi_agda/pull/1249),
  *signed-zero/hyperfabric wave*, **open**. Existing source owners on master
  are independent and can be reused.

### The actual shortest unsolved cut

What repo inspection **did not establish** is not a general theory of
spirals, wreath actions, rigid-motion frames, observation systems,
electromagnetic fields or torsion:

1. **Patent geometry selection:** a measured, edition-qualified metal
   surface and material parameters, with the 0.5/1.5 mm discrepancy
   explicitly resolved or analysed as two alternatives.
2. **Same-object geometric realisation:** a coordinate/inclusion map from
   that measured surface into *one selected existing* spiral/helical
   carrier; handedness, winding, units, contact conditions and boundary
   orientation must commute. A map from a ternary path alone is not
   sufficient to characterise arbitrary smooth geometry.
3. **Same-geometry physical boundary-value operator:** instantiate existing
   Maxwell/acoustic/scattering machinery on the selected *curved metallic*
   enclosure, with measured conductivity, frequency, loss, apertures and
   material response. The repository's parallel-plate perfect-conductor
   interface and stationary-phase toy are not already that solution.
4. **Distinctive predicted observable:** tie a specified existing
   mechanics/electromagnetism model or an explicitly sourced modified
   torsion model to calibrated sensor values and a numerical error budget.
   Prove/test the relevant conservation balance; no free "time energy"
   detector or causal anomaly is implied by winding algebra.
5. **Physical evidence receipt:** preregister a same-key sham/active
   measurement, publish independent data and uncertainty provenance,
   verify reproducibility, then consider generalisation. No raw
   calibrated Kozyrev apparatus measurements or external replication
   were verified by this source audit.

P0/P1 mathematical construction is therefore substantially **reuse
complete**. Existing calibrated SE(3) and observer-transport *interfaces*
also make the P2 implementation an instantiation task, not a new
physics framework. P2 is now a **seven-obligation realisation cut** in
`canonicalExistingGeometryRealisationCut`, not a request to build new
mathematical spirals or wreaths. P3–P6 are distinct measurement,
mechanism and safety gates.

## Phase roadmap and deliverable gates (torsion reuse-first revision)

**Planning baseline: 2026-10-27.** This is a dependency-ordered technical
roadmap. A phase is **complete** only when its named artifacts, execution
receipts and exit tests exist. Writing a target or source document is not
the same as meeting its acceptance gate.

| Phase | Deliverable with owner | Pass / exit evidence | Present status |
| --- | --- | --- | --- |
| **P0 — Reuse and provenance** | This document and `KozyrevMirrorClaimTesting.agda`; merge-source ledger for Kozyrev names, patent, signed-zero, torque, Cartan/POAMS and external models | Exact repo/PR source roots and typed non-identity; patent thickness contradiction carried rather than guessed | **Source written**; Agda kernel and full source verification open |
| **P1 — Typed torsion bridge** | Native `TorsionMeaning`, `canonicalTorsionBridgeRequirements`, orientation and signed-zero reuse | Real imported theorem owners; disjoint meanings; no torsion-field promotion without physical source/coupling/observable | **Source written**; 10 obligations open; Agda kernel open |
| **P2 — Instrument/geometry null** | P2-A synthetic exact polygon reflection/parity/momentum fixture; P2-B existing spiral/SE(3)/Maxwell/optics selected on one measured apparatus and controls | Synthetic tests execute; for physical P2 closure require real surface/material and wave-solver convergence, calibrated prediction | **P2-A executed (5 tests PASS); P2-B and P2-C OPEN** |
| **P3 — Registered bench discrimination** | Timestamped SHA-256 protocol, blinded matched sham/active sequences and immutable raw telemetry; `kozyrev_mirror_claim_test.py` for eligible paired continuous endpoints | Recorded consent when applicable; independent timing and hash checks; sham parity; pre-fixed detectable effect and null rejection; no unplanned model switching | **Runner source written**, no independent registration or physical data |
| **P4 — Torsion-specific mechanism bridge** | Selected metric/connection model, spin-density source term, constitutive prediction, laboratory observable and nuisance budget | Distinct, dimensionful nonzero prediction; plain mechanical/EM/thermal/acoustic models excluded by preregistered discriminators; independent model reproduction | **OPEN — highest scientific cut** |
| **P5 — Prospective independent replication** | New apparatus/operator, held-out blinded dataset, error budget, adversarial review and statistical reporting including nulls | Replication on preregistered same observable and matched calibration; no leakage or uncontrolled field coupling | **OPEN** |
| **P6 — Human/clinical extension** | Ethics-authorised independent human protocol, sham validated masking, stopping rules and adverse-event data | Approval **before** enrolment, primary endpoint and power/uncertainty locked, independent replication; no treatment-authority promotion on a source report | **DEFERRED**; cannot depend on P1 toy semantics alone |

### Max-cut / Pareto stop–go ordering

1. Reuse the **merged** source owners first. The highest-value completed
   mathematical donor is [PR #1164](https://github.com/chboishabba/dashi_agda/pull/1164)
   (`TorqueTrialectic369Exact`, real finite SO(3) orientation, cross product
   and right-hand rule). Its exact swap-involution is consumed by the new
   bridge. **This is a kinematic orientation fact, not a mirror-field effect.**
2. Treat [PR #1249](https://github.com/chboishabba/dashi_agda/pull/1249)
   (signed-zero/path-wave hyperfabric) as **open sibling PR**. The reused
   `SignedZeroTorsionReceipt` is available in current master independently;
   do not assume new #1249 branch theorems are merged, or confuse
   signed-arrival metadata with spacetime torsion.
3. Reuse `LorentzianLeviCivitaConditional` as a **torsion-free supplied
   hypothesis**, and `YangMillsCizekEinsteinCartanClaimAuditExact` as an
   explicit Einstein–Cartan claim audit. The latter was cross-pollinated
   through [PR #466](https://github.com/chboishabba/dashi_agda/pull/466),
   which is **closed, unmerged**. The existing source-audit module remains
   usable on master; PR branch status is not proof authority.
4. Reuse **merged** [PR #714](https://github.com/chboishabba/dashi_agda/pull/714)
   `ScientificMechanismEvidenceBidiExact` and
   `POAMSScientificMechanismBoundaryExact` for the ordinary
   angular-momentum conservation comparator. The preliminary POAMS
   report is not the Kozyrev apparatus or an independent torsion detection.
5. Use [PR #1246](https://github.com/chboishabba/dashi_agda/pull/1246)
   (open Ferrocell geometry/null-model branch) as **analogy and reusable
   methodology only** unless a specific theorem/code file is independently
   selected, reviewed and intentionally transferred. The native
   `CrossDomainClaimPromotionBoundary` remains authoritative.
6. Only after P2 / P3 controls work, attempt P4. Stop if the hypothesised
   mechanism cannot supply a measurable unit, a calibrated detector,
   a source term, an uncertainty budget or a predicted deviation beyond
   ordinary physics. A *negative* test is reportable; do not repeatedly
   tune the prediction against the same data.
7. P5 independently reproduces a specific model-sensitive result.
   P6 is optional and safety-gated, not an automatic consequence of P5.

### Explicit physical torsion bridge, not mere vocabulary

For a connection `∇`, geometric torsion is
`T(X,Y) = ∇_X Y - ∇_Y X - [X,Y]`; in coordinate basis the last bracket
term vanishes. This is not the mechanical twist of an aluminium sheet,
not signed-zero path orientation, and not a two-torsion elliptic-curve
group law. Sources:
[Cartan torsion review](https://www.mdpi.com/2218-1997/5/10/206)
and [Einstein–Cartan matter review](https://doi.org/10.1103/PhysRevD.104.064036).

The **minimal** Einstein–Cartan model ties torsion algebraically to spin
density; it is not a free propagating, mirror-generated information field.
A stronger/different proposed model must explicitly specify new
dynamics and face all known constraints. Do not relabel
`TorqueTrialectic369Exact`, signed-zero orientation or a torsion-free
Levi-Civita hypothesis as a nonzero gravitational torsion producer.

The torsion-specific discriminator is a frozen tuple:

```text
(source spin density, constitutive equation, material geometry,
 coupling law, metric/connection, predicted detector observable,
 physical unit, calibration, null field response, nuisance model,
 effect threshold, preregistration, blind dataset, independent replay)
```

A finite symbolic proof of the algebra does not discharge the measured
coupling, instrument and source-field requirements. The existing Agda
`canonicalTorsionBridgeReadiness` records **false** for coupling,
calibration, replication and physical promotion.

### Phase exit commands and provenance

```sh
# Existing source-written Python synthetic fixtures; not physical evidence.
python3 -m unittest discover -s scripts/tests -p 'test_kozyrev_mirror_claim_test.py' -v

# Structural/syntax preflight is weaker than kernel validation.
dashi-agda-preflight --root . DASHI/Empirical/KozyrevMirrorClaimTesting.agda

# Execute with repository-pinned standard library and full Agda kernel:
agda -i . -i <repo-standard-library-path> DASHI/Empirical/KozyrevMirrorClaimTesting.agda
```

Record the exact Git SHA, python/Agda versions, runner log hash,
preregistration hash and independent verification identity before
claiming **executed** or **kernel checked**. Current PR #1404 has no
verified external experimental measurements.

### Attribution and model-identity invariants

- [PR #1164](https://github.com/chboishabba/dashi_agda/pull/1164)
  owns the pre-existing torque/Hodge/369 derivations. This change only
  instantiates its swap theorem on the Kozyrev candidate vocabulary.
- Cartan/Einstein–Cartan historical mathematics belongs to the cited
  original authors. Current external source papers are attributed as
  external theory/model, never as a proof the mirror is effective.
- Kaznacheev/Trofimov own their source/patent claims. Broken Branch
  owns its external toy simulation and numerical correction. No code/data
  is copied from either.
- The repository's exact same-object / Max Cut, Pareto, snowball, Ibrahim,
  Monster 3B and ESD attribution rules are unchanged. No shared word,
  character, cardinality, phase or torsion orientation proves the
  source and target are the same physical or mathematical object.

## Max-cut claim matrix

| ID | Distinct question | Ordinary explanation / control | Promotion status |
| --- | --- | --- | --- |
| KM-GEOM | What was patented and which geometry? | Patent drawings, dimensions, material, edition | Documented design only |
| KM-SCATTER | Does the enclosure alter known optical/acoustic fields? | Matched sham; geometry, reflectance, energy/momentum accounting; mesh/timestep convergence | 2-D model external only; physical test open |
| KM-SUBJECTIVE | Is reported experience distinguishable from expectancy? | Masked randomised sham, environment and order controls | Untested |
| KM-CLINICAL | Is a validated clinical endpoint improved beyond sham? | Human ethics review, medication controls, adverse-event surveillance, statistical multiplicity | Untested; no therapeutic promotion |
| KM-REMOTE | Can blinded targets be identified above locked chance? | Independent random target generator, cryptographic precommitment, leakage audit, decoys | Untested |
| KM-TIME | Is there a reproducible clock/causal deviation? | Traceable clocks, EM/temperature/pressure/vibration/drift controls | Untested |
| KM-TORSION | Can any explicit torsion model predict a measurable nonzero deviation? | Define detector response, units, calibrated null and prediction *first* | Bridge P4 open; measurement unselected |

**Do not conflate** an ordinary scattered wave, simulated acoustic torque,
subjective report, instrumental clock drift, information leakage, treatment
response, and a new causal or torsion field. Each needs its own effect
definition, acceptance range, independent negative control and provenance.

## Ordered Pareto / snowball experimental gates

1. **Source and geometry gate (cheap).** Archive original patent,
   identify the 0.5-versus-1.5 mm ambiguity, specify material/curvature,
   record expected ordinary scattering and absorption. Stop novel-mechanism
   promotion if the claimed signal lacks dimensions or detector physics.
2. **Instrument-only control (cheap, discriminating).** Pre-register a
   quantitative difference between active spiral, matched sham and ordinary
   reflector. Use calibrated optical/acoustic sensors. Fix the acquisition
   clock. Log ambient EM, noise, temperature, airflow and vibration. Repeat
   sham/active pairs using concealed random order.
3. **Calibration / numerical integrity.** Reproduce the known baseline,
   energy and momentum flux balance. For simulations, refine grid and
   timestep and include equilibrium/empty-box negative controls. A numerical
   artifact is not an instrument measurement.
4. **Freeze and replay.** Publish an immutable preregistration manifest
   before acquisition; independently timestamp its SHA-256. Freeze the
   data artifact hash before analysis. Use blinded analysis and a held-out
   study for claims that survive pilot tests. Report null and adverse results.
5. **Independent replication.** Use a second operator and apparatus, new
   randomisation, a predeclared target sample, stated uncertainty, and a
   separate audit of control outcomes. Do not promote one-run p values.
6. **Human claims only after safety gates.** For subjective/clinical tests,
   require a human research ethics decision, informed consent, risks and
   adverse-event protocol; no treatment changes outside clinical supervision.
   No rotating platform, intense sound/light, lasers or confined chamber
   experiments with people without independent engineering and ethics review.

## Minimal paired computational assay

The provided standard-library runner accepts a *specific* design: exact
active/sham pairs with a continuous, predefined primary outcome and
exchangeable signs under a sharp-null randomized assignment. It **does not**
fit all the claims above automatically. A binary remote-target hit-rate,
multi-arm dose study or clinical trial requires a separately preregistered
appropriate statistical analysis.

```sh
python3 scripts/kozyrev_mirror_claim_test.py --plan /path/to/registered.json

# After externally registering plan SHA-256 and acquiring frozen data:
python3 scripts/kozyrev_mirror_claim_test.py \
  --plan /path/to/registered.json \
  --data /path/to/paired.csv \
  --frozen-plan-sha256 "EXTERNALLY_REGISTERED_64_HEX" \
  --frozen-data-sha256 "FROZEN_OBSERVATION_64_HEX"

python3 -m unittest discover -s scripts/tests \
  -p 'test_kozyrev_mirror_claim_test.py'
```

The JSON manifest must contain: `study_id`, `claim_id`, `source_uri`,
`primary_outcome`, `outcome_unit`, `n_pairs` (2–18; exact enumeration),
`direction` (`positive`, `negative`, `two-sided`),
`minimum_effect`, `alpha` (at most 0.05), `preregistration_uri`,
`preregistration_timestamp_utc`, `randomization_method`,
`blinding_policy`, `sham_description`, `calibration_reference`,
`negative_controls` (at least two), `confound_controls` (at least
two), `analysis_plan`, `safety_approval_status`, and
`independent_replication_plan`. For human claims, the status must
be `approved`.

The CSV must have exactly `pair_id,condition,outcome`; each pair must
contain one `active` and one `sham` entry. **Exclude identities and
sensitive health information from this CSV.** The runner checks both supplied
hashes, data shape, a fixed paired sign-flip p value and minimum effect.
It **cannot verify** that a remote preregistration or calibration was genuine,
that blinding occurred, that signs were truly exchangeable, or that an
independent replication exists. Every output keeps
`physical_effect_established=false` and
`clinical_efficacy_established=false` even if the synthetic/real numbers
cross a statistical threshold.

**Audit invariants:** source report != independent evidence; patent !=
measured efficacy; toy model != 3-D experiment; statistics != new physics;
mathematical homonym != same object; coding/proof of a gate != its external
satisfaction; no copied source code or synthetic receipt claims ownership
of the upstream result.

## Explicit limitations

No local Agda kernel run is recorded here until executed separately.
Source review, file creation, synthetic Python regressions, and any eventual
kernel verification must appear as distinct ledger entries. A future
successful statistical analysis is only a candidate. It must not be
reported as established time travel, remote transmission, a new field, a
clinical therapy, or a resolved DASHI TOE proof.
