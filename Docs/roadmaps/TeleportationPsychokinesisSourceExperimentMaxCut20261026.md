# Teleportation / psychokinesis: source-first experimental max-cut (2026-10-26)

## Attribution and status

Source authors retain authorship. This repository owns only the typed bridge and experiment-design contracts. Archival possession, commissioned review, investigator assertion, statistical contrast, independent replication, theoretical proposal and kernel proof are distinct.

- Eric W. Davis (2004), *Teleportation Physics Study*, AFRL-PR-ED-TR-2003-0034 / ADA425545: historical commissioned report, including theoretical categories and claims in chapter 5. No Air Force endorsement or independent replication follows from publication.
- Bösch, Steinkamp and Boller (2006), *Examining Psychokinesis: The Interaction of Human Intention With Random Number Generators—A Meta-Analysis*, Psychological Bulletin, DOI 10.1037/0033-2909.132.4.497: review of 380 studies; small heterogeneous aggregate association and potential publication bias, not a validated paranormal mechanism.
- Radin and Nelson (1989): earlier RNG meta-analysis, overlapping literature; not an independent experimental replication merely by appearing in a later archival collection.
- SRI, DIA, Chinese and Soviet psychokinesis narratives: locate *original experiment* and separate translations, intelligence reports, archival copies and downstream quotations before assigning corroboration.

## Existing owners; no duplicates

- `DASHI.Core.ExperimentalCoordinateDesignExact`: coordinate roles, controls, nuisance, derived observables, collision separation.
- `DASHI.Core.CanonicalSpineRegistry`: owner registry for experimental coordinates and OSINT source-acquisition.
- PR #1207: claim-relative verification; PR #1242: psychotronics original-source/citation genealogy; PR #1252: synthetic causal/source-target discriminator; PR #1246: Ferrocell quantum-claim discriminator.
- Lean #61/#76/#85: *same-global-state*, finite partial traces, mode/parity false-herald boundaries; quantum state teleportation must consume actual compatible channel infrastructure rather than a separately postulated equality.

## Explicit falsification / discrimination matrix

| Model | Primary predicted observable | Controls | Biggest residual |
|---|---|---|---|
| Independent fair RNG | `P(X=1|do(I=i))=1/2` for every randomized intention arm | device swap, sham instructions, opaque seeds, drift calibration | proof of true randomization, independent trial units |
| Intention-dependent RNG | preregistered directional contrast not null under controlled interventions | identical double blind streams, laboratories, precommitted analysis | biological/physical coupling and replication |
| Conventional sensor coupling | outcome tracks temperature/EM/handling/vibration | instrumented full-spectrum sensor streams, Faraday and sham geometry as appropriate | unknown confounders |
| Macroscopic purported passage | tracked sealed-custody matter inventory and sensors | blind custody and substitution traps | original raw data, artifact identification |
| Quantum state teleportation | corrected channel identity on the input density state; no-signalling before classical message | classical message withheld, Bell resource replaced | compatible same-object channel proof |
| Extra-dimensional bypass | formal path avoids slice-contained barrier | topology and geometric boundary assumptions | physical accessibility and measured coupling |

### RNG estimand and identifiability

For `I∈{-1,+1}`, `X∈{0,1}`, a symmetric illustrative alternative is
`P(X=1|do(I=i))=1/2+i δ`, `0≤δ≤1/2`. Let
`δ̂=(p̂_plus-p̂_minus)/2`.
For *independent* equal-size Bernoulli arms with `n` samples per arm, at `δ=0`,
`Var(δ̂)=1/(8n)`. Trials nested within runs/devices/operators are not automatically independent; estimate uncertainty at assignment unit and account for hierarchical dependence, drift, interim looks and selection. Statistical deviation alone is not physical-mechanism identification.

At study level: `y_i ~ Normal(θ_i,s_i²)`, `θ_i ~ Normal(μ,τ²)`; observed publication probability `w(y_i,s_i)` implies `p(y_i|published) ∝ w(y_i,s_i)p(y_i)`. Archive copies and multiple reviews of the same run must share an original experimental-root ID in the evidence DAG; no multiplication of sample size by citation count.

## Prioritised independent source acquisitions

1. Original Chinese material cited by Davis: obtain translation, dates, instrumentation, custody chain, raw protocol, and classify *each* reported outcome separately.
2. PEAR MegaREG and 3-laboratory replication: resolve unit of randomization, directional reversal and original analysis registration; keep failed primary endpoint separate from exploratory post hoc tests.
3. SRI Puthoff/Targ and Soviet/Czech reports: originals, translations, intelligence layer and subsequent retellings must receive different edge types.
4. Original 1974 wire-deformation and 1985 Sasaki/Ochi experimental manuscripts and controls.

## Delivered and not delivered

Source-written Agda: `DASHI/Physics/TeleportationPsychokinesisEvidenceCutExact.agda`. Distinct source/evidence/mechanism constructors; witnessed nonpromotion inequalities; typed controlled measurement and nuisance contracts; a hypothetical higher-dimensional path; import of canonical experimental-coordinate collision separation.

Not claimed: Agda kernel compile (compiler unavailable in this session), independent experimental replication, physical PK proof, cloned original datasets, quantum channel correctness theorem, or same-object physical coupling. No stand-in proof of empirical adequacy.
