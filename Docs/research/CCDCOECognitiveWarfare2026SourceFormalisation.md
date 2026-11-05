# CCDCOE cognitive-warfare primary-source / DASHI formalisation

Status (2026-11-04): **source-written, not kernel-checked in this pass**.
This is an attributed *finite structural model*, not a validation of a
military, clinical, political, or empirical diagnosis.

## Sources and interpretation boundaries

**Primary research:** Fedir Korobeynikov, Andrii Davydiuk, Volodymyr Mokhor,
*Ontological Foundations of Cognitive Warfare* (NATO CCDCOE, Tallinn, 2026),
https://ccdcoe.org/uploads/2026/04/ONTOLOGICAL_FOUNDATIONS_OF_COGNITIVE_WARFARE.pdf .
The CCDCOE published its announcement on **10 April 2026**, not on the date
shown in the viral video's overlay. The publication warns that it does **not
necessarily represent NATO policy**.

**User-supplied commentary:** an SRT transcript of a short video whose
speaker identifies himself as Adam Rosner. It presents an
“arbiter/narrative/projection-surface/in-group–out-group” interpretation,
Plato's cave, literacy statistics, and Russian reflexive-control history.
These are the speaker's assertions. Do **not** attribute that four-mechanism
model to the CCDCOE paper.

**Related, independently published 2026 source:** the same authors'
*A Structural Model of the Human Agent in Cognitive Warfare*:
https://ccdcoe.org/library/publications/a-structural-model-of-the-human-agent-in-cognitive-warfare/ .
It moves from group/system layers to personal invariants, transition
connections, altered holonomy, and invariant compatibility. Those are
additional research proposals, not proved by this finite graph.

## Prior art reused (never re-owned)

- `CognitiveWarfareAdmissibleDetectionExact`: same present appearance, differing
  underlying origins; future admissible provenance inspection may separate them.
- `CognitiveWarfarePlatoTraumaDetectorWeldExact`: content / reachable cone /
  provenance independence, query-specific observation, no hostile-intent
  inference from a cone change.
- `PlatoCaveTraumaMemoryDecisionBridgeExact`: projected shadow is not
  automatically false; refinement does not confer ultimate-reality authority.
- `IntersectionalNonFactorability`: generic witness blocking global
  factorizations through lossy observers.
- `AttributedSourceCore`: citation does not import proof or endorsement.
- `TrialecticMemoryLearningHyperfabricExact` and `EpistemicAttractorCore`:
  experience / truth / evidence / interpretation and self-sealing belief
  updates remain separately typed.
- Historical PRs: #317 (cognition), #531 (epistemic governance), #584
  (observer refinement), #1458 (higher-order hyperfabric).
- Direct predecessor: commit 82f5bcba73fc32ae08d4a80909075b0f5ae841d1.

## New finite theorem surface

`DASHI/Cognition/CCDCOECognitiveMultiplexInvariantExact.agda`

1. Exact five-layer constructors: epistemic, axiological, identificatory,
   social, teleological. Every layer has the **same two actor nodes**.
2. Local within-layer operation is preserved when a chosen cross-layer
   bridge is removed (`localOperationUnchangedByCut`).
3. A four-bridge dependency chain is a selected spanning path. For all
   three other Boolean edge values, losing the third bridge cuts this path
   (`singleCutBlocksPath`). This is a **chosen path** theorem, not a claim
   that any single edge disconnects an arbitrary multiplex.
4. The intact and cut configurations have the same visible
   `OutwardReport` but different path states; generic
   `NonFactorabilityWitness` rules out perfect inference of this
   structural property from outward functionality alone.
5. A four-episode source case shows **both** directions fail:
   architecture does not determine organic-versus-influence provenance,
   and provenance does not determine architectural integrity.
6. Abstract bridge restoration makes the selected path pass again.
   This is not a validated, safe, consentful or feasible real-world repair.

No empirical coefficients, causal weights, observed agencies, adversary
identities, or field measurements are invented. These remain open gates.

## Formal model and boundaries

For the selected actor `a`, write the four interlayer links as
`e(a), v(a), i(a), s(a) ∈ {0,1}`, and define

```text
P(a) = e(a) ∧ v(a) ∧ i(a) ∧ s(a)
```

Then `P(a) = 0` whenever the selected `i(a)=0`, irrespective of
the other three link values. In the witness the within-layer relations
are all `1` while `P(a)` changes from `1` to `0`.
This is a proof of **structural possibility**, not that actual communities
always follow a four-bridge chain.

Observation/provenance non-equivalences:

```text
same outward report ≠ same cross-layer integrity
same architecture ≠ same provenance
same provenance ≠ same architecture
coherence ≠ truth
source citation ≠ proof of the source theory
```

The paper explicitly says that quantitative connectivity indicators,
connector-node identification, and metrics of cognitive coherence require
further research. Its “constitutive invisibility” claim concerns possible
unrecognised influence, not a theorem that detection is impossible for
every observer and every evidence-acquisition procedure.

## Attached video: audit

- **Genuine source, false novelty framing:** CCDCOE released the work in
  April 2026; an overlay dated 22 September is not its publication date.
- **“NATO has announced global war”**: not supported. A CCDCOE research
  publication is neither a war declaration nor necessarily NATO doctrine.
- **Four projection-surface mechanisms**: commentary's framework, not a
  formal four-step theorem in the actual paper. The Plato cave comparison
  is an analogy, not evidence of empirical completeness.
- **“Impossible to see”**: overstatement. The paper's relevant claim is
  that a target *may never become aware* and attribution can be difficult.
- **OECD literacy**: 2023 PIAAC OECD average ~11% at Level 4 and ~1% at
  Level 5, not a robust categorical 13%; “sixth-grade reading” is not a
  valid direct translation of adult PIAAC proficiency levels.
- **Surkov and Russia**: historical influence/reflexive-control material
  requires independently sourced causal analysis. It does not establish
  that Surkov invented the techniques or “engineered” the whole Ukraine war.
- **Protection**: verify primary sources, provenance, and observer-relative
  evidence; preserve epistemic suspension and revisability. Neither
  “absolute truth” rhetoric nor mere institutional trust is a mathematical
  or empirical guarantee of immunity.

## Exact open gates

G1. Kernel-run the new Agda file and its imports; add a focussed regression.
G2. Lift the toy actor set and four-link selected path to a general
    finite multiplex with vertex- and layer-indexed edges, arbitrary
    paths, and explicit connectivity proofs.
G3. Define source- and time-indexed measured connectivity indicators,
    sampling/provenance uncertainty and falsifiable coherence metrics.
G4. Identify causal perturbations using longitudinal/experimental designs;
    distinguish externally originated influence, intentional hostile
    operations, incidental divergence and legitimate criticism/dissent.
G5. Lift to real observer/action resources, admissible future queries,
    memory-preserving repair, individual consent and pluralism.
G6. Keep the later CCDCOE personal-holonomy model as a *separate*
    candidate bridge pending exact transport and measurement.

Source assertions, mathematical witnesses, candidate explanations, and
real-world attributions must remain distinct authority classes.

## 2026-11-06 exact max-cut (PR #1467)

**Implementation status: SOURCE-WRITTEN, NO AGDA KERNEL RECEIPT.**
The source audit has been rechecked against the attached 6m24s SRT,
the actual original CCDCOE April-2026 PDF (sections 5.1–5.4), and
the authors' later individual-agent paper. Explicit no-promotion
boundaries are preserved.

### Reused prior art, not reimplemented

- `DASHI.Core.IntersectionalNonFactorability`: every observer inadequacy
  witness uses the **existing** `NonFactorabilityWitness` and
  `FactorsThrough` definitions.
- `DASHI.Core.QueryIndexedProjectionAdequacyExact`: one outward
  observation is adequate for outward function and demonstrably
  inadequate for inter-layer integrity and provenance.
- `DASHI.Core.AttributedSourceCore`: research-paper attribution.
- `DASHI.Cognition.PNF.EventAlgebra`: actual `EventPNF`,
  `CandidatePNF`, revision and temporal coordinates.
- `DASHI.Cognition.CognitiveWarfareAdmissibleDetectionExact` and
  `CognitiveWarfarePlatoTraumaDetectorWeldExact`: existing noncausal
  provenance, action cone and coherence/truth firewalls.
- `DASHI.Cognition.PlatoCaveTraumaMemoryDecisionBridgeExact`:
  source-native refinements are conceptually separate from Plato
  metaphors or claims to possess 'ultimate truth'.

### Source-written mathematical deliverables

| Gate | New owner/proof | Exact result / limit |
| --- | --- | --- |
| M1 generic multiplex | `CCDCOEMultiplexGraphCutCoreExact` | Common actor carrier, two types of typed edges, arbitrary proof-bearing walks and concatenation, retained-edge partition and disconnection theorem |
| M2 five-layer cut | `CCDCOEFiveLayerCertifiedCutExact` | All original intra-layer links survive; exhaustive interlayer constructors certify a genuine cut separating epistemic from teleological layers, for **both actors** |
| M3 alternate-path safety | `scripts/check_ccdcoe_cognitive_multiplex.py` | Exhaustive 16 connector masks × four ordered actor pairs; bypass edge must *invalidate* cut certificate |
| M4 query sufficiency | `CCDCOEQueryPNFEvidenceBridgeExact` | Source-native `QuerySemantics` shows outward observer sufficient for function, insufficient for connectivity/provenance; recharting cannot restore lost information |
| M5 PNF interface | `EvidenceOf About episode question` | Actual PNF event and candidate, plus **application-provided typed `About` proof**; existing event/observation time and revision-retention fields reused, no synthetic observation promoted |
| M6 personal context | `CCDCOEPersonalHolonomyBoundaryExact` | Different loop transport under unchanged public role; finite non-factorability and no hostile-origin inference |
| M7 old example | `CCDCOECognitiveMultiplexInvariantExact` + regression | Boolean selected-path cut, independent origin/architecture, abstract repair and bounds |

### Why this is stronger than the previous four-edge example

A broken **specified path** does not imply graph disconnection when
alternative routes exist. The generic theorem first supplies a
partition map `side : V → Bool`, then requires every surviving
edge to be certified same-side. Only then can *any* walk from a
true-side node to a false-side node be ruled out. The five-layer
case discharges this stronger edge-by-edge obligation by exhaustive
constructor pattern matching. The Python counterexample adds a
cross-partition bypass edge: the certificate fails and reachability
returns.

```text
path missing != graph disconnected
every surviving edge side-preserving + endpoints opposite sides
    => no surviving path can join endpoints
```

### Exact still-open gates (do NOT claim completion)

| Gate | Remaining acceptance evidence | Why the graph proofs do not pay it |
| --- | --- | --- |
| KERNEL | `agda -i .` compile each new module, regression, and cognition umbrella, inspect CI and use explicit `--safe` where dependency graph permits | No Agda executable or CI kernel receipt accessible in this pass |
| MEASURE | independently measured, appropriately sampled, time-stamped layer membership, edge existence, confidence/uncertainty, and criterion-valid group-level indicators | Synthetic complete intra-layer relations do not represent measured networks |
| CAUSAL | longitudinal/experimental, confounder-sensitive discrimination between voluntary change, institutional failure, external influence, hostile intention, and independently verified events | Four-episode counterexample proves an identification **impossibility** from structural state alone |
| PNF-PRODUCER | source-licensed original `EventPNF` and `CandidatePNF` for a **specific** publicly inspectable event with typed `About` witness and revisable lineage | A contract requiring evidence is not an actual ingested evidence record |
| HUMAN | establish that observed decisions across real contexts are faithfully represented by a selected personal state/connection, and that holonomy transport is empirically meaningful | Two-state finite loop is mathematical analogy, not psychological measurement |
| INTERVENTION | consent, privacy, pluralism, reversible action, effectiveness, adverse effects and independent oversight in a declared setting | `abstractRepair` is only a mathematical map that resets an edge |
| EXTERNAL | distinguish CCDCOE original systemic paper, later human-agent/companion work, presenter commentary, and DASHI theorems in every claim | Citation, interpretation, and proof are different authority types |

### Falsifiability and ethical requirements for any real-world extension

A legitimate observational study must define its sampling frame and
decision-process outcomes first, collect only proportionate,
consent-governed **aggregate procedural** observations, pre-register
the connectivity indicator and negative controls, test stability
under measurement error, and explicitly measure alternative
explanations. Do not operationalise the model as surveillance,
psychological classification of individuals, or a label for dissent.
No manipulation of participant beliefs is required or authorised
by the formal programme.

### Regression commands

```sh
python3 scripts/check_ccdcoe_cognitive_multiplex.py
agda -i . DASHI/Cognition/CCDCOEMultiplexGraphCutCoreExact.agda
agda -i . DASHI/Cognition/CCDCOEFiveLayerCertifiedCutExact.agda
agda -i . DASHI/Cognition/CCDCOEQueryPNFEvidenceBridgeExact.agda
agda -i . DASHI/Cognition/CCDCOEPersonalHolonomyBoundaryExact.agda
agda -i . DASHI/Cognition/CCDCOECognitiveMultiplexInvariantRegression.agda
agda -i . DASHI/Cognition/Everything.agda
```

Until an actual successful Agda run is recorded, the formal status
is **source-written, not kernel-verified**. A successful finite
Python test is not an Agda proof receipt, and neither establishes
empirical cognitive warfare.
