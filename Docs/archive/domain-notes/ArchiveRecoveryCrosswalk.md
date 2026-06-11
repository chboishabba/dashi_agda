# Archive Recovery Crosswalk

Recovery-first normalization of archive truth for the current physics-recovery
targets.

Archive status keys:

- `archive-claim`: the archive makes a concrete affirmative claim in its own
  language
- `archive-design`: the archive gives a usable design/dictionary/scaffold, but
  not a closed theorem claim
- `archive-heuristic`: the archive gives analogy, motivation, or direction only
- `archive-open`: the archive itself indicates the target is still missing,
  weaker than needed, or only partially framed

Minimum recovery-first sources used here:

- `Dashi and Physics Insights` — `ad17536d8eeb320106585654a0950424abafa93b`
- `DASHI Atom` — `25ec0d2e654f33ea6f524f816b4c465e86ef21cf`
- `Branch · Math Mysticism Breakdown` — `54e662a4243d10d575758d394f3c472210ed7cd2`

Additional archive sources used where they were visibly stronger:

- `Branch · Formalism Bridging GR and MDL` — `88923ac659cb8f659d4477d8193e4213e11be121`
- untitled realization-independence thread — `ee57b1be44a85035a1f7c08ec815181f6cba87d6`

| Target | Strongest archive status | Thread title | Canonical thread id | What the archive actually supports | Repo owner target if any | Promotion implication |
| --- | --- | --- | --- | --- | --- | --- |
| natural dynamics law | `archive-open` | `Dashi and Physics Insights` | `ad17536d8eeb320106585654a0950424abafa93b` | The archive supports a dynamics-law program shape around contraction, projection/Δ compatibility, cone preservation, and coarse/evolve witnesses, but it also explicitly says the continuum story is still weaker than the transport / projection-Δ story and does not recover a realized natural law by itself. | `Docs/NaturalDynamicsLaw.md`; `DASHI/Physics/Closure/AbstractGaugeMatterBundle.agda` (`NaturalDynamicsWitness`); `DASHI/Physics/Closure/CanonicalAbstractGaugeMatterInstance.agda` | Promote requirement/scaffold language and local witness language only. Do not promote to a recovered realization-independent dynamics theorem. |
| conserved physical quantity / vacuum / action language | `archive-design` | `Branch · Math Mysticism Breakdown` | `54e662a4243d10d575758d394f3c472210ed7cd2` | The archive gives a usable vocabulary: vacuum as an equivalence-class or lowest-energy-like slice, action/defect language, unitary-vs-contractive separation, and bounded quantum-compatibility requirements. It reads as a design/checklist and dictionary, not as a Noether-grade theorem package. | `Docs/GaugeMatterCapstone.md`; `Docs/AbstractGaugeMatterBundle.md`; `DASHI/Physics/ShiftDiscreteActionPrinciple.agda`; `DASHI/Physics/ShiftGaugeFieldTheoryAgreement.agda`; `DASHI/Physics/ShiftMinimalGaugeTheory.agda` | Safe to promote theorem-thin vacuum/action/conserved-observable wording. Unsafe to promote full conserved-charge, full vacuum physics, or full field-theoretic action recovery. |
| continuum limit | `archive-open` | `Dashi and Physics Insights` | `ad17536d8eeb320106585654a0950424abafa93b` | The archive supports “continuum limit” as a target interface and discusses toy continuum stories, but it also records that the continuum side remains weaker than the transport/projection-Δ side. This is a live open seam, not a closed scaling-limit theorem. | `Docs/GaugeMatterCapstone.md`; `DASHI/Physics/Closure/AbstractGaugeMatterBundle.agda` (`ContinuumWitness`); `DASHI/Physics/ShiftPhaseWaveContinuumStory.agda` | Keep promotion at finite-continuum-style witness/scaffold level. Do not promote to PDE, scaling-limit, or full continuum recovery claims. |
| realization independence | `archive-design` | `(no title)` | `ee57b1be44a85035a1f7c08ec815181f6cba87d6` | The archive explicitly frames realization independence as invariance under equivalent realizations and pushes it as a theorem target. It supports abstract hypotheses and transport language, but not a fully general recovered closure theorem. | `Docs/RealizationIndependence.md`; `DASHI/Physics/Closure/PhysicsClosureRealizationIndependenceTheorem.agda`; `DASHI/Physics/Closure/AbstractGaugeMatterBundle.agda` | Safe to promote “scoped theorem target with partial abstraction already landed.” Unsafe to promote full realization-independent closure or carrier-independent physical recovery. |
| gauge/matter recovery | `archive-design` | `DASHI Atom` | `25ec0d2e654f33ea6f524f816b4c465e86ef21cf` | The archive gives the strongest design dictionary here: admissible redundancy group, field bundle, jet order, invariant action/functionals, quotient observables, and explicit caution that GR or full recovery does not “just fall out automatically.” This is scaffold-grade support, not a finished theorem. | `Docs/AbstractGaugeMatterBundle.md`; `Docs/GaugeMatterCapstone.md`; `DASHI/Physics/Closure/AbstractGaugeMatterBundle.agda`; `DASHI/Physics/Closure/CanonicalAbstractGaugeMatterInstance.agda` | Promote abstract bundle, transported-observable, and partial recovery wording only. Do not promote to full gauge/matter recovery or full P0 closure. |
| GR/QFT regime recovery | `archive-design` | `Branch · Formalism Bridging GR and MDL` | `88923ac659cb8f659d4477d8193e4213e11be121` | The archive supports a direct dictionary from admissible symmetry, locality, and invariant/action language into GR-like and QFT-facing bridge language. It explicitly reads as a translation/design layer and “known-limits” style regime bridge, not as full recovery of gravity or QFT. | `DASHI/Physics/Closure/KnownLimitsGRBridgeTheorem.agda`; `DASHI/Physics/Closure/KnownLimitsQFTBridgeTheorem.agda`; `Docs/PhysicsRealityRoadmap.puml` | Keep the repo at “known-limits bridge” phrasing. Do not promote to full GR/QFT derivation or complete regime recovery. |
| atom / quantum correspondences | `archive-claim` | `DASHI Atom` | `25ec0d2e654f33ea6f524f816b4c465e86ef21cf` | The archive explicitly claims the atom/molecule dictionary, closed-shell behavior, gauge-information annihilation at saturated shells, quotient-observable language, and links to quantum-facing correspondence talk. The support is stronger than mere heuristic, but it is still correspondence-level, not a closure proof. | `DASHI/Physics/Closure/CanonicalAbstractGaugeMatterInstance.agda`; `Docs/PhysicsRealityRoadmap.puml`; `Docs/AbstractGaugeMatterBundle.md` | Safe to promote correspondence/dictionary claims and closed-shell quotient language. Unsafe to promote full atomic, quantum, or chemistry recovery from the canonical closure stack. |

## Normalized readout

- The archive is strongest on dictionaries, design scaffolds, and bounded bridge
  language.
- The archive is not yet strongest on full natural-law, realization-independent,
  continuum-limit, or full gauge/matter closure claims.
- The repo owner surfaces already reflect that split fairly well:
  `KnownLimits*` are bridges, `AbstractGaugeMatterBundle` is a scaffold, and the
  continuum / natural-dynamics / realization-independence docs remain program
  notes rather than final closure theorems.
