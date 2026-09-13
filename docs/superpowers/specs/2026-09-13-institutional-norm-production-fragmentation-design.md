# Institutional Norm Production, Situated Reasonableness, and Fragmentation — Design

Date: 2026-09-13
Branch: `agent/institutional-norm-production-fragmentation`
Parent head: `40d7a926a421fbe8f843ac8041a192215f3223b8` (PR #911)

## Purpose

Formalise the shared higher-order structure exposed by the Wednesbury/reasonableness, expert-evidence, trauma/neurodivergence, Mabo/colonial naturalisation, lobbying/proximity, operational enforcement, and distributed-bureaucracy discussion without collapsing those domains into one doctrine or introducing a parallel reasoning ontology.

The governing question is:

> How do institutions turn contingent, power-shaped representations of reality into authoritative decisions with definite consequences, and what information is lost at each projection?

The tranche must preserve the distinction between legal description, historical description, empirical claim, normative evaluation, and formal DASHI cross-pollination.

## Parent-first architecture

This branch is stacked directly on PR #911 and must follow existing owners rather than minting replacements.

Primary parents/donors:

- `DASHI.Core.QueryIndexedProjectionAdequacyExact` — adequacy is query-indexed; a collision with different fine answers blocks factorisation.
- `DASHI.Core.ObserverRefinementLatticeExact` — joined observers/refinement pay missing coordinates rather than reinterpret coarse outputs.
- `DASHI.Core.IntersectionalNonFactorability` — coarse single-axis views may erase situated coordinates and post-processing cannot recover erased information.
- `DASHI.Core.AttributedSourceCore` — author/title/publication/DOI-or-no-DOI/URL/source-kind/formalisation relationship; citation imports neither proof nor authority.
- PR #911 `SensibLawExpertEvidenceProductionIntegrityExact` — data -> selected/observed data -> inference -> opinion -> report use, with explicit consumed/excluded evidence, assumptions, limitations, abstention and non-promotion.
- PR #911 `MeasurementAdministrationComparabilityExact` — same named instrument does not imply comparable administration; comparability is consumer-indexed.
- PR #911 source-genealogy regression — report agreement does not imply independent evidentiary genealogy.
- merged PR #893 `SensibLawSpringfieldGasLobbyingOwnershipSnowballExact` — political donation, lobbying contact, employment lineage, partnership, control and ownership are distinct edge kinds; proximity does not promote to influence, quid pro quo or causation.
- merged source/snowball invariants: acquisition may occur out of dependency order; conclusion payment may not skip identity, source manifestation, same-object relation or unpaid dependency.

No new generic fibre/factorisation calculus is permitted in this tranche.

## Core data flow

The shared institutional production chain is represented as distinct coordinates:

```text
material/social power
  -> proximity/access
  -> agenda/framing
  -> norm/category production
  -> formal rule / institutional authority
  -> observation
  -> classification / inference
  -> reasonableness / credibility / relevance judgment
  -> institutional decision
  -> enforcement / non-enforcement / regularisation
  -> distributed local actions
  -> aggregate consequence
  -> baseline formation / naturalisation
  -> next-cycle institutional reasoning
```

These arrows are dependency relations, not automatic causal proofs. Each edge requires its own witness when instantiated historically.

## Generic world carrier

The generic owner will use a small finite carrier with conceptually distinct coordinates:

```text
InstitutionalWorld =
  PowerProximity
  × FramingState
  × NormativeReference
  × FormalRuleState
  × ObservationState
  × ClassificationState
  × DecisionState
  × EnforcementState
  × LocalActionState
  × AggregateOutcomeState
  × BaselineState
```

The implementation may use records rather than a literal product if that keeps the Agda surface clearer.

The master non-collapse boundary is:

```text
observed
!= empirically common
!= institutionally normal
!= legally reasonable
!= formally authorised
!= operationally tolerated/permitted
!= epistemically justified
!= morally justified
```

No field automatically promotes another.

## Owner 1 — Institutional norm production and naturalisation

Target:

`DASHI/Core/InstitutionalNormProductionExact.agda`

Responsibilities:

1. Represent proximity/access, framing, rule production, baseline reuse and naturalisation as separate coordinates.
2. Define `Naturalisation` as production-history erasure during baseline formation, not as a motive attribution.
3. Provide an exact finite two-world collision:
   - same later legal/institutional baseline;
   - different production histories / framing paths;
   - therefore historical/normative production history does not factor through the bare baseline.
4. Provide a constructive repair by joining baseline with retained provenance/history.
5. Keep `institutionParticipatesInNaturalisation != everyParticipantEndorsesUnderlyingIdeology` explicit.

Required firewalls:

```text
legal validity != political neutrality
legal validity != moral justification
formal equality != equal norm-production power
institutional familiarity != epistemic superiority
status signal != substantive adequacy
lawful lobbying != neutral policy outcome
consultation != balanced participation
proximity/access != influence conclusion
proximity/access != quid pro quo
```

`ProximityCapital` is analytical only and may include wealth, family/religious/professional/political ties, repeat-player status, reputation and brokerage. Presence of a coordinate never proves misconduct.

## Owner 2 — Fragmentation composition duality

Target:

`DASHI/Core/FragmentationCompositionExact.agda`

Purpose: capture the shared structural lesson without equating trauma with bureaucracy.

Two independent finite specimens:

### A. Trauma/reporting specimen

One coherent underlying event may project to fragmented/nonlinear observable reports. Therefore:

```text
EventTruth does not factor through NarrativeCoherence alone.
```

The formal object must not assert a clinical rule that trauma always causes fragmentation or that fragmentation proves trauma. It only proves insufficiency of the coarse narrative-coherence observer for the truth query in the finite witness.

### B. Distributed-action specimen

Many locally intelligible or role-conforming actions may compose to a globally harmful outcome. Therefore:

```text
forall localAction, LocalIntelligibility(localAction)
  does not entail GlobalDefensibility(composition).
```

Required firewalls:

```text
routine task != harmless task
local compliance != moral/legal justification
small causal contribution != zero causal contribution
distributed causation != no causation
not policy architect != no possible responsibility
same structural mechanism != same history/severity/legal status/culpability
```

Responsibility itself is not decided by this core owner.

## Owner 3 — Situated observer and reasonableness

Target:

`DASHI/Core/ObserverSituatedReasonablenessExact.agda`

Reasonableness must be indexed by at least:

```text
institution
legal/source context
reference perspective
relevant-factor set
threshold
consequence query
review standard
```

The generic core must distinguish:

```text
EmpiricalNormality
InstitutionalNormality
LegalReasonableness
```

with exact non-implications from observed frequency and institutional convention to legal/normative reasonableness.

A situated-observer fixture must show that the same underlying answer can receive different surface classifications under different observer expectation models. This is a formal observer-dependence witness, not a claim that every reasonableness standard is arbitrary.

Neurodivergence/trauma are thin fixtures, not definitions of the generic owner. Required no-promotion surfaces include:

```text
atypical affect ->/-> dishonesty
eye-contact difference ->/-> evasion
literal response ->/-> non-cooperation
dysregulation ->/-> dangerousness
narrative fragmentation ->/-> false event
social-norm conformity ->/-> reasonableness/credibility/risk
```

Use intersectional machinery to preserve multi-axis context rather than define an unparameterised universal `ReasonablePerson`.

## Owner 4 — SensibLaw legal reasonableness adapter

Target:

`DASHI/Law/SensibLawLegalReasonablenessExact.agda`

This is a domain adapter over Owner 3, not the generic theory.

It will distinguish:

```text
merits disagreement
factual error
relevant/irrelevant consideration error
legal unreasonableness
jurisdictional consequence
```

Wednesbury is retained as a historical doctrinal formulation/source fixture; Australian legal unreasonableness is not definitionally identical to the strongest rhetorical Wednesbury formula.

Primary/authoritative source candidates to acquire and source-bind:

- `Associated Provincial Picture Houses Ltd v Wednesbury Corporation [1948] 1 KB 223` — original formulation, if an authoritative/full-text source is located.
- `Minister for Immigration and Citizenship v Li [2013] HCA 18` — High Court primary authority.
- `Minister for Immigration and Border Protection v SZVFW [2018] HCA 30` — High Court primary authority.

Required firewalls:

```text
bad decision != legally unreasonable
harsh decision != legally unreasonable
court disagreement != legally unreasonable
legal unreasonableness != judicial merits substitution
relevant-consideration doctrine != definitionally the same as legal unreasonableness
Wednesbury rhetoric != automatic jurisdictional consequence
```

## Owner 5 — Operational legality and enforcement

Target:

`DASHI/Law/SensibLawOperationalLegalityExact.agda`

Coordinates:

```text
FormalRule
Detection
Investigation
Prosecution
Sanction
NonIntervention
Regularisation
MaterialSupport
OperationalConstraint
```

The exact generic witnesses must establish:

```text
formal prohibition != effective prevention
not prosecuted != lawful
tolerated != formally authorised
regularised != justified
formal domestic validity != external/international legality
```

No intent, conspiracy or tacit agreement may be inferred merely from non-enforcement. Tacit enablement is decomposed into source-payable event kinds: failure to prevent, failure to investigate, failure to prosecute, material support, regularisation, presence without intervention, and direct assistance.

Israel/West Bank may later instantiate this owner only through source-bound legal/institutional fixtures. It must not be hard-coded into the generic owner.

## Owner 6 — Institutional action and responsibility separation

Target:

`DASHI/Law/SensibLawInstitutionalResponsibilityExact.agda`

Typed status coordinates:

```text
Cause
Permission
Authority
Enforcement
Justification
Knowledge
Intent
CapacityToRefuse
Role
Responsibility
```

Core no-collapse statements:

```text
caused != authorised
authorised != justified
lawful != morally justified
small contribution != no contribution
distributed causation != causeless outcome
role obligation != complete responsibility answer
```

The owner must not assign culpability to any historical person or group. Historical cases are separate attributed fixtures.

## Expert-evidence cross-pollination

PR #911 remains the parent expert-production owner. This tranche adds only adapters showing how situated observers and fragmentation affect the adequacy query.

Planned thin adapter:

`DASHI/Law/SensibLawExpertEvidenceSituatedObserverExact.agda`

Questions it exposes without answering underlying case truth:

```text
What was observed?
What was excluded?
What observer assumptions shaped classification?
Was narrative/affective fragmentation treated as reliability loss?
Was institutional familiarity treated as credibility?
Are agreeing reports genealogically independent?
What uncertainty remains?
How severe and reversible is the downstream intervention?
```

No ABC allegation, practitioner complaint, court finding or regulator process may be promoted into a professional-breach finding unless the literal authoritative object pays it.

## Epistemic uncertainty × consequence severity × reversibility

Target analytical owner:

`DASHI/Law/SensibLawEpistemicConsequenceBoundaryExact.agda`

Coordinates remain distinct:

```text
EpistemicUncertainty
ConsequenceSeverity
Reversibility
```

The owner does not invent a legal doctrine requiring a particular numerical threshold. It exposes the analytical question whether highly uncertain inference is feeding a severe and difficult-to-reverse institutional outcome.

Required firewall:

```text
high consequence != proof underlying inference is false
high uncertainty != automatic prohibition on action
legal availability != epistemic adequacy for every consumer
```

## Historical / manifestation fixtures

Historical and contemporary cases are consumers of the generic owners, never definitions of them.

Planned fixtures, implemented only when source payment is sufficient:

1. **Wednesbury / Li / SZVFW** — legal-reasonableness lineage.
2. **Mabo [No 2]** — denaturalisation / observer inadequacy fixture: pre-existing Indigenous land relation is not created by citation or common-law recognition; later High Court descriptions explicitly distinguish recognition/giving effect from creation.
3. **Tasmanian colonial genocide** — historical source atlas only at first, with genocide claims bound to historians/archives and no invented same-object detail. University of Tasmania material and primary colonial archives are locators, not replacements for primary objects where claims require them.
4. **ABC family-report material** — news manifestation fixture over the generic expert-evidence spine; allegations remain allegations unless paid by court/regulator findings.
5. **Disability/neurodivergence access-to-justice** — Australian Human Rights Commission institutional source for communication/credibility barriers; autism-specific extensions require autism-specific sources rather than silently generalising all disability evidence.
6. **Israel/West Bank operational legality** — ICJ/international-law and enforcement/settler-violence fixtures kept separate; domestic legality, international legality, enforcement practice and individual attribution remain distinct.
7. **Lobbying/proximity/religious social brokerage** — generic social-network fixture must not encode the user's family anecdote as historical fact. Church/religious-network claims require independent historical scholarship before promotion.

## Attribution and snowball rules

Every source-bearing fixture must use `DASHI.Core.AttributedSourceCore` or an existing compatible source wrapper.

Hard rules:

1. Citation imports neither proof nor authority.
2. Source identity != claim truth.
3. News report != court/regulator finding.
4. Practitioner/academic interpretation != legal holding.
5. Primary legal source pays only what the judgment/instrument actually holds/states.
6. Secondary sources may locate primary objects but cannot silently pay primary facts.
7. Negative search/non-location != non-existence.
8. Acquisition may occur out of dependency order; conclusion payment may not skip unpaid dependencies.
9. Same-object identity must be explicit where multiple manifestations, cases, people, entities or events could be confused.
10. Structural cross-pollination never implies historical equivalence between domains.
11. Dynamic social/account metadata, when used, is timestamped source-snapshot metadata only and creates no authority.
12. Historical atrocity terminology must be attributed to the relevant scholarly/legal source unless independently established by the formal fixture's authority surface.

## Initial source snowball

Already located candidate sources for later fixtures:

- High Court of Australia, `Minister for Immigration and Citizenship v Li [2013] HCA 18` — primary Australian legal-unreasonableness authority.
- Australian Human Rights Commission, `Equal Before the law: Towards Disability Justice Strategies` — institutional evidence on disability, communication, credibility and justice-system barriers.
- ABC Background Briefing, 19 June 2023, expert-witness/report-writer investigation — news manifestation only.
- ABC Background Briefing, 30 June 2023, family-report writer regulation/Erin account — news manifestation only.
- University of Tasmania explainer on evidence for Tasmanian genocide — scholarly secondary locator; primary archives and named scholarship remain the next payment route for historical details.
- High Court/Kirby materials describing the factual and legal shift associated with `Mabo [No 2]` — secondary/judicial commentary locators; the actual `Mabo [No 2]` judgment remains the primary fixture target.

No source above creates a theorem, breach finding, historical equivalence, or authority outside its source class.

## Testing / TDD

Implementation is test-first.

For each owner:

1. add focused regression/static contract first;
2. verify exact branch lookup/file absence before production implementation when the owner is genuinely new;
3. implement the minimum finite witness and firewalls required by the regression;
4. wire only through the narrowest aggregate needed for discoverability;
5. extend a focused Agda workflow rather than relying on repo-wide manual-only CI;
6. reject trust escapes (`postulate`, unsolved metas, compiler escapes) in the new tranche;
7. do not claim Agda GREEN without an exact-head workflow/local kernel receipt.

Parent PR #911 certification debt remains distinct from this child branch. The child must not claim inherited parent certification merely because it is based on the parent head.

## Branch / PR structure

This work remains stacked on PR #911 until the expert-production parent merges. The child PR should target `agent/sensiblaw-expert-production-integrity` rather than `master` while parent-specific imports are required.

Do not silently copy PR #911 production files into the child. Follow-parent means dependency, not duplication.

If PR #902's coarse/fine calculus merges before implementation reaches a point where it materially simplifies a witness, re-evaluate and import it explicitly. Until then, do not stack a second open-parent dependency merely for elegance.

## Success criteria

The tranche is successful when it provides reusable executable witnesses for:

- production-history erasure / naturalisation;
- retained-provenance repair;
- trauma-side and bureaucracy-side fragmentation non-collapse;
- situated reasonableness observer dependence without arbitrariness-by-definition;
- Wednesbury/Australian legal-reasonableness separation;
- formal rule versus operational enforcement separation;
- cause/permission/authority/justification/responsibility separation;
- expert-evidence situated-observer integration;
- uncertainty/severity/reversibility analytical separation;
- strict source attribution and snowball debt accounting for every historical manifestation.

It must not claim:

- that all law is arbitrary;
- that all reasonableness standards are subjective or ideological;
- that neurodivergence or trauma determines truthfulness;
- that lobbying/proximity proves influence or corruption;
- that local role compliance erases or proves responsibility;
- that structurally similar mechanisms make historical cases equivalent;
- that any cited news report proves an allegation;
- that source citation imports proof or authority.
