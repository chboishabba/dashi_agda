# Child–Caregiver–Authority Trauma Hyperformalism

This lane is role-general. No theorem premise names a particular family member. Concrete histories instantiate abstract child/dependent, parent/caregiver, supporter, authority, institution, archive, evidence, and adjudication carriers.

It is stacked on the role-general relational-state lane in `DASHI.Reasoning.RelationalEverything` and extends that base rather than duplicating it.

## Exact response carrier

A response is indexed by the exact guarded node, decision episode, proposition version, scope, and time:

\[
\operatorname{ActualResponse}(x,n,d,t).
\]

A positive response to `might consider` preserves a live unresolved branch. It is not a promise of deliberation, selection, execution, or recurring obligation.

Transport to another proposition requires independent witnesses for descendant, context, modality, scope, temporal, and version changes. Consideration therefore does not silently become commitment, and a bounded response does not become an indefinite role.

## Dependent authority and coercion

The core roles are dependent child/subject, caregiver, delegated supporter, educator, religious authority, institutional authority, and neutral custodian.

The coercive primitive is not parenting, religion, education, or care. It requires an authority demand, constrained refusal, meaningful penalty, and dependence. Observed compliance is non-injective: willingness, freezing, submission, and fear can share the same behavioural surface.

Teaching is distinct from indoctrination. The latter requires repeated transmission together with restricted counter-evidence, punished doubt, authority closure, and constrained exit.

## Diachronic delegated authority

Prior authorisation, present will, historical evidence, and continuing authority are distinct.

\[
\operatorname{Revocation}
\not\Rightarrow
\operatorname{HistoricalErasure},
\]

while

\[
\operatorname{HistoricalEvidence}
\not\Rightarrow
\operatorname{RestoredAuthority}.
\]

After revocation, process effects are typed as already completed, unavoidable continuation, required closure, or new discretionary action. New discretionary action ordinarily requires fresh authority.

A dual-use archive may be both memory/support infrastructure and revocable private data. Neutral custody separates preservation or targeted retrieval from monitoring, alteration, or control.

## Role-general chronology and projection

`DASHI.Reasoning.RelationalChronologyProjectionBoundary` abstracts the chronology into reusable operators.

### Triangular positioning

A dependent participant can be positioned as child/dependent, witness, messenger, possible ally, or symbolic extension within conflict between adults. These are relational assignments rather than personal identity.

### Identity-prior contamination

The same current act is evaluated under two prior loads. The finite countermodel proves:

\[
\operatorname{appraise}(0,\mathsf{requestParticulars})
\neq
\operatorname{appraise}(1,\mathsf{requestParticulars}).
\]

Only the inherited prior changes. This proves that prior loading can change classification while present conduct remains fixed; it does not assert contamination in a concrete case without evidence.

### Causal-order loss

The typed chronology

\[
\text{act}\to\text{impact}\to\text{objection}\to\text{response}
\]

is distinct from the lossy projection

\[
\text{objection}\to\text{secondary distress}\to\text{blame}.
\]

A counter-complaint transition can increase the number of open boundaries while leaving the original issue unresolved.

### Pseudo-consultation

The canonical witness records requested input that does not affect the decision, followed by a unilateral result narrated as joint. Hearing, uptake, decision sensitivity, and agreement remain separate types.

### Evidence-root analysis

Evidence layers include original recording, contemporaneous conversation, account record, professional record, sworn statement, later reconstruction, and generated interpretation.

Two documents with one provenance root cannot construct an `IndependentEvidencePair`. A genuinely different root can. Distinct provenance proves source independence, not truth or legal weight.

### Node-specific acknowledgement

The five-node response distinguishes:

1. event occurrence;
2. reported impact;
3. inappropriateness;
4. attributed intention;
5. pattern-level or legal characterisation.

The model constructs two distinct responses—`affirm, affirm, affirm, reject, reject` and wholesale affirmation—that both project to coarse `admission`. This proves that the coarse projection loses semantically important distinctions.

### Procedural projection

A fixed recorded account may avoid live compression but be unavailable for reciprocal testing. A live account may be testable while exposed to time limits, compression, and demeanour interpretation.

Two distinct lived histories map to one adjudicated record. The adjudication map is therefore non-injective. No inverse from an order or finding to total personal identity is supplied.

## Trauma, memory, and directed branch control

Memory retains live, traversed, blocked, expired, reinstantiated, and learned branch topology rather than only terminal success or failure.

Liveness is stratified across logical, institutional, economic, agent, capacity, and temporal dimensions. A globally imaginable option need not lie inside a particular agent's reachable cone.

A larger branch set can be serviceable while locally non-viable because flow is diffused below attention thresholds. Short-term relief can coexist with long-term adverse drift. Positive standalone value can become negative portfolio value after interference.

The exact three-branch optimiser enumerates all eight subsets of aligned, exploratory, and trap-directed branches. `aligned + explore` has value five and dominates every alternative. The serviceable maximum-count portfolio has value one and only two effective basins.

Thus:

\[
\operatorname{MaximumCount}
\land
\operatorname{Serviceable}
\not\Rightarrow
\operatorname{Optimal}.
\]

## Childhood religious-coercion research bridge

The research specialisation separates religious participation from coercive delivery. Exposure dimensions include fear, compulsion, punishment, isolation, institutional betrayal, direct abuse, epistemic closure, and disclosure suppression.

The design is longitudinal and mixed-methods but begins with retrospective childhood exposure reports. Mixed-effects modelling is primary. Association is not promoted to causation; participant narrative is not promoted to diagnosis; strong belief is not promoted to coercion without the relational sanction structure.

## Amalek boundary

`Amalek` is restricted to recursive terminalisation, enemy-production risk, and remembered-harm-to-domination protocols. It is not a predicate of a child, dissenter, survivor, religion, ethnicity, nationality, or human group.

Safe disclosure, particularised evidence, independent review, blocked retaliation, dependent welfare, and institutional corrigibility interrupt the closed authority loop.

## Module map

Role-general base:

- `DASHI/Reasoning/RelationalStateCore.agda`
- `DASHI/Reasoning/RelationalSharedStateUpdate.agda`
- `DASHI/Reasoning/ConditionalResponseTree.agda`
- `DASHI/Reasoning/DefensiveReversalRepair.agda`
- `DASHI/Reasoning/RelationalProcessMemoryHyperfabric.agda`
- `DASHI/Reasoning/AttractorAlignedBranchSelection.agda`
- `DASHI/Reasoning/RelationalEverything.agda`

Stacked specialisation:

- `DASHI/Governance/GuardedPropositionResponseTree.agda`
- `DASHI/Governance/DependentAuthorityCoercionKernel.agda`
- `DASHI/Governance/DiachronicDelegatedAuthorityBoundary.agda`
- `DASHI/Reasoning/RelationalChronologyProjectionBoundary.agda`
- `DASHI/Biology/TraumaMemoryAttractorPortfolio.agda`
- `DASHI/Biology/DirectedAttractorPortfolioCalculus.agda`
- `DASHI/Biology/DirectedBranchPolicyControl.agda`
- `DASHI/Biology/FiniteBranchPortfolioOptimisation.agda`
- `DASHI/Governance/ChildReligiousCoercionResearchBridge.agda`
- `DASHI/Culture/AmalekAuthorityProjectionBoundary.agda`
- `DASHI/Biology/ChildAuthorityTraumaSourceAtlas.agda`
- `DASHI/Biology/DirectedPortfolioSourceAtlas.agda`
- `DASHI/ChildAuthorityTraumaHyperfabric.agda`
