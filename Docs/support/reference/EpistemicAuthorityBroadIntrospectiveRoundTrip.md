# Epistemic authority broad introspective round trip

## Scope

This specimen formalises the broader theory developed in the legal/folk-law thread. It is structural rather than a historical proof or legal conclusion.

The formal model distinguishes:

- socially learned legal anchors from local/tentative legal knowledge;
- a Pareto trade-off between a folk model (anchor fit / low revision cost) and an institutional model (new-evidence fit) before observer refinement;
- public rule visibility from authority to evaluate positions and assign binding meaning;
- a coarse folk observer from a separating institutional observer;
- public rule access from Go/chess-like position-evaluation competence;
- objective apparentness from actual comprehension;
- verified explanation/teach-back as an observer refinement that can change the feasible model set;
- AI action-language expansion from observer refinement.

## Formal files

- `DASHI/Reasoning/FolkLawEpistemicAuthorityCaptureExact.agda`
- `DASHI/Reasoning/FolkLawEpistemicAuthorityBroadExact.agda`
- `DASHI/Reasoning/EpistemicAuthorityIntrospectiveVisualReceiptExact.agda`
- `DASHI/Reasoning/EpistemicAuthorityBroadVisualFindingExact.agda`

## Visual proof

Generate the refined SVG with:

```bash
python tools/introspective_epistemic_authority_broad.py
```

The output path is:

```text
artifacts/introspective/epistemic-authority/epistemic_authority_broad_visual_proof.svg
```

The visual has six linked claims:

1. capture is a change in authority profile, not necessarily rule secrecy;
2. the same fine states can collide under the folk observer and separate under the institutional observer;
3. public rules and a fine position feed folk and institutional evaluators in parallel;
4. receipt/objective apparentness and actual comprehension occupy distinct lanes;
5. learned anchors can keep multiple models Pareto-live before refinement, while verified explanation can remove a model from the feasible set;
6. AI can enlarge the action language without refining the coarse observer.

## Introspective finding

The first broad visual draft used ordinary directed arrows too freely. Direct inspection revealed that it falsely suggested two sequential derivations:

```text
public rules -> institutional evaluation
folk evaluator -> institutional evaluator
```

The refined visual grammar instead distinguishes:

```text
authority-profile transition
shared-input computation
epistemic refinement
capability inclusion
```

The resulting mathematical finding is stronger than a graphical cleanup. The broad Agda module proves that no generic reconstruction

```text
FolkObservation -> InstitutionalObservation
```

can agree with the institutional observer on both fine states in the canonical folk collision fibre. In other words, institutional evaluation does not in general descend through the coarse folk projection.

A second refined result makes public visibility orthogonal to capture: `CaptureWithoutSecrecy` witnesses a profile in which community norm memory persists and rules are public while position evaluation and binding interpretation are institutionally seated.

## Non-claims

- This is not a proof of a particular historical genealogy of Western law.
- It does not establish that every self-represented litigant fails to comprehend written advice.
- It does not establish that verified conversation always causes withdrawal.
- It does not claim that a larger AI-enabled action set lowers ideal optimal utility; the old actions remain available.
- The visual is an observer of the formal model, not independent semantic authority. The reified results are the explicit defects/refinements found by inspecting that observer.
