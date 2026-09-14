# SensibLaw CCW/LAWS Instrument Lifecycle Design

## Scope

Add a reusable SensibLaw international-instrument lifecycle model, a source-bounded 2026 CCW/GGE LAWS fixture, and a thin counter-UAS application bridge. Do not modify the generic `SensibLawOntologyTopology` carrier and do not treat the September 2026 GGE result as an adopted treaty or protocol.

## Existing owners reused

- `DASHI.Core.AttributedSourceCore`: source identity/DOI/URL/source-kind metadata; citation imports neither proof nor authority.
- `DASHI.Interop.SensibLawOntologyTopology`: treaties are already normative sources, legal systems are jurisdiction-indexed, and legal sources carry effective intervals.
- `DASHI.Core.QueryIndexedProjectionAdequacyExact` and `DASHI.Core.ObserverRefinementLatticeExact`: non-factorability and constructive observer refinement.
- `DASHI.Applications.CounterUASDroneShieldExact`: detection/threat/mitigation-authority separation.

## Lifecycle coordinates

Keep the following coordinates orthogonal rather than encoding one linear truth-state enum:

1. `NegotiationStatus`: discussion/proposal/consensus-elements/adopted-instrument.
2. `InstrumentNature`: unresolved/political/non-binding/legally-binding.
3. `LegalEffectStatus`: no-new-binding-effect/adopted-not-in-force/in-force.
4. `ApplicabilityStatus`: applicability-unresolved/bound-state-context-required/applicable/not-applicable.

A source record may describe any lifecycle coordinate but does not itself establish legal authority.

## Central non-factorability theorem

`BindingLegalEffect` does not factor through textual consensus alone. Two worlds can expose the same consensus-text surface while differing in institutional act/legal effect. Repair by joining text status with institutional/lifecycle status.

## 2026 CCW/GGE fixture

Primary institutional sources are UNODA/UN documents. The fixture must record:

- 2026 GGE mandate: formulate by consensus elements of an instrument **without prejudging its nature**.
- sessions: 2-6 March and 31 August-4 September 2026 in Geneva.
- the September 2026 state as consensus elements / instrument nature unresolved, without predicting the Seventh CCW Review Conference outcome.
- existing IHL applicability as a separate proposition from whether the GGE created a new binding rule.

No DOI is invented for UN documents. Missing DOI is atlas-local. QID/Dewey/OEIS metadata is only added when a verified identifier is actually recovered; absence is not silently filled by analogy.

## Attribution and snowball invariants

- Prefer primary/official institutional documents for status claims.
- Preserve author/issuing body, title/document symbol, publication context/date, canonical URL, source kind, and bounded formalisation relationship.
- Citation never imports proof, endorsement, legal authority, treaty status, or applicability.
- Acquisition may occur out of dependency order; downstream legal-effect/applicability payments cannot skip unpaid institutional steps.
- A later Review Conference outcome must append/refine lifecycle state rather than retroactively rewriting the September snapshot.

## Application bridge

`CounterUASSensibLawAuthorityBridgeExact` joins the existing domestic mitigation-authority coordinate with international-law lifecycle/context. It must not imply that every counter-UAS event is a LAWS event or an armed-conflict event.

Core boundary:

`technical capability != threat assessment != domestic mitigation authority != international-law applicability != lawful autonomous engagement`.

## Verification

Extend the existing `CounterUASDroneShieldRegression.agda` root so the focused #913 Agda workflow typechecks the generic lifecycle theorem, the 2026 source fixture, and the thin application bridge. Add the new files to the workflow path filter. Preserve the existing no-waveform/no-targeting/no-defeat-recipe scope.