# 12. Formal-Methods Positioning

Status: `docs-only; positioning section; fail-closed; non-promoting`

This section positions the DASHI Paper 1 contribution relative to established
formal-methods practice. It does not add a new theorem surface. Its purpose is
to explain why typed obstruction governance is a recognizable formal-methods
move, how it differs from stronger proof-assistant claims, and which external
literature targets should be attached before the manuscript is promoted.

## 12.1 O/R/C/S/L/P/G/F Position

In the working formal model, DASHI Paper 1 can be described as follows.

O, the organization, is a multi-lane Agda development whose paper-facing
claims are routed through typed receipts, audits, and named blockers.

R, the requirement, is fail-closed claim governance: a result may be stated as
paper-admissible only when its owning lane exposes the relevant inhabited
surface. Constructorless authority tokens, request packets, diagnostics, and
historical worklog claims remain blockers until the owning receipt exists.

C, the code/artifact surface, is the current repo-backed inventory named in the
working manuscript: G2 schema-extension receipt surfaces, G6 official tracked
cross-lane commuting and above-threshold surfaces, G3 selected finite-support
subtraction support, and E8/Lila local-to-upstream promotion-boundary audits.

S, the state, is deliberately mixed. Some internal receipt surfaces are
inhabited and usable for Paper 1. Empirical authority, Drell-Yan luminosity
convention authority, non-flat GR recovery, Schwarzschild recovery, upstream
E8 completion, old full G6 `LaneOperator` promotion, and global G3 operator
closure remain blocked.

L, the lattice, is the partial order of promotion levels: local construction,
diagnostic, request, typed receipt, authority token, paper-facing theorem, and
later empirical or physical adequacy claim. DASHI's contribution is to make the
non-monotone jumps in that lattice explicit: a diagnostic cannot silently
become an authority token, and a local semantic theorem cannot silently become
an upstream receipt.

P, the proposal, is to present DASHI as a typed obstruction-governance method
for formal carrier development, not as a completed physics unification result.
The positive claim is packaging discipline plus bounded formal progress.

G, the governance rule, is that external positioning can contextualize the
method but cannot promote a DASHI claim. The promotion path remains repo-local:
named theorem, receipt, diagnostic, audit, or authority surface first; prose
second.

F, the remaining gaps, are bibliography hardening and theorem-audit
integration. External citations must be attached to the formal-methods
positioning, and each citation must be used only for the concept it actually
supports.

## 12.2 Relation to Proof Assistants and Dependent Type Theory

DASHI sits naturally in the proof-assistant tradition because it uses Agda's
type checker as part of the claim boundary. The paper should not overstate
this as full mechanization of the target physics. The more precise statement
is that selected carrier, receipt, and obstruction surfaces are represented in
a dependently typed environment, where absence of an inhabitant is treated as
meaningful manuscript state.

This aligns DASHI with dependent type theory at the level of method:
propositions are represented by types, proofs or certificates by inhabitants,
and missing constructors by uninhabited obligations. The distinctive feature
for this paper is not merely that some mathematics is mechanized. It is that
paper admissibility is also typed: the system records when a downstream
manuscript claim lacks the exact receipt needed to state it.

The positioning should therefore avoid saying that DASHI has mechanically
proved a unified physical theory. It may say that DASHI uses proof-assistant
infrastructure to separate checked internal closure from blocked promotion
claims.

## 12.3 Relation to Proof-Carrying Code and Proof-Carrying Data

Typed receipt surfaces are close in spirit to proof-carrying code and
proof-carrying data. In those settings, an artifact is accompanied by a
certificate that a checker can validate before accepting the artifact for a
specific use. DASHI applies a similar discipline to research claims: a paper
claim is accepted only when the corresponding typed receipt, authority token,
or audit surface is available at the owning boundary.

The analogy should stay bounded. DASHI Paper 1 is not claiming a general PCC
framework, a certified compiler, or a reusable proof-carrying-data protocol.
The useful comparison is conceptual: the manuscript consumer should not trust
an unsupported artifact merely because it is nearby in the repo. The claim must
carry, or point to, the relevant typed evidence.

This framing is especially important for empirical and provider-facing lanes.
A provider packet, checksum, HEPData diagnostic, or request template can
improve provenance. It does not become an accepted-evidence authority token
unless the governing authority surface is actually inhabited.

## 12.4 Relation to Certified Pipelines

Certified-pipeline work shows how a long chain can be made trustworthy by
checking each transformation and preserving the proof obligations between
stages. DASHI's current contribution is narrower but adjacent: it exposes
which stages of the pipeline are certified, which are diagnostic, and which
are request-only.

For Paper 1, the pipeline is not data-to-physics validation. It is
claim-to-receipt validation. The G2, G6, G3, and E8/Lila surfaces provide a
bounded formal core. The empirical, W4/W5, and GR surfaces remain downstream
pipeline obligations. A certified-pipeline citation can support the general
principle that end-to-end trust requires preserved obligations across stages;
it should not be used to imply that DASHI already has such an end-to-end
physics pipeline.

## 12.5 Relation to Mechanized Mathematics

Mechanized mathematics provides a useful comparison point for DASHI's theorem
and obstruction surfaces. Large proof developments often succeed not only by
proving target theorems, but also by maintaining libraries, interfaces,
lemmas, and explicit dependency boundaries. DASHI Paper 1 belongs to that
engineering culture: it reports a formal package whose value depends on
precise module anchors and refusal to hide missing lemmas.

The paper's current contribution is therefore closer to a formal
infrastructure and auditability result than to a finished flagship theorem.
The G3 finite-support route, for example, should be presented as constructive
support for selected operators plus named norm-law blockers, not as completed
global operator closure. The E8/Lila route should be presented as local
semantic completeness and upstream-promotion audit, not as upstream completion
itself.

Mechanized-mathematics citations can support the broader practice of
machine-checked proof development, library-scale proof engineering, and
formal theorem audit. They should not be used as evidence for any DASHI theorem
unless the theorem is separately cited to the repo surface.

## 12.6 Provenance, Traceability, and Theorem Auditability

DASHI's provenance posture is stronger when stated as traceability rather than
authority. The working folder records robust-context IDs, NotebookLM IDs,
local worklogs, source ledgers, and repo-local control documents. Those
materials help reconstruct why a lane exists and how a claim was selected.
They do not certify the claim.

The theorem-audit rule is simple: every promoted statement should be traceable
to an exact surface, and every blocked statement should be traceable to an
exact obstruction. This makes the manuscript reviewable in both directions. A
reader can ask which Agda object supports a positive statement, and can also
ask which absent token prevents a stronger statement.

This is the main formal-methods positioning claim for Paper 1. DASHI does not
only accumulate proofs; it records the difference between proof, request,
diagnostic, provenance, and authority. That difference is essential for a
paper about an incomplete but actively governed formal carrier core.

## 12.7 Safe Manuscript Wording

Safe wording:

> DASHI uses Agda-backed typed receipt surfaces to make paper-admissibility
> fail closed. The current Paper 1 contribution is a bounded formal carrier
> package with explicit obstruction accounting; empirical validation and
> non-flat GR recovery remain blocked by named authority and theorem surfaces.

Avoid wording:

> DASHI is a fully certified physics pipeline.

> The proof assistant validates the full unification claim.

> Provenance records and diagnostics are equivalent to formal receipts.

> Local E8 semantic completeness proves upstream E8 root enumeration
> completion.

> Drell-Yan diagnostics establish accepted empirical authority.

## 12.8 Citation Targets

The following are citation targets, not verified bibliography entries. Exact
bibliographic data, editions, URLs, and page references still need final
verification before manuscript submission.

| Target | Should support | Use boundary |
|---|---|---|
| Martin-Lof dependent type theory or standard dependent type theory reference | propositions-as-types, types-as-specifications, inhabitants as proofs | Do not cite as evidence that DASHI proves physical adequacy. |
| Agda system/reference/manual citation target | Agda as the implementation environment for dependent types and checked definitions | Do not cite as a DASHI theorem source; repo surfaces carry DASHI claims. |
| Coq proof assistant citation target | proof assistants as machine-checked theorem environments | Comparative context only. |
| Lean and mathlib citation targets | large-scale mechanized mathematics and library-scale theorem development | Comparative context only; not a DASHI dependency. |
| Isabelle/HOL citation target | mature proof-assistant ecosystem and theorem audit practice | Comparative context only. |
| de Bruijn criterion citation target | independent checking of proof objects or proof certificates | Use to motivate checkability; do not imply all DASHI artifacts are independently exported proof objects. |
| Necula proof-carrying code citation target | artifacts carrying certificates checked before acceptance | Analogy for typed receipts; DASHI is not claiming a general PCC framework. |
| proof-carrying data citation target | data or computational artifacts accompanied by checkable evidence | Analogy for provider packets and receipts; request packets remain non-promoting. |
| CompCert citation target | certified compiler or certified pipeline exemplar | Supports end-to-end certification as a related ideal; DASHI Paper 1 is not claiming a certified physics pipeline. |
| seL4 verification citation target | large practical verification project and auditability of implementation claims | Comparative formal-methods context only. |
| Flyspeck or formal proof of the Kepler conjecture citation target | large mechanized mathematical proof and theorem-audit practice | Comparative mechanized mathematics context only. |
| W3C PROV or canonical provenance-model citation target | provenance records and traceability vocabulary | Supports provenance/traceability language; not a formal receipt source. |
| software supply-chain attestation or in-toto/SLSA citation target | staged attestations and preservation of trust boundaries across pipelines | Optional analogy for claim pipeline governance; do not imply DASHI has adopted that standard. |

## 12.9 Integration Checklist

Before this section is merged into the main manuscript:

1. Replace each citation target with a verified bibliographic entry or remove
   the sentence that depends on it.
2. Keep all DASHI-positive claims tied to exact repo surfaces already listed
   in the formal-core section.
3. Keep empirical, W4/W5, GR, upstream E8, old full G6, and global G3 claims
   in blocked language unless their owning typed receipts are inhabited.
4. Ensure the bibliography does not make the external literature carry DASHI
   theorem claims that only the repo can carry.
