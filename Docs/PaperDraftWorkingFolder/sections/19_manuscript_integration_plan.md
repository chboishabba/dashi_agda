# 19. Manuscript Integration Plan After Outreach and Cross-Domain Intake

Status: docs-only worker lane; parent handoff; non-promoting.

## Compact O/R/C/S/L/P/G/F Summary

O: The parent manuscript integrator owns `Paper1_Manuscript.md`,
`SourceLedger.md`, and `ClaimLedger.md`; this worker owns only this planning
file. Lane owners and authority providers remain the only surfaces that can
promote mathematical, empirical, or physical claims.

R: Integrate the math-prof outreach and cross-domain variational-spine material
into Paper 1 without changing the paper's claim class: constructive physics
unification with fail-closed typed promotion boundaries. The manuscript should
gain clearer motivation, routing, and future-work boundaries, not completed
physics, chemistry, biology, perception, or TOE closure claims.

C: This plan is constrained by `Paper1_Manuscript.md`, sections 08-13,
`Docs/MathProfOutreachSummary.md`,
`Docs/MATH_PROF_OUTREACH_CROSSWALK.md`,
`DASHI/Physics/Closure/CrossDomainVariationalSpine.agda`,
`SourceLedger.md`, `ClaimLedger.md`, and
`Docs/LimitedSMGRPaperReadinessMatrix.md`.

S: The current manuscript already has a stable constructive-unification
structure: introduction, governance enforcement layer, abstraction, formal
core, empirical boundary, GR future-work boundary, formal-methods positioning,
provenance/literature positioning, claim ledger, validation checklist, and
conclusion. Outreach adds strategy and provenance. The cross-domain spine adds
a typed projection-defect / MDL theorem-target boundary with explicit
non-promotion fields.

L: The integration lattice is: provenance context, then theorem-target
boundary, then typed receipt, then paper-admissible positive claim, then
future empirical or physical adequacy. Outreach remains at provenance context.
The cross-domain spine sits at theorem-target boundary unless a later domain
receipt is inhabited.

P: Add one short cross-domain boundary section after formal-methods
positioning, tighten the provenance section with outreach source routing, add
ledger rows for outreach and cross-domain status, and leave the formal core
claim inventory unchanged.

G: No direct manuscript edits in this lane. Parent promotion requires exact
source-ledger status, claim-ledger status, and a final overclaim scan. Archive
threads, summaries, and cross-domain theorem targets cannot substitute for
repo-local typed receipts or accepted external authority tokens.

F: The remaining gap is editorial assembly. The parent must decide whether to
renumber sections or fold the cross-domain block into existing Section 8. The
substantive gap remains missing quantitative calibration, universality,
tractability, domain empirical receipts, and cross-domain recovery
equivalence.

## Recommended Integration Order

Use this order when editing `Docs/PaperDraftWorkingFolder/Paper1_Manuscript.md`.
It minimizes churn because it preserves the existing formal-core and blocked
physics sections.

1. Keep Sections 1-7 in their present order:
   introduction, governance, abstraction, formal core, empirical/Drell-Yan,
   GR boundary, and formal-methods positioning.
2. Insert a new short section immediately after current Section 7:
   `## 8. Cross-Domain Variational Spine Boundary`.
3. Move the current `## 8. Provenance and Literature Positioning` to
   `## 9. Provenance and Literature Positioning`, or fold the cross-domain
   block into it as `## 8.1` if the parent wants zero section renumbering.
   The cleaner paper shape is the new standalone Section 8.
4. Renumber the current claim ledger, validation checklist, and conclusion if
   using the standalone Section 8:
   current `## 9` becomes `## 10`, current `## 10` becomes `## 11`, and
   current `## 11` becomes `## 12`.
5. Update the claim ledger after adding the cross-domain section. This ensures
   the new section's allowed and forbidden interpretations are visible before
   validation.
6. Update the source ledger after the claim ledger. The source ledger should
   distinguish outreach summary/crosswalk context from the Agda cross-domain
   boundary record.
7. Run the final validation scan and `git diff --check -- Docs/PaperDraftWorkingFolder`.

Do not insert outreach material into the formal core. Do not add cross-domain
rows to the G2/G3/G6/E8 positive inventory unless the wording says
`theorem target`, `boundary`, or `non-promoting structural spine`.

## Exact Section Placement

### Introduction

Add at most one sentence near the end of Section 1, after the paragraph that
lists the current positive scope. This should frame outreach as motivation
and audience calibration, not as authority.

Suggested insertion:

```text
Recent math-professor outreach context sharpens the same editorial boundary:
the mathematical program is credible as a typed orbit, receipt, and obstruction
program, while the physics program remains early until its authority and
recovery surfaces are inhabited.
```

Do not mention wave, moonshine, B4, biology, perception, or molecule examples
in the introduction unless they are explicitly named as excluded future-work
context.

### Formal Core

Make no structural change to Section 4. The G2, G6, G3, and E8/Lila inventory
should remain the formal core of Paper 1.

If the parent wants one bridge sentence at the end of Section 4.4, use this:

```text
These core lanes also define the standard for any cross-domain extension:
structural theorem targets may be recorded, but they do not promote unless the
owning receipt or authority surface is inhabited.
```

This sentence is optional. It is safer to put the cross-domain material in its
own boundary section.

### New Section 8

Insert this section after current Section 7.

```text
## 8. Cross-Domain Variational Spine Boundary

The cross-domain material is included as a theorem-target boundary, not as a
new promoted result. The current Agda surface
`DASHI.Physics.Closure.CrossDomainVariationalSpine.canonicalCrossDomainVariationalSpineBoundary`
records a common typed object,
`(X, delta, pi, defect, gate, observation, symmetry)`, shared by physics,
molecular, bonding, biological, and perceptual target rows. Its positive value
for Paper 1 is structural: it shows how projection, defect, admissible descent,
observation quotient, and symmetry-orbit language can be stated in one typed
grammar.

The same boundary record also prevents over-reading. Its status is
`spineTypedNonPromoting`, and it records that quantitative calibration,
universality proof, computational tractability proof, chemistry, biology, and
perception empirical prediction receipts, and cross-domain recovery
equivalence remain missing. Accordingly, Paper 1 may say that DASHI has a
typed cross-domain variational spine as an outlook target. It may not say that
chemistry closure, bonding-energy prediction, molecular spectra, protein
folding, biological prediction, perceptual empirical fit, or universal TOE
closure follows from that spine.

This section should be read as future-work discipline. It keeps the
cross-domain ambition inside the same fail-closed governance model used for
G2, G3, G6, E8/Lila, empirical, and GR material. A cross-domain statement
becomes paper-admissible only when the relevant domain receipt or authority
surface is present; until then, the shared spine is a typed target and
exclusion ledger.
```

### Provenance and Literature Positioning

In the provenance section, keep the existing outreach ranking paragraph but
extend it to include the two local synthesis files. Use the outreach material
for routing, not for theorem authority.

Suggested replacement for the existing outreach bullet:

```text
5. The math-professor outreach context in
   `Docs/MathProfOutreachSummary.md` and
   `Docs/MATH_PROF_OUTREACH_CROSSWALK.md`, sourced from the thread titled
   `Math Prof Outreach Stage`, online UUID
   `69aa52b4-6f7c-839f-aa7f-d120ffe0c1ad`, canonical thread ID
   `decf9e3cde5ccdec0c51ad8aab15999201503998`.
```

Add this paragraph after the existing sentence that says the outreach ranking
should be used for manuscript strategy:

```text
The outreach summary should calibrate tone: the orbit/shell and signature
program is mathematically serious, local Agda scaffold surfaces now exist for
several outreach-facing objects, and the physics-side program remains early.
Those facts support introduction strategy, related-work routing, and
future-work staging. They do not expand the Paper 1 theorem inventory.
```

If adding cross-domain provenance to the same section, use this sentence:

```text
The cross-domain variational-spine module is repo-local evidence for a
non-promoting theorem-target boundary, not literature evidence and not an
empirical authority.
```

### Claim Ledger

In the main manuscript claim ledger, add one admissible claim after the E8/Lila
item, because it is structural and non-promoting:

```text
8. The cross-domain variational spine may be described as a typed structural
   theorem target with explicit non-promotion gates.
```

Add the required wording boundary immediately after that item:

```text
   This does not claim chemistry closure, bonding-energy prediction, molecular
   spectra, protein-folding or biological prediction, perceptual empirical
   fit, cross-domain recovery equivalence, or universal TOE closure.
```

In the blocked-claims list, add:

```text
11. chemistry, biology, perception, or cross-domain empirical prediction from
    the variational-spine boundary alone.
12. cross-domain universality, computational tractability, or recovery
    equivalence from the current spine target.
```

If the ledger is renumbered, preserve the existing full-DASHI-unification
blocker as the final blocker.

### Validation Checklist

Add these scans to the validation checklist:

```text
6. targeted text scan for cross-domain overclaims such as `chemistry closure`,
   `bonding prediction`, `molecular spectra`, `protein folding`, `biology
   prediction`, `perceptual fit`, `universal spine`, and `cross-domain
   recovery`
7. source-ledger audit confirming outreach files are non-promoting context and
   the cross-domain Agda module is a non-promoting theorem-target boundary
```

## Source Ledger Update Proposal

`Docs/PaperDraftWorkingFolder/SourceLedger.md` already has an archive outreach
context entry. Parent should preserve it and extend it rather than duplicate
it.

Add or revise the outreach entry to include:

```text
- `Docs/MathProfOutreachSummary.md`
- `Docs/MATH_PROF_OUTREACH_CROSSWALK.md`
- Source thread title: `Math Prof Outreach Stage`
- Online UUID: `69aa52b4-6f7c-839f-aa7f-d120ffe0c1ad`
- Canonical thread ID: `decf9e3cde5ccdec0c51ad8aab15999201503998`
- Use in Paper 1: tone calibration, introduction strategy, related-work
  routing, future-work staging, and exclusions only. Not theorem authority,
  not empirical authority, and not a substitute for repo-local typed receipts.
```

Add a separate repo-local theorem-target entry:

```text
## Repo-Local Non-Promoting Theorem Targets

- Source: `DASHI/Physics/Closure/CrossDomainVariationalSpine.agda`
- Canonical surface:
  `canonicalCrossDomainVariationalSpineBoundary`
- Use in Paper 1: optional cross-domain outlook/boundary section. This is
  evidence for a typed projection-defect / MDL theorem target whose own record
  says `spineTypedNonPromoting`.
- Allowed use: structural grammar for domain theorem targets across physics,
  molecular, bonding, biological, and perceptual rows.
- Forbidden use: chemistry closure, bonding theorem, spectra, molecular
  prediction, biology/cognition prediction, perceptual empirical fit,
  cross-domain recovery equivalence, or TOE closure.
```

## Claim Ledger Update Proposal

If updating `Docs/PaperDraftWorkingFolder/ClaimLedger.md`, add this allowed row:

```text
| Cross-domain variational spine boundary | `DASHI.Physics.Closure.CrossDomainVariationalSpine.canonicalCrossDomainVariationalSpineBoundary` | DASHI may describe a typed projection-defect / MDL spine as a structural theorem-target boundary across physics, molecular, bonding, biological, and perceptual rows. |
```

Add these required blocked claims:

```text
- Cross-domain variational-spine material remains non-promoting: no chemistry
  closure, bonding-energy theorem, spectra, molecular prediction, biology or
  cognition prediction, perceptual empirical fit, cross-domain recovery
  equivalence, or universal TOE closure follows.
- The first missing cross-domain receipts remain quantitative calibration,
  universality proof, computational tractability proof, domain empirical
  prediction receipts, and cross-domain recovery equivalence.
```

## What To Exclude

Exclude these from the main Paper 1 positive result:

1. Any outreach archive or summary sentence used as theorem authority.
2. Any claim that the orbit/shell profile proves physical unification.
3. Any claim that local wave-lift, B4 shell series, twined traces, moonshine,
   JMD, Monster, psi, topology, MDA/MDL, or kernel-learning material is a
   dependency of Paper 1's promoted result.
4. Any claim that gauge, constraint, spin-local Lorentz, or dynamic-candidate
   scaffolds close matter coupling, a natural dynamics law, a conserved
   physical quantity, continuum limit, realization-independent closure, GR,
   QFT, or limited SM+GR.
5. Any claim that the cross-domain spine predicts chemistry, bonding energies,
   spectra, molecular behavior, protein folding, biology, cognition, or
   perception.
6. Any claim that stable scientific objects across domains are literally the
   same object rather than represented by a shared typed local-minimum schema.
7. Any claim that `fixedPointClaimIsStructural = true` implies quantitative
   calibration or empirical depth.
8. Any positive use of `universal`, `validated`, `closed`, `recovered`,
   `derived`, or `prediction` in the cross-domain section unless the sentence
   names the corresponding missing receipt or blocker.

## Parent Assembly Notes

The lowest-churn path is to insert the new cross-domain section and update
only ledgers/checklists. The formal core should remain unchanged because the
new material does not alter the G2/G3/G6/E8 receipt inventory.

If the paper needs to be shorter, fold the cross-domain section into the
provenance/literature section as a three-paragraph "Cross-Domain Outlook
Boundary" subsection and skip global renumbering. That version is less clean
but still safe if the claim ledger and validation checklist are updated.

The parent should run the final exact command:

```text
git diff --check -- Docs/PaperDraftWorkingFolder
```
