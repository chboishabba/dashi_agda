# 16. Outreach Email Research Note

Status: `docs-only; outreach appendix; non-promoting`

## Compact Formal Model

O: This section is an outreach appendix for the Paper 1 working folder. It is
owned by the docs-only worker lane and is scoped to safe external prose for
mathematicians and nontechnical family or friends.

R: Distill the Gmail/outreach research-note material into two polished
artifacts without expanding the manuscript's theorem inventory: a half-page
mathematician research note and a one-paragraph plain-language summary.

C: Context is drawn from `Docs/PaperDraftWorkingFolder/Paper1_Manuscript.md`,
`Docs/MathProfOutreachSummary.md`, `Docs/MATH_PROF_OUTREACH_CROSSWALK.md`,
and the user-provided outreach instruction. This file is the only edited
artifact in this lane.

S: The current safe center is a contraction and closure program: a shell-orbit
or quadratic profile invariant selects the Lorentz signature class `(3,1)` in
the present four-dimensional framework, while several gauge, constraint,
wave-lift, graded-series, and local-Lorentz bridge surfaces exist as formal
scaffolds. Dynamics, conserved physical quantities, continuum limits, strong
matter/gauge closure, and realization-independent closure remain open.

L: The outreach lattice is `provenance/motivation -> scaffold -> proved local
claim -> promoted theorem authority`. The appendices may move motivation into
clear questions and may describe scaffolds as scaffolds, but they must not move
scaffolds into theorem authority.

P: Use the contraction-to-invariant-to-signature-to-constraint-closure spine as
the mathematician-facing note, and use a modest plain-language description for
family and friends.

G: Personal email, archive prose, and outreach summaries are provenance and
motivation. They are not theorem authority, empirical authority, or substitutes
for current typed DASHI receipts.

F: The missing promotion evidence is still substantial: a natural dynamics
law, a conserved quantity with settled physical interpretation, an explicit
continuum-limit theorem, strong matter/gauge constraint closure, and
realization-independent closure.

## Artifact 1: Mathematician Research Note

Subject: A constructive closure program around contraction, quadratic
invariants, and Lorentz signature

I am working on a dependently typed formalization project, DASHI, whose
current mathematical target is narrower than a physics unification claim. The
useful core is a closure spine:

```text
contraction data -> quadratic/profile invariant -> signature/cone class
                 -> constraint-closure obligations
```

The strongest present mathematical point is that, inside the current
four-dimensional framework, a shell-orbit profile invariant selects the
Lorentz signature class `(3,1)`. The intended reading is a symmetry and
orbit-profile statement, not an empirical or continuum-physics theorem. The
profile is treated as an invariant of the signed block-preserving
neighborhood, with `B4`/Weyl-style comparisons used as classifiers of nearby
finite shell behavior rather than as confirmation of physical Lorentzian
geometry.

The reason this is interesting is that the contraction picture appears to
force a quadratic invariant before one is allowed to speak responsibly about a
cone. Once the cone and signature class are fixed, the next mathematical
question is not "is this physics done?" but "which closure obligations become
typed and which ones fail closed?" In the present repository, that question is
made explicit through Agda receipt and obstruction surfaces. Some surfaces
exist as local scaffolds: wave-lift/even-subalgebra structure, finite
orbit-shell generating series, finite graded or twined shell traces, and
bridge records for gauge constraints, parametric gauge constraints, spin/local
Lorentz structure, and Lorentz-neighborhood dynamics. These are useful because
they make candidate closure paths inspectable instead of leaving them as
informal prose.

The claim boundary is deliberately conservative. The project may presently
describe a serious invariant/signature program and a typed audit method for
closure routes. It may also say that local formal scaffolds exist for several
bridge directions. It should not say that it has derived a natural dynamics
law, identified a conserved physical quantity with settled interpretation,
proved a continuum limit, closed matter/gauge constraints in the strong sense,
or obtained realization-independent physical closure.

For review, the best mathematical question is therefore local and structural:
does the contraction-to-quadratic-invariant step genuinely force the stated
signature/cone class in the formal setting, and do the subsequent constraint
obligations have the right shape to become theorems rather than rhetoric?

### Proved / Scaffold / Open

Proved or currently admissible:

1. A shell-orbit profile invariant selects the Lorentz signature class `(3,1)`
   in the current four-dimensional framework.
2. The manuscript can present DASHI as a fail-closed constructive closure
   architecture: promoted claims require typed receipts, and missing receipts
   remain visible as blockers.
3. Local formal objects exist for finite orbit-shell and graded-series style
   comparisons, including `B4`-neighborhood classifiers.

Scaffolded but not promoted:

1. Wave-lift/even-subalgebra structure.
2. Gauge-constraint and parametric gauge-constraint bridge records.
3. Spin/local-Lorentz and Lorentz-neighborhood dynamic candidate records.
4. Finite graded or twined shell-trace objects whose mathematical
   significance is not yet settled.

Open:

1. A natural dynamics law.
2. A conserved quantity with a settled physical interpretation.
3. An explicit continuum-limit theorem.
4. Strong matter/gauge/constraint closure.
5. Realization-independent closure and any empirical physics promotion.

## Artifact 2: Plain-Language Family/Friend Summary

I am writing up a careful mathematical software project about how to keep big
physics-shaped ideas honest. The current result is not "a theory of
everything"; it is a checked framework that separates what has actually been
proved from what is only a promising bridge or an open problem. The most
interesting part so far is a pattern where a symmetry calculation points to
the same kind of space-time signature used in relativity, and the project then
tracks exactly what would still be needed before anyone could responsibly call
that physics. In plain terms: there is a real mathematical signal, there are
some useful formal scaffolds around it, and there is still a long list of hard
things not yet proved.
