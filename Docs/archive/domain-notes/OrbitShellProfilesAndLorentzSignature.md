# Orbit-Shell Profiles and Lorentz-Signature Discrimination in 4D

## Purpose

This note is the repo-facing explanation of the current mathematical spine:

- shell-orbit profiles under signed actions,
- 4D Lorentz-signature discrimination,
- the current validation state across multiple realizations,
- and the exact gap between the present results and stronger realization-
  independent closure claims.

It is written for mathematically literate readers. It is **not** a claim of
full physics closure.

## Current Theorem Ladder

### Stage A

The current finished theorem headline is:

- an orbit-profile discriminator in 4D selects the Lorentz signature class
  `(3,1)` among the candidate signatures.

This is the theorem-backed “classification” result.

### Stage B

For the current finite 4D framework, the repo also has a theorem-backed bridge
from:

- cone + arrow + isotropy
- to shell action
- to shell-orbit enumeration
- to orbit profile
- to `sig31`

This bridge is solved only for the present finite realization framework.

### Stage C

The repo does **not** claim finished physics closure.

The current Stage C target is:

- minimum credible physics closure,
- theorem-backed dynamics package,
- observable / validation surface,
- forward-benchmark program.

## Why the Orbit Profile Is the Keystone

The current codebase repeatedly routes through the same object:

- shell points,
- symmetry action,
- orbit enumeration,
- profile invariant.

That object is what drives:

- signature discrimination,
- realization comparison,
- closure-facing validation summaries.

So the repeated return to the orbit profile is not accidental. It is the
current keystone invariant of the stack.

## Shell-Neighborhood Class

The current evidence supports a cleaner ordering:

- shell-neighborhood class,
- then orbit-profile family,
- then signature class.

In particular:

- the signed-permutation shift reference sits in the **one-minus shell
  neighborhood**,
- the independent `B₄` realization sits in the **definite shell
  neighborhood**.

This is stronger and cleaner than treating every realization as if it were
directly competing for immediate Lorentz promotion.

## Mathematical Neighborhood

The current shell/profile object is closest in spirit to:

- a signed shell-orbit invariant,
- a Weyl/Coxeter orbit statistic,
- a theta-series-like shell fingerprint,
- or a weight-enumerator-like symmetry-reduced profile.

Those are **analogies**, not current theorem claims.

The most natural symmetry neighborhood for the present 4D signed-permutation
story is:

- `B₄` / hyperoctahedral / signed-permutation geometry.

That is why the next serious alternate realization is being tested in that
language.

## Moonshine Ordering

The current safe downstream ordering is:

1. Weyl/root-system/signed-lattice shell data,
2. theta-series-like or weight-enumerator-like repackaging,
3. only then any Niemeier/umbral-style question if a root-lattice shell model
   actually appears,
4. and only after a genuine grading/trace bridge any Monster-style question.

This ordering matters.

For the current repo state, the shell/profile story is closest to
Weyl/root-system/theta-like combinatorics.

If a future realization packages the same orbit-shell data as a shell
enumerator on a root-lattice object, then it becomes reasonable to ask whether
the invariant lives near the same lattice/modular ecosystem as
Niemeier/umbral moonshine.

That is still a neighborhood comparison, not a theorem claim.

For Monster/Moonshine, the bar is much higher:

- a graded module or comparably structured wave-lifted object,
- trace-like or graded-series data,
- and a theorem-level bridge from the current finite orbit-shell invariant to
  that graded structure.

Related reporting discipline:

- if a Monster-labeled corpus only shows a small rigid substructure under an
  embedding but does not separate from non-Monster controls as a class, the
  safe statement is negative:
  no distinct Monster fingerprint has been shown.
- Shared rigid slots are not enough by themselves; they can reflect generic
  stylistic or structural regularity rather than Monster-specific
  self-reference.

Without those pieces, the current repo should be described as
**pre-moonshine**: orbit enumerators, shell polynomials, and
Weyl/root-system combinatorics, not a graded-trace theorem.

## Orbit-Shell Generating Series

The repo already contains a finite orbit-shell generating series as a local
formal object. In particular:

- `DASHI.Physics.OrbitShellGeneratingSeriesRootSystemB4` constructs a finite
  series from explicit shell data,
- the same series layer is re-exported through the current validation summary
  surfaces for comparison work.

This series is built from:

- the orientation tag when available,
- the shell-1 orbit-size multiplicities,
- the shell-2 orbit-size multiplicities.

This series makes current orbit data easier to compare across realizations
without changing the theorem source. For the signed-permutation shift
realization, it is derived directly from the same profile inputs used by the
4D signature discriminant.

Immediate uses:

- a theorem-backed shift-series witness,
- a standalone `B₄` series comparison,
- a prototype wave-graded lift that uses the finite series as a grade-0 seed.

This is an algebraic repackaging of the present shell data. It is **not** yet
a theta-series theorem, a modular-form theorem, or a graded-trace theorem.

The current symmetry-facing prototype layer is:

- finite graded shell series built from actual shell-state counts,
- finite signed/Weyl actions on shell states,
- twined finite traces computed as fixed-point counts on graded shell pieces,
- a wave-facing grading adapter kept explicitly as a prototype.

This is now landed as **pre-moonshine** infrastructure. It does not yet claim:

- modularity,
- Niemeier/umbral identification,
- Monster traces,
- or a graded infinite-dimensional module.

## One-Minus Shell Family

The current one-minus family visible in the repo is:

- `m = 2 -> [2,2]`
- `m = 3 -> [8,4,2]`
- `m = 4 -> [24,6,2]`
- `m = 5 -> [48,8,2]`
- `m = 6 -> [80,10,2]`
- `m = 7 -> [120,12,2]`
- `m = 8 -> [168,14,2]`

For the bounded range already encoded in the repo, the intended shell-1 family
formula is:

- `m = 2 -> [2,2]`
- `m = 3 -> [8,4,2]`
- `m >= 4 -> [4(m-1)(m-2), 2(m-1), 2]`

The next theorem milestone is to make this bounded family explicit and
theorem-backed for `m = 2..8`, then promote the following milestones to:

- a parametric `m` family layer,
- then a full parametric theorem.

The next implementation target after the bounded theorem is therefore:

- make the one-minus shell-1 family parametric in `m`,
- use that parametric layer as the shell-neighborhood explanation for the current shift
  reference,
- then tighten that parametric layer into a full theorem,
- keep the canonical Stage C entrypoint explicit in code while the theorem
  seam is still being finished,
- and only then resume the search for a second realization in the same
  Lorentz-family neighborhood.

## Current Validation Snapshot

The current repo-facing validation summary is:

- signed-permutation reference: `exactMatch`
- synthetic one-minus admissible alternate realization: `exactMatch`
- Bool inversion secondary admissible alternate realization: `signatureOnlyMatch`
- tail-permutation negative control: `mismatch`

The current synthetic Lorentz-neighborhood search surface is:

- shell-1 exact match to the shift reference,
- shell-2 exact match to the shift reference,
- explicit promotion-bridge status now saying the current synthetic path is
  admissible-ready,
- a minimal independent-dynamics witness is now present on that path.

This already shows:

- the signature-level result is stronger than exact shell-profile rigidity
  across all nearby realizations,
- and the validation harness is now strong enough to distinguish admissible
  alternates from negative controls.

## Current B₄ Status

The repo now has an independent `B₄` shell/profile computation built from:

- explicit root-shell points,
- a Weyl-style action,
- standalone shell-orbit enumeration.

But it is still **not** routed into the admissible rigidity harness.

Reason:

- its current shell data land in the **definite shell class** `[8] / [24]`,
  not in the Lorentz shell class `[24,6,2] / [16,12]`,
- so orientation/signature promotion is blocked structurally, not just by
  missing wiring.

So the honest current `B₄` status is:

- independent shell/profile report: **yes**
- current shell neighborhood: **definite-shell-class**
- standalone series comparison: **next**
- admissible comparison realization: **not yet**

## What the B₄ Realization Is Testing

The `B₄` realization is intended to answer:

> is the current shell/profile result a shift artifact, or is it really a
> signed-orbit invariant in a known symmetry neighborhood?

That is a better mathematical test than adding another ad hoc dynamics with no
known geometric interpretation.

## What Is Still Missing

Four important things remain open:

1. a stronger realization-independent orbit/profile theorem,
2. a theorem-backed bounded one-minus shell-family object for the currently
   encoded dimensions,
3. the later parametric `m` generalization of that family,
4. broader physics closure beyond the current signature-and-validation spine.

In particular, the repo still does **not** have:

- GR/QFT recovery,
- a finished matter/gauge sector,
- or a realization-independent final closure theorem.

## Safe Claim Boundary

The strongest safe current claim is:

> the repo contains an Agda-formalized 4D orbit-profile discriminator that
> selects the Lorentz signature class, plus a closure/validation program that
> now compares multiple realizations against that invariant.

That is strong.

It is **not** the same as:

- “physics solved”
- “GR derived”
- “full closure proved”

## Next Step

The next step after this note is:

- add a canonical shell-neighborhood classification layer,
- prove the bounded one-minus shell-family theorem for `m = 2..8`,
- use that family to sharpen the shift-side Lorentz story,
- and record **parametric `m`** as the next theorem milestone after the
  bounded family lands.

For outreach-specific framing of the scaffold-vs-theorem boundary, see
`Docs/MathProfOutreachSummary.md` and `Docs/MATH_PROF_OUTREACH_CROSSWALK.md`.

Current closure-side hardening target alongside that theorem work:

- keep the recommended Stage C path on the concrete shift dynamics package and
  the intrinsic `(3,1)` theorem,
- and remove the last trivial constraint shim from the empirical full adapter,
- while exposing the synthetic-promotion blocker and strengthened dynamics
  status directly through the validation/closure summaries.
  so the closure-facing full adapters share the same concrete constraint
  witness.
