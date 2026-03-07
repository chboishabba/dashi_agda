# Research Roadmap: A -> B -> C

## Current Theorem State

The current finished mathematical headline in this repo is:

> **Stage A — Orbit Profile Signature Discrimination**  
> The orbit shell profile computed from the shift dynamics uniquely selects
> Lorentz signature `(3,1)` among the candidate 4D signatures.

The canonical path is:

`OrbitProfileComputedSignedPerm`
-> `Signature31ShiftProfileWitness`
-> `Signature31FromShiftOrbitProfile`
-> `PhysicsClosureInstanceAssumed` / `PhysicsClosureFullInstance`
-> `SpinDiracGateFromClosure`

This is the finished classification theorem. In addition, the repo now closes
the Stage B bridge for the current finite 4D shift realization: the
cone/arrow/isotropy instance carries a finite shell realization and finite
isotropy realization, the shell-orbit enumeration is derived from the abstract
shell-action layer, and the resulting profile agrees with the computed
signed-permutation profile used by the Stage A discriminant.

What is still missing is the broader generalization beyond the current finite
4D realization. The repo does not yet prove that arbitrary abstract
cone/arrow/isotropy data force the same shell-orbit structure without passing
through the current finite realization framework.

## Stage A — Orbit Profile Signature Discrimination

Stage A is the finished theorem layer currently supported by the repo.

What it establishes:

- a concrete orbit shell invariant is computed from the 4D shift dynamics,
- that invariant is matched against the candidate signatures
  `sig40`, `sig31`, `sig22`, `sig13`, `sig04`,
- the discriminant uniquely selects `sig31`.

Immediate implications:

- a new invariant for dynamical classification,
- a signature detector derived from orbit statistics,
- a mathematically clean entrypoint for collaborators and outreach.

Primary repo anchors:

- `DASHI.Physics.Signature31ShiftProfileWitness`
- `DASHI.Physics.Signature31FromShiftOrbitProfile`
- `DASHI.Physics.Closure.PhysicsClosureSummary`

## Stage B — Cone -> Signature Forcing

Stage B is now solved for the current finite 4D shift realization framework.

Current status:

- complete for the concrete finite 4D shift realization,
- still open as a fully realization-independent theorem.

Target statement:

`cone invariance + arrow/time orientation + isotropy -> orbit shell profile`

combined with Stage A:

`orbit shell profile -> sig31`

to yield:

`cone invariance + arrow/time orientation + isotropy -> sig31`

What is now proved in the current framework:

- `SignatureAxioms` carries the finite shell carrier, shell predicates, and
  finite isotropy action for the 4D shift instance,
- `AbstractShellAction` transports that data through the geometry-side shell
  action layer,
- generic shell enumeration derives the shell-orbit profile from that abstract
  shell action,
- the resulting profile is proved equal to the computed signed-permutation
  profile used by the Stage A discriminant,
- therefore the concrete finite 4D cone/arrow/isotropy realization forces
  `sig31`.

What remains open beyond Stage B:

- remove dependence on the current finite realization framework itself,
- derive the shell-orbit structure from more intrinsic abstract hypotheses,
- generalize beyond the current ternary 4D signed-permutation model.

## Stage C — Full Closure Program

Stage C is a speculative long-horizon research program, not a current theorem.

The intended direction is:

`ultrametric contraction`
-> `quadratic / polarization / orthogonality`
-> `cone structure`
-> `signature forcing`
-> `closure consequences`
-> possible deep symmetry structure

Possible downstream themes include:

- stronger closure and geometric rigidity results,
- representation-theoretic explanations of the orbit invariant,
- Monster/Moonshine-style symmetry as a later structural hypothesis or theorem
  target.

Stage C must not be described as proved by the current repo state.
Any Monster/Moonshine interpretation remains explicitly downstream and
speculative unless supported by separate theorem-level bridges.

## Milestones and Exit Criteria

### Stage A

Status: complete.

Exit criterion:

- the computed shift orbit profile uniquely selects `(3,1)` among the candidate
  4D signatures and is exposed through the theorem path.

### Stage B

Status: complete for the current finite 4D realization framework.

Exit criterion:

- the concrete shift theorem no longer depends on a manual profile or
  enumeration seam,
- the shell/action side determines the orbit profile theoremically,
- the signature theorem can be stated as a genuine cone-forcing result for the
  current finite 4D realization.

Remaining follow-on objective:

- generalize the theorem beyond the current finite realization framework.

### Stage C

Status: speculative.

Exit criterion:

- closure, symmetry, and downstream physical structures are linked by
  theorem-level bridges rather than assumption packages or compatibility
  scaffolding.

## Practical Implications by Stage

### A — Orbit invariant

- mathematical classification tool,
- geometric/signature inference from dynamics,
- possible new invariant for dynamical systems and optimization geometry.

### B — Cone -> signature forcing

- structural geometric theorem,
- causal-cone-first explanation of Lorentz signature,
- stronger classification of isotropic cone-preserving dynamics.

### C — Full closure

- speculative foundational structure,
- possible deep symmetry interpretation,
- potential long-term bridge between dynamics, geometry, and algebra.

The intended reading discipline is:

- A is proved,
- B is solved for the current finite 4D realization,
- C is a research program.
