# Orbit Profile Signature Discrimination

## Headline

The current finished mathematical result in this repo is:

> The orbit shell profile computed from the shift dynamics uniquely selects
> Lorentz signature `(3,1)` among the candidate 4D signatures.

This is a classification theorem. The repo now also closes the cone-to-profile
bridge for the current finite 4D shift realization, but not yet as a fully
realization-independent theorem.

## Canonical Theorem Path

The intended proof-reading order is:

1. `DASHI.Physics.OrbitProfileComputedSignedPerm`
   computes the shell profile for the 4D signed-permutation action.
2. `DASHI.Physics.Signature31ShiftProfileWitness`
   packages that computed profile as the concrete witness consumed downstream.
3. `DASHI.Geometry.ConeArrowIsotropyShellAction` and
   `DASHI.Geometry.ConeArrowIsotropyShellEnumeration`
   provide the abstract shell-action and shell-enumeration layer.
4. `DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration`
   instantiates that layer for the finite 4D shift realization and derives the
   shell-orbit enumeration from the shell action.
5. `DASHI.Physics.ConeArrowIsotropyOrbitProfileAgreement`
   turns the Stage B shift bridge into the profile equality consumed by the
   theorem layer.
6. `DASHI.Physics.Signature31FromShiftOrbitProfile`
   proves the theorem-level `sig31` result from the computed profile and the
   profile discriminant.
7. `DASHI.Physics.Closure.PhysicsClosureInstanceAssumed` and
   `DASHI.Physics.Closure.PhysicsClosureFullInstance`
   consume that signature result.
8. `DASHI.Physics.Closure.SpinDiracGateFromClosure`
   is a downstream consumer of the closure, not the primary theorem headline.

## Current Stage B Status

For the current finite 4D shift realization, the repo now proves:

- the finite shell carrier, shell predicates, and finite signed action are
  supplied through `SignatureAxioms`,
- `AbstractShellAction` carries that structure through the geometry layer,
- shell-orbit enumeration is derived from that shell action rather than
  reconstructed locally in the shift bridge,
- the resulting orbit profile agrees with the computed signed-permutation
  profile used by the Stage A discriminant.

This closes the Stage B bridge for the current finite realization framework.

## Current Open Generalization

What remains open is the broader intrinsic theorem beyond the current finite
4D realization. The repo does not yet prove that arbitrary abstract
cone/arrow/isotropy data force the same shell-orbit structure without passing
through the present finite ternary signed-permutation realization.

## Outreach Framing

For external mathematical communication, the conservative and accurate summary
is:

> We compute an orbit shell invariant from the dynamics and show that it
> uniquely identifies Lorentz signature `(3,1)` among the candidate 4D
> signatures. In the current finite 4D realization, the cone/arrow/isotropy
> structure now derives the shell-orbit profile used by that discriminant. The
> remaining open problem is to generalize that bridge beyond the present finite
> realization.

## Next Roadmap

For the staged internal research path from the current theorem state to the
cone-forcing theorem target and the longer-horizon full-closure program, see:

- `Docs/ResearchRoadmap_A_to_C.md`
