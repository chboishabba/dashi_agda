module DASHI.Core.C3OrbitFibreDynamicsReceiptExact where

------------------------------------------------------------------------
-- Exact finite witness: C3 phase motion is hidden by the coarse orbit surface
-- but necessarily moves the retained provenance receipt.
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Graduate Texts in Mathematics 163, Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.C3OrbitProvenanceQuotientExact as Orbit
import DASHI.Core.FibrePreservingDynamicsExact as Dynamics
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Core.ProvenanceFibreDynamicsReceiptExact as ReceiptDynamics

rotateForward : C3.C3 → C3.C3
rotateForward x = C3.act C3.c1 x

rotateBackward : C3.C3 → C3.C3
rotateBackward x = C3.act C3.c2 x

rotateForwardBackward : ∀ x → rotateBackward (rotateForward x) ≡ x
rotateForwardBackward C3.c0 = refl
rotateForwardBackward C3.c1 = refl
rotateForwardBackward C3.c2 = refl

rotateBackwardForward : ∀ x → rotateForward (rotateBackward x) ≡ x
rotateBackwardForward C3.c0 = refl
rotateBackwardForward C3.c1 = refl
rotateBackwardForward C3.c2 = refl

rotateForwardPreservesSurface :
  Dynamics.SurfaceInvariant Orbit.orbitCore rotateForward
rotateForwardPreservesSurface x = refl

rotateBackwardPreservesSurface :
  Dynamics.SurfaceInvariant Orbit.orbitCore rotateBackward
rotateBackwardPreservesSurface x = refl

c3RotationAutomorphism : Dynamics.FibreAutomorphism Orbit.orbitCore
c3RotationAutomorphism =
  Dynamics.fibreAutomorphism
    rotateForward
    rotateBackward
    rotateForwardPreservesSurface
    rotateBackwardPreservesSurface
    rotateForwardBackward
    rotateBackwardForward

rotateC0ActuallyMoves : rotateForward C3.c0 ≡ C3.c0 → ⊥
rotateC0ActuallyMoves ()

c3RotationNontrivial : Dynamics.NontrivialFibreAutomorphism Orbit.orbitCore
c3RotationNontrivial =
  Dynamics.nontrivialFibreAutomorphism
    c3RotationAutomorphism
    C3.c0
    rotateC0ActuallyMoves

c3RotationHiddenTransition :
  Dynamics.HiddenTransition Orbit.orbitCore rotateForward C3.c0
c3RotationHiddenTransition =
  Dynamics.nontrivialFibreAutomorphismCreatesHiddenTransition
    c3RotationNontrivial

c3RotationMustChangeReceipt :
  Orbit.orbitReceipt (rotateForward C3.c0)
    ≡ Orbit.orbitReceipt C3.c0 → ⊥
c3RotationMustChangeReceipt =
  ReceiptDynamics.hiddenTransitionChangesReceipt
    Orbit.c3OrbitProvenanceBearingQuotient
    c3RotationHiddenTransition

c3RotationReceiptDifferenceComputes :
  Orbit.orbitReceipt (rotateForward C3.c0)
    ≡ Orbit.orbitReceipt C3.c0 → ⊥
c3RotationReceiptDifferenceComputes ()
