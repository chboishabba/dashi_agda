module DASHI.Core.C3OrbitFibreDynamicsReceiptExact where

-- Dixon & Mortimer, Permutation Groups, Springer 1996.
-- DOI: 10.1007/978-1-4612-0731-3.

open import DASHI.Core.Prelude

import DASHI.Core.C3OrbitProvenanceQuotientExact as Orbit
import DASHI.Core.FibrePreservingDynamicsExact as Dynamics
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Core.ProvenanceFibreDynamicsReceiptExact as ReceiptDynamics

rotateForward : C3.C3 → C3.C3
rotateForward x = C3.act C3.c1 x

rotateBackward : C3.C3 → C3.C3
rotateBackward x = C3.act C3.c2 x

c3RotationAutomorphism : Dynamics.FibreAutomorphism Orbit.orbitCore
c3RotationAutomorphism =
  Dynamics.fibreAutomorphism
    rotateForward
    rotateBackward
    (λ x → refl)
    (λ x → refl)
    backwardForward
    forwardBackward
  where
    backwardForward : ∀ x → rotateBackward (rotateForward x) ≡ x
    backwardForward C3.c0 = refl
    backwardForward C3.c1 = refl
    backwardForward C3.c2 = refl
    forwardBackward : ∀ x → rotateForward (rotateBackward x) ≡ x
    forwardBackward C3.c0 = refl
    forwardBackward C3.c1 = refl
    forwardBackward C3.c2 = refl

rotateC0ActuallyMoves : rotateForward C3.c0 ≡ C3.c0 → ⊥
rotateC0ActuallyMoves ()

c3RotationNontrivial : Dynamics.NontrivialFibreAutomorphism Orbit.orbitCore
c3RotationNontrivial =
  Dynamics.nontrivialFibreAutomorphism
    c3RotationAutomorphism C3.c0 rotateC0ActuallyMoves

c3RotationMustChangeReceipt :
  Orbit.orbitReceipt (rotateForward C3.c0) ≡ Orbit.orbitReceipt C3.c0 → ⊥
c3RotationMustChangeReceipt =
  ReceiptDynamics.nontrivialFibreAutomorphismChangesReceipt
    Orbit.c3OrbitProvenanceBearingQuotient
    c3RotationNontrivial
