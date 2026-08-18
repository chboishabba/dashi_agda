module DASHI.Core.C3OrbitVerticalDynamicsExact where

------------------------------------------------------------------------
-- Exact finite witness for hidden dynamics on a reopenable quotient.
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", GTM 163, Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- The existing C3 orbit quotient sends all three phase points to one coarse
-- surface while retaining the point as the reopening receipt.  Rotation by c1
-- is therefore a canonical nontrivial vertical automorphism.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.C3OrbitProvenanceQuotientExact as Orbit
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Core.ProvenanceBearingQuotient as PBQ
import DASHI.Core.ProvenanceVerticalDynamicsExact as Vertical

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

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

rotationSurfaceInvariant :
  ∀ x →
  Orbit.orbitCore .DASHI.Core.FibreRestrictionCore.project (rotateForward x)
    ≡ Orbit.orbitCore .DASHI.Core.FibreRestrictionCore.project x
rotationSurfaceInvariant x = refl

c3OrbitVerticalAutomorphism : Vertical.FibreAutomorphism Orbit.orbitCore
c3OrbitVerticalAutomorphism =
  Vertical.fibreAutomorphism
    rotateForward
    rotateBackward
    rotateForwardBackward
    rotateBackwardForward
    rotationSurfaceInvariant

c1≢c0 : C3.c1 ≢ C3.c0
c1≢c0 ()

rotationMovesC0 : rotateForward C3.c0 ≢ C3.c0
rotationMovesC0 = c1≢c0

c3HiddenTransition :
  Vertical.HiddenVerticalTransition
    Orbit.orbitCore
    (Vertical.automorphismAsVerticalOperator c3OrbitVerticalAutomorphism)
c3HiddenTransition =
  Vertical.hiddenVerticalTransition C3.c0 rotationMovesC0

rotationMustChangeOrbitReceipt :
  PBQ.receipt Orbit.c3OrbitProvenanceBearingQuotient (rotateForward C3.c0)
    ≢ PBQ.receipt Orbit.c3OrbitProvenanceBearingQuotient C3.c0
rotationMustChangeOrbitReceipt =
  Vertical.nontrivialAutomorphismChangesReceipt
    Orbit.c3OrbitProvenanceBearingQuotient
    c3OrbitVerticalAutomorphism
    C3.c0
    rotationMovesC0
