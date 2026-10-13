module DASHI.Physics.Chemistry.Nobel2026SharedC3ActionWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.CyclotomicPhaseAmplitudeBoundaryExact as C3
import DASHI.Physics.Chemistry.AsymmetricChiralDynamicsExact as Dynamics
import DASHI.Physics.Chemistry.CyclotomicChiralConjugationBridgeExact as ChiralC3

------------------------------------------------------------------------
-- SHARED C3 ACTION / REFLECTION WELD
--
-- The existing cyclotomic owner already supplies the literal finite C3 action
-- `phaseAdvance` and reflection `conjugatePhase`.  The chemistry bridge already
-- supplies the molecular-mirror -> conjugation intertwiner.  Here we close the
-- action algebra itself: reflection reverses the C3 generator.
--
-- This is precisely the common representation-theoretic surface needed by
-- atomic/369 C3 realizations without importing their physical semantics.
------------------------------------------------------------------------

phaseRetreat : C3.C3Phase → C3.C3Phase
phaseRetreat p = C3.phaseAdvance (C3.phaseAdvance p)

advanceThenRetreat :
  (p : C3.C3Phase) → phaseRetreat (C3.phaseAdvance p) ≡ p
advanceThenRetreat C3.phaseOne = refl
advanceThenRetreat C3.phaseZeta = refl
advanceThenRetreat C3.phaseZetaSquared = refl

retreatThenAdvance :
  (p : C3.C3Phase) → C3.phaseAdvance (phaseRetreat p) ≡ p
retreatThenAdvance C3.phaseOne = refl
retreatThenAdvance C3.phaseZeta = refl
retreatThenAdvance C3.phaseZetaSquared = refl

-- Dihedral relation: reflection sends the +1 generator to its inverse.
conjugationReversesAdvance :
  (p : C3.C3Phase) →
  C3.conjugatePhase (C3.phaseAdvance p)
    ≡ phaseRetreat (C3.conjugatePhase p)
conjugationReversesAdvance C3.phaseOne = refl
conjugationReversesAdvance C3.phaseZeta = refl
conjugationReversesAdvance C3.phaseZetaSquared = refl

-- Same law, pulled back along the chemistry phase observer.
chiralMirrorReversesProjectedC3Action :
  (x : Dynamics.ChiralBiasState) →
  C3.conjugatePhase (C3.phaseAdvance (ChiralC3.chiralPhase x))
    ≡ phaseRetreat (ChiralC3.chiralPhase (Dynamics.mirrorBias x))
chiralMirrorReversesProjectedC3Action Dynamics.leftAmplified = refl
chiralMirrorReversesProjectedC3Action Dynamics.leftSeed = refl
chiralMirrorReversesProjectedC3Action Dynamics.racemic = refl
chiralMirrorReversesProjectedC3Action Dynamics.rightSeed = refl
chiralMirrorReversesProjectedC3Action Dynamics.rightAmplified = refl

record SharedC3ActionWeldBoundary : Set where
  constructor sharedC3ActionWeldBoundary
  field
    orderThreeActionOwned : Bool
    inverseActionOwned : Bool
    reflectionReversesGeneratorOwned : Bool
    molecularMirrorIntertwinerOwned : Bool
    actionSurfaceReusableByAtomicC3Representation : Bool
    sharedActionImpliesSharedPhysicalMechanism : Bool
    molecularChiralityIdentifiedWithMagneticQuantumNumber : Bool

canonicalSharedC3ActionWeldBoundary : SharedC3ActionWeldBoundary
canonicalSharedC3ActionWeldBoundary =
  sharedC3ActionWeldBoundary true true true true true false false
