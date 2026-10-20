module DASHI.Physics.Chemistry.Nobel2026SharedC3ActionWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.CyclotomicPhaseAmplitudeBoundaryExact as C3
import DASHI.Algebra.TriadicDepthOneCharacters as AtomicC3
import DASHI.Physics.Chemistry.AsymmetricChiralDynamicsExact as Dynamics
import DASHI.Physics.Chemistry.CyclotomicChiralConjugationBridgeExact as ChiralC3
import DASHI.Physics.Chemistry.Nobel2026CyclotomicCarrierEquivalenceExact as Carrier

------------------------------------------------------------------------
-- SHARED C3 ACTION / REFLECTION WELD
--
-- The existing cyclotomic owner supplies the finite C3 action and reflection.
-- The chemistry bridge supplies molecular mirror -> conjugation.  The carrier
-- equivalence now also identifies this +1 action with multiplication by the
-- repository's canonical atomic/Fourier generator phase1.  Thus the common
-- action is theorem-level, not a same-cardinality analogy.
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

conjugationReversesAdvance :
  (p : C3.C3Phase) →
  C3.conjugatePhase (C3.phaseAdvance p)
    ≡ phaseRetreat (C3.conjugatePhase p)
conjugationReversesAdvance C3.phaseOne = refl
conjugationReversesAdvance C3.phaseZeta = refl
conjugationReversesAdvance C3.phaseZetaSquared = refl

chiralMirrorReversesProjectedC3Action :
  (x : Dynamics.ChiralBiasState) →
  C3.conjugatePhase (C3.phaseAdvance (ChiralC3.chiralPhase x))
    ≡ phaseRetreat (ChiralC3.chiralPhase (Dynamics.mirrorBias x))
chiralMirrorReversesProjectedC3Action Dynamics.leftAmplified = refl
chiralMirrorReversesProjectedC3Action Dynamics.leftSeed = refl
chiralMirrorReversesProjectedC3Action Dynamics.racemic = refl
chiralMirrorReversesProjectedC3Action Dynamics.rightSeed = refl
chiralMirrorReversesProjectedC3Action Dynamics.rightAmplified = refl

------------------------------------------------------------------------
-- Atomic/Fourier generator recognition.
------------------------------------------------------------------------

advanceIsAtomicPositiveGenerator :
  (p : C3.C3Phase) →
  Carrier.chemToAtomic (C3.phaseAdvance p)
  ≡ AtomicC3.multiplyPhase AtomicC3.phase1 (Carrier.chemToAtomic p)
advanceIsAtomicPositiveGenerator = Carrier.chemAdvanceIsAtomicGeneratorAction

mirrorIsAtomicConjugation :
  (x : Dynamics.ChiralBiasState) →
  Carrier.chemToAtomic (ChiralC3.chiralPhase (Dynamics.mirrorBias x))
  ≡ AtomicC3.conjugatePhase
      (Carrier.chemToAtomic (ChiralC3.chiralPhase x))
mirrorIsAtomicConjugation Dynamics.leftAmplified = refl
mirrorIsAtomicConjugation Dynamics.leftSeed = refl
mirrorIsAtomicConjugation Dynamics.racemic = refl
mirrorIsAtomicConjugation Dynamics.rightSeed = refl
mirrorIsAtomicConjugation Dynamics.rightAmplified = refl

record SharedC3ActionWeldBoundary : Set where
  constructor sharedC3ActionWeldBoundary
  field
    orderThreeActionOwned : Bool
    inverseActionOwned : Bool
    reflectionReversesGeneratorOwned : Bool
    molecularMirrorIntertwinerOwned : Bool
    atomicFourierGeneratorActionRecognized : Bool
    actionSurfaceReusableByAtomicC3Representation : Bool
    sharedActionImpliesSharedPhysicalMechanism : Bool
    molecularChiralityIdentifiedWithMagneticQuantumNumber : Bool

canonicalSharedC3ActionWeldBoundary : SharedC3ActionWeldBoundary
canonicalSharedC3ActionWeldBoundary =
  sharedC3ActionWeldBoundary true true true true true true false false
