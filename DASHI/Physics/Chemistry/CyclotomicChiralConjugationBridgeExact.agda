module DASHI.Physics.Chemistry.CyclotomicChiralConjugationBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.CyclotomicPhaseAmplitudeBoundaryExact as C3
import DASHI.Physics.Chemistry.AsymmetricChiralDynamicsExact as Dynamics

------------------------------------------------------------------------
-- C3 CYCLOTOMIC CROSS-POLLINATION
--
-- The existing C3 phase owner has the exact involution
--   conjugate(zeta)=zeta^2, conjugate(zeta^2)=zeta.
-- Molecular handedness also carries a two-branch involution.  The lawful reuse
-- is therefore an intertwining of involutions, not an assertion that chemical
-- chirality literally is a cyclotomic phase.
------------------------------------------------------------------------

chiralPhase : Dynamics.ChiralBiasState → C3.C3Phase
chiralPhase Dynamics.leftAmplified = C3.phaseZeta
chiralPhase Dynamics.leftSeed = C3.phaseZeta
chiralPhase Dynamics.racemic = C3.phaseOne
chiralPhase Dynamics.rightSeed = C3.phaseZetaSquared
chiralPhase Dynamics.rightAmplified = C3.phaseZetaSquared

mirrorIsCyclotomicConjugation :
  (x : Dynamics.ChiralBiasState) →
  chiralPhase (Dynamics.mirrorBias x) ≡ C3.conjugatePhase (chiralPhase x)
mirrorIsCyclotomicConjugation Dynamics.leftAmplified = refl
mirrorIsCyclotomicConjugation Dynamics.leftSeed = refl
mirrorIsCyclotomicConjugation Dynamics.racemic = refl
mirrorIsCyclotomicConjugation Dynamics.rightSeed = refl
mirrorIsCyclotomicConjugation Dynamics.rightAmplified = refl

racemicMapsToConjugationFixedSector : chiralPhase Dynamics.racemic ≡ C3.phaseOne
racemicMapsToConjugationFixedSector = refl

leftAndRightMapToConjugateSectors :
  C3.conjugatePhase (chiralPhase Dynamics.leftSeed)
  ≡ chiralPhase Dynamics.rightSeed
leftAndRightMapToConjugateSectors = refl

------------------------------------------------------------------------
-- Dynamics and cyclotomic involution commute after projection.
------------------------------------------------------------------------

projectedStep : Dynamics.ChiralBiasState → C3.C3Phase
projectedStep x = chiralPhase (Dynamics.amplifyBias x)

projectedStepMirrorLaw :
  (x : Dynamics.ChiralBiasState) →
  projectedStep (Dynamics.mirrorBias x)
  ≡ C3.conjugatePhase (projectedStep x)
projectedStepMirrorLaw Dynamics.leftAmplified = refl
projectedStepMirrorLaw Dynamics.leftSeed = refl
projectedStepMirrorLaw Dynamics.racemic = refl
projectedStepMirrorLaw Dynamics.rightSeed = refl
projectedStepMirrorLaw Dynamics.rightAmplified = refl

record CyclotomicChiralConjugationBoundary : Set where
  constructor cyclotomicChiralConjugationBoundary
  field
    involutionIntertwinerPaid : Bool
    involutionIntertwinerPaidIsTrue : involutionIntertwinerPaid ≡ true

    racemicToFixedSectorPaid : Bool
    racemicToFixedSectorPaidIsTrue : racemicToFixedSectorPaid ≡ true

    molecularChiralityIsLiterallyCyclotomicPhase : Bool
    molecularChiralityIsLiterallyCyclotomicPhaseIsFalse :
      molecularChiralityIsLiterallyCyclotomicPhase ≡ false

    c3PhaseDeterminesChemicalKinetics : Bool
    c3PhaseDeterminesChemicalKineticsIsFalse :
      c3PhaseDeterminesChemicalKinetics ≡ false

    sharedInvolutionEstablishesPhysicalMechanismIdentity : Bool
    sharedInvolutionEstablishesPhysicalMechanismIdentityIsFalse :
      sharedInvolutionEstablishesPhysicalMechanismIdentity ≡ false

canonicalCyclotomicChiralConjugationBoundary : CyclotomicChiralConjugationBoundary
canonicalCyclotomicChiralConjugationBoundary =
  cyclotomicChiralConjugationBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
