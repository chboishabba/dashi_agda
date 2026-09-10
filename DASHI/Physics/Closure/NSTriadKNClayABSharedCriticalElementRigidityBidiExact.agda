module DASHI.Physics.Closure.NSTriadKNClayABSharedCriticalElementRigidityBidiExact where

------------------------------------------------------------------------
-- CLAY A/B SHARED CRITICAL-ELEMENT RIGIDITY BIDI
--
-- PURPOSE
-- -------
-- Reuse the existing pre-release R255/R257/R260/R261/R262 architecture without
-- identifying the Euclidean and periodic Clay alternatives.
--
-- The domain-specific producer side differs:
--
--   A / R^3:
--     Euclidean critical profile / concentration production
--       -> nonlinear mixed-defect decoupling
--       -> compact critical element.
--
--   B / T^3:
--     periodic H^(1/2) bounded sequence
--       -> scale-one periodic weak profile
--          OR shrinking Euclidean bubbles
--       -> nonlinear mixed-defect decoupling
--       -> compact critical element.
--
-- Once a compact nontrivial critical element on the appropriate physical
-- carrier has been produced, both alternatives use the SAME theorem-shaped
-- rigidity consumer:
--
--   compactness modulo NS symmetry
--   + terminal vorticity vanishing/decay
--   + ESS parabolic/backward-uniqueness hypotheses
--   -> zero vorticity
--   -> trivial velocity
--   -> contradiction with the nonzero mixed-defect obstruction.
--
-- R257 owns the logical contradiction compiler. R262 identifies the published
-- ESS/GKP PDE content. R260/R261 identify the profile/mixed-defect source
-- content. None of those analytic source records is silently promoted into a
-- finite-Agda proof of its own Set-valued PDE fields.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNTorusEuclideanProfileDichotomyRound255Exact as R255
import DASHI.Physics.Closure.NSTriadKNCriticalElementBackwardUniquenessRound257Exact as R257
import DASHI.Physics.Closure.NSTriadKNPeriodicFractionalProfileSourceRound260Exact as R260
import DASHI.Physics.Closure.NSTriadKNNonlinearProfileMixedDefectSourceRound261Exact as R261
import DASHI.Physics.Closure.NSTriadKNCriticalElementRigiditySourceRound262Exact as R262
import DASHI.Physics.Closure.NSClayFourAlternativeReleasedProofBidiExact as Clay4

------------------------------------------------------------------------
-- 1. Keep A and B constructor-distinct.
------------------------------------------------------------------------

data UnforcedABAlternative : Set where
  euclideanA : UnforcedABAlternative
  periodicB : UnforcedABAlternative

data ABProfileGeometry : Set where
  euclideanProfileGeometry : ABProfileGeometry
  periodicScaleOnePlusEuclideanBubbleGeometry : ABProfileGeometry

profileGeometry : UnforcedABAlternative → ABProfileGeometry
profileGeometry euclideanA = euclideanProfileGeometry
profileGeometry periodicB = periodicScaleOnePlusEuclideanBubbleGeometry

mapsToClayAlternative : UnforcedABAlternative → Clay4.ClayAlternative4
mapsToClayAlternative euclideanA = Clay4.A-euclidean-unforced-global
mapsToClayAlternative periodicB = Clay4.B-periodic-unforced-global

------------------------------------------------------------------------
-- 2. The rigidity consumer is deliberately domain-agnostic at theorem shape.
------------------------------------------------------------------------

SharedRigidityConsumer :
  ∀ {ℓ : Level} → Set ℓ → Set _
SharedRigidityConsumer CriticalElement =
  R257.CriticalElementRigidityAuthority CriticalElement

sharedRigidityContradiction :
  ∀ {ℓ : Level} {CriticalElement : Set ℓ} →
  SharedRigidityConsumer CriticalElement → ⊥
sharedRigidityContradiction = R257.criticalElementImpossible

------------------------------------------------------------------------
-- 3. Periodic producer keeps the scale-one / shrinking-bubble dichotomy.
------------------------------------------------------------------------

record PeriodicProfileProducer
    {ℓ : Level}
    (TorusState EuclideanState : Set ℓ) : Set (Level.suc ℓ) where
  field
    dichotomy : R255.TorusToProfileCarrier TorusState EuclideanState
    fractionalProfile :
      R260.PeriodicFractionalProfileTheorem TorusState EuclideanState

open PeriodicProfileProducer public

record SharedMixedDefectProducer
    {ℓ : Level} (Profile : Set ℓ) : Set (Level.suc ℓ) where
  field
    nonlinearProfileTheorem : R261.NonlinearMixedDefectProfileTheorem Profile

open SharedMixedDefectProducer public

------------------------------------------------------------------------
-- 4. Source-exact rigidity payload remains distinct from its inhabitation.
------------------------------------------------------------------------

record RigiditySourceRealization
    {ℓ : Level} (CriticalElement : Set ℓ) : Set (Level.suc ℓ) where
  field
    publishedRigidityPayload : R262.ESSCriticalElementRigidity CriticalElement
    executableRigidityConsumer : SharedRigidityConsumer CriticalElement

open RigiditySourceRealization public

realizedRigidityContradictsCriticalElement :
  ∀ {ℓ : Level} {CriticalElement : Set ℓ} →
  RigiditySourceRealization CriticalElement → ⊥
realizedRigidityContradictsCriticalElement R =
  sharedRigidityContradiction (executableRigidityConsumer R)

------------------------------------------------------------------------
-- 5. BIDI/WrongType firewalls.
------------------------------------------------------------------------

data PeriodicProofAutomaticallyIsEuclideanProof : Set where
data EuclideanProofAutomaticallyIsPeriodicProof : Set where
data SharedRigidityConsumerImpliesSharedProfileProducer : Set where
data SourceExactRigidityRecordImpliesFiniteKernelDerivation : Set where

data PeriodicBubbleBranchEliminatesScaleOneBranch : Set where

periodicDoesNotAutomaticallyPayEuclidean :
  PeriodicProofAutomaticallyIsEuclideanProof → ⊥
periodicDoesNotAutomaticallyPayEuclidean ()

euclideanDoesNotAutomaticallyPayPeriodic :
  EuclideanProofAutomaticallyIsPeriodicProof → ⊥
euclideanDoesNotAutomaticallyPayPeriodic ()

sharedRigidityDoesNotCreateSharedProfileProducer :
  SharedRigidityConsumerImpliesSharedProfileProducer → ⊥
sharedRigidityDoesNotCreateSharedProfileProducer ()

sourceRecordDoesNotCreateKernelDerivation :
  SourceExactRigidityRecordImpliesFiniteKernelDerivation → ⊥
sourceRecordDoesNotCreateKernelDerivation ()

shrinkingBubblesDoNotErasePeriodicScaleOneBranch :
  PeriodicBubbleBranchEliminatesScaleOneBranch → ⊥
shrinkingBubblesDoNotErasePeriodicScaleOneBranch ()

------------------------------------------------------------------------
-- 6. Introspective cut.
------------------------------------------------------------------------

data ABSharedResidual : Set where
  realizeDomainSpecificCriticalProfile : ABSharedResidual
  realizeMixedDefectAsymptoticAdditivity : ABSharedResidual
  realizeESSRigidityOnSameCriticalElement : ABSharedResidual
  dischargeSharedRigidityContradiction : ABSharedResidual
  abRigidityLaneComplete : ABSharedResidual

firstSharedABResidual : ABSharedResidual
firstSharedABResidual = realizeDomainSpecificCriticalProfile

sharedABRigidityConsumerIdentified : Bool
sharedABRigidityConsumerIdentified = true

periodicAndEuclideanProfileProducersIdentified : Bool
periodicAndEuclideanProfileProducersIdentified = false

periodicScaleOneBranchPreserved : Bool
periodicScaleOneBranchPreserved =
  R255.round255ScaleOnePeriodicBranchPreserved

sharedMixedDefectSourceTheoremIdentified : Bool
sharedMixedDefectSourceTheoremIdentified =
  R261.round261MixedDefectAsymptoticAdditivitySourceDerived

sharedESSRigiditySourceTheoremIdentified : Bool
sharedESSRigiditySourceTheoremIdentified =
  R262.round262ESSBackwardUniquenessIsExactRigidityLeaf

sharedESSRigidityKernelDerivedInFiniteAgda : Bool
sharedESSRigidityKernelDerivedInFiniteAgda =
  R262.round262ESSAnalyticTheoremKernelDerivedInFiniteAgda

clayAInternallyPaidHere : Bool
clayAInternallyPaidHere = false

clayBInternallyPaidHere : Bool
clayBInternallyPaidHere = false

sharedABRigidityConsumerIdentifiedIsTrue :
  sharedABRigidityConsumerIdentified ≡ true
sharedABRigidityConsumerIdentifiedIsTrue = refl

periodicAndEuclideanProfileProducersIdentifiedIsFalse :
  periodicAndEuclideanProfileProducersIdentified ≡ false
periodicAndEuclideanProfileProducersIdentifiedIsFalse = refl

clayAInternallyPaidHereIsFalse : clayAInternallyPaidHere ≡ false
clayAInternallyPaidHereIsFalse = refl

clayBInternallyPaidHereIsFalse : clayBInternallyPaidHere ≡ false
clayBInternallyPaidHereIsFalse = refl
