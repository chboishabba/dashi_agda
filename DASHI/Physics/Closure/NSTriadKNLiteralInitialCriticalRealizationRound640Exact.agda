{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNLiteralInitialCriticalRealizationRound640Exact where

------------------------------------------------------------------------
-- ROUND638 / COMMON INITIAL DATUM -> CANONICAL R637 INITIAL CRITICAL SLICE
--
-- R240 owns one common initial Fourier datum and equality with the initial
-- Galerkin velocity on every mode satisfying Audit.modeListed.
--
-- The finite-system record also stores the explicit mode list, but its current
-- abstract interface does not itself state
--
--   mode ∈ Audit.modes  ->  Audit.modeListed mode.
--
-- This owner isolates exactly that representation receipt.  Once supplied, the
-- R637 canonical slice's initial critical coordinate is definitionally the
-- dyadic critical mass of the common R240 initial datum on the same cutoff
-- list.  The only remaining initial-data analysis is one cutoff-independent
-- ceiling for that explicit functional.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical34
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCriticalSliceRound639Exact as R639
import DASHI.Physics.Closure.NSTriadKNInitialCriticalRealizationToR421Round512Exact as R512
import DASHI.Physics.Closure.NSTriadKNCanonicalModeListedCoherenceRound643Exact as R643

F : C3.RealField _
F = Rational.rationalRealField

canonicalR34ModeListedFromMembership :
  ∀ {r} {F' : C3.RealField r} {E : C3.IntegerEmbedding F'}
    {state : State.ReconstructedPhysicalState F' E}
    (datum : Canonical34.CutoffSameObjectDatum F' E state)
    (mode : Z3.FourierMode) →
  mode Cube.∈ Audit.modes (Canonical34.canonicalAuditFiniteSystem datum) →
  Audit.modeListed (Canonical34.canonicalAuditFiniteSystem datum) mode
canonicalR34ModeListedFromMembership datum mode member = member

weightedInitialDatumMass :
  (Z3.FourierMode → C3.Complex3 F) →
  List Z3.FourierMode →
  ℚ
weightedInitialDatumMass initial [] = 0ℚ
weightedInitialDatumMass initial (mode ∷ rest) =
  Fold.dyadicCriticalWeight mode
    * L2.complex3NormSquared (initial mode)
    + weightedInitialDatumMass initial rest

module InitialCritical
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus Time DerivativeOf ScalarDerivativeOf)
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo) where

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Modes = ModeCarrier.LiteralModeCarrier
    Time initialTime integrateTo DerivativeOf
  module Obs = Fold.LiteralCriticalObservables
    Time initialTime integrateTo DerivativeOf
  module Physical = R639.PhysicalSlice
    Time initialTime integrateTo DerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity
  module Initial = R512.InitialCritical
    Time initialTime integrateTo DerivativeOf

  record ModeListedCoherence
      (D : Live.LiteralRHSTrajectoryData) : Set where
    field
      listedFromModeMembership :
        (cutoff : Nat) (mode : Z3.FourierMode) →
        mode Cube.∈ Audit.modes
          (Live.Base.systemAt
            (Live.stateTrajectory (Live.support D)) cutoff initialTime) →
        Audit.modeListed
          (Live.Base.systemAt
            (Live.stateTrajectory (Live.support D)) cutoff initialTime)
          mode

  open ModeListedCoherence public

  initialMassSameObjectOnList :
    (D : Live.LiteralRHSTrajectoryData) →
    (coherence : ModeListedCoherence D) →
    (cutoff : Nat) →
    (modes : List Z3.FourierMode) →
    ((mode : Z3.FourierMode) →
      mode Cube.∈ modes →
      mode Cube.∈ Audit.modes
        (Live.Base.systemAt
          (Live.stateTrajectory (Live.support D)) cutoff initialTime)) →
    Fold.weightedVelocityMass
      Fold.dyadicCriticalWeight
      (Live.Base.systemAt
        (Live.stateTrajectory (Live.support D)) cutoff initialTime)
      modes
    ≡ weightedInitialDatumMass (Live.initialVelocity (Live.support D)) modes
  initialMassSameObjectOnList D coherence cutoff [] include = refl
  initialMassSameObjectOnList D coherence cutoff (mode ∷ rest) include =
    trans
      (cong
        (λ selected →
          Fold.dyadicCriticalWeight mode
            * L2.complex3NormSquared selected
            + Fold.weightedVelocityMass
                Fold.dyadicCriticalWeight
                (Live.Base.systemAt
                  (Live.stateTrajectory (Live.support D))
                  cutoff initialTime)
                rest)
        (Live.initialVelocityAgreement
          (Live.support D) cutoff mode
          (listedFromModeMembership coherence cutoff mode
            (include mode (Cube.here refl)))))
      (cong
        (Fold.dyadicCriticalWeight mode
          * L2.complex3NormSquared
              (Live.initialVelocity (Live.support D) mode) +_)
        (initialMassSameObjectOnList
          D coherence cutoff rest
          (λ selected member → include selected (Cube.there member))))

  initialDatumCritical :
    (D : Live.LiteralRHSTrajectoryData) →
    Nat → ℚ
  initialDatumCritical D cutoff =
    weightedInitialDatumMass
      (Live.initialVelocity (Live.support D))
      (Audit.modes
        (Live.Base.systemAt
          (Live.stateTrajectory (Live.support D)) cutoff initialTime))

  initialCriticalSameObject :
    (D : Live.LiteralRHSTrajectoryData) →
    (coherence : ModeListedCoherence D) →
    (cutoff : Nat) →
    Obs.criticalEnergyAt
      (Live.literalPhysicalTrajectory D) cutoff initialTime
    ≡ initialDatumCritical D cutoff
  initialCriticalSameObject D coherence cutoff =
    initialMassSameObjectOnList
      D coherence cutoff
      (Audit.modes
        (Live.Base.systemAt
          (Live.stateTrajectory (Live.support D)) cutoff initialTime))
      (λ mode member → member)

  record InitialCriticalCeiling
      (D : Live.LiteralRHSTrajectoryData) : Set where
    field
      cutoffIndependentInitialCeiling : ℚ
      initialDatumCriticalBound :
        (cutoff : Nat) →
        initialDatumCritical D cutoff ≤ cutoffIndependentInitialCeiling

  open InitialCriticalCeiling public

  buildR512InitialRealization :
    ∀ {D C R terminal}
      (sliceData :
        (cutoff : Nat) →
        Physical.PhysicalCriticalSliceData D C R cutoff terminal) →
      (coherence : ModeListedCoherence D) →
      (ceiling : InitialCriticalCeiling D) →
    Initial.InitialCriticalRealization
      (Live.literalPhysicalTrajectory D) R terminal
      (λ cutoff →
        Physical.canonicalPhysicalCriticalSlice (sliceData cutoff))
  buildR512InitialRealization {D} {C} {R} {terminal}
      sliceData coherence ceiling =
    record
      { Initial.initialDatumCritical = initialDatumCritical D
      ; Initial.initialCriticalSameObject =
          initialCriticalSameObject D coherence
      ; Initial.cutoffIndependentInitialCeiling =
          cutoffIndependentInitialCeiling ceiling
      ; Initial.initialDatumCriticalBound =
          initialDatumCriticalBound ceiling
      }

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round640CommonInitialDatumSameObjectCompilerClosed : Bool
round640CommonInitialDatumSameObjectCompilerClosed = true

round640CanonicalR34ModeListCoherenceClosed : Bool
round640CanonicalR34ModeListCoherenceClosed = true

round640LiveTrajectoryToCanonicalR34AttachmentStillRequired : Bool
round640LiveTrajectoryToCanonicalR34AttachmentStillRequired = true

round640ModeListToModeListedCoherenceStillRequired : Bool
round640ModeListToModeListedCoherenceStillRequired = true

-- For an arbitrary audit trajectory the predicate/list relation remains a
-- receipt because Audit deliberately keeps them independent.  The actual R34
-- canonical constructor now has the exact definitional compiler in R643.
round640CanonicalR34ModeListCoherenceCompilerAvailable : Bool
round640CanonicalR34ModeListCoherenceCompilerAvailable =
  R643.canonicalR34PaysR640ModeCoherenceWithoutEstimate

round640CutoffUniformInitialCeilingStillProofBearing : Bool
round640CutoffUniformInitialCeilingStillProofBearing = true

round640InitialCriticalAliasFreedomRemoved : Bool
round640InitialCriticalAliasFreedomRemoved = true

round640IntroducesNewNSEstimate : Bool
round640IntroducesNewNSEstimate = false

round640ClayPromotion : Bool
round640ClayPromotion = false

round640CommonInitialDatumSameObjectCompilerClosedIsTrue :
  round640CommonInitialDatumSameObjectCompilerClosed ≡ true
round640CommonInitialDatumSameObjectCompilerClosedIsTrue = refl

round640CanonicalR34ModeListCoherenceClosedIsTrue :
  round640CanonicalR34ModeListCoherenceClosed ≡ true
round640CanonicalR34ModeListCoherenceClosedIsTrue = refl

round640LiveTrajectoryToCanonicalR34AttachmentStillRequiredIsTrue :
  round640LiveTrajectoryToCanonicalR34AttachmentStillRequired ≡ true
round640LiveTrajectoryToCanonicalR34AttachmentStillRequiredIsTrue = refl

round640ModeListToModeListedCoherenceStillRequiredIsTrue :
  round640ModeListToModeListedCoherenceStillRequired ≡ true
round640ModeListToModeListedCoherenceStillRequiredIsTrue = refl

round640CanonicalR34ModeListCoherenceCompilerAvailableIsTrue :
  round640CanonicalR34ModeListCoherenceCompilerAvailable ≡ true
round640CanonicalR34ModeListCoherenceCompilerAvailableIsTrue =
  R643.canonicalR34PaysR640ModeCoherenceWithoutEstimateIsTrue

round640CutoffUniformInitialCeilingStillProofBearingIsTrue :
  round640CutoffUniformInitialCeilingStillProofBearing ≡ true
round640CutoffUniformInitialCeilingStillProofBearingIsTrue = refl

round640InitialCriticalAliasFreedomRemovedIsTrue :
  round640InitialCriticalAliasFreedomRemoved ≡ true
round640InitialCriticalAliasFreedomRemovedIsTrue = refl

round640IntroducesNewNSEstimateIsFalse :
  round640IntroducesNewNSEstimate ≡ false
round640IntroducesNewNSEstimateIsFalse = refl

round640ClayPromotionIsFalse :
  round640ClayPromotion ≡ false
round640ClayPromotionIsFalse = refl
