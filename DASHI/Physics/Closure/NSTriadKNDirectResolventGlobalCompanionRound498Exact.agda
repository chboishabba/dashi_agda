module DASHI.Physics.Closure.NSTriadKNDirectResolventGlobalCompanionRound498Exact where

------------------------------------------------------------------------
-- ROUND498 / GLOBAL OUTPUT SUM OF THE DIRECT NONSEPARABLE COMPANION
--
-- R398 constructs the physical global pair list by concatenating one R397
-- output-pair list for every selected output.  R497 proves on each such fibre
-- that the literal weighted nonlinear remainder is exactly four times the
-- direct resolvent companion.  This file lifts that identity over the output
-- list using R398's exact remainder-append theorem.
--
-- No cross-output coherence estimate is needed: this is only finite additivity
-- of the already-literal pair list.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNFibreLocalR378GlobalInstantaneousGramFluxRound398Exact as R398
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNDirectResolventFibreCompanionRound497Exact as R497

F : C3.RealField _
F = Rational.rationalRealField

module DirectGlobal
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (P : R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H
      (DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit.velocityAt
        (Field30.finiteSystem physicalSystem))) where

  module Global = R398.GlobalFluxLocal physicalSystem S L H P
  module Fibre = R497.DirectFibre physicalSystem S

  globalDirectCompanion :
    (cutoff : Agda.Builtin.Nat.Nat) →
    (outputs : List Z3.FourierMode) →
    Global.OutputFibresPositiveOn cutoff outputs → ℚ
  globalDirectCompanion cutoff [] Global.positiveOutputsNil = 0ℚ
  globalDirectCompanion cutoff (output ∷ outputs)
      (Global.positiveOutputsCons headPositive tailPositive) =
    Fibre.directFibreCompanion
      (Output.physicalOutputFiber cutoff output) headPositive
    + globalDirectCompanion cutoff outputs tailPositive

  globalRemainderIsFourDirectCompanion :
    (cutoff : Agda.Builtin.Nat.Nat) →
    (outputs : List Z3.FourierMode) →
    (positive : Global.OutputFibresPositiveOn cutoff outputs) →
    R385.sumWeightedRemainder (Global.globalPairs cutoff outputs positive)
    ≡ R299.four * globalDirectCompanion cutoff outputs positive
  globalRemainderIsFourDirectCompanion cutoff [] Global.positiveOutputsNil =
    solve []
  globalRemainderIsFourDirectCompanion cutoff (output ∷ outputs)
      (Global.positiveOutputsCons headPositive tailPositive) =
    let
      fibre = Output.physicalOutputFiber cutoff output
      headPairs = Global.O.outputPairs cutoff output headPositive
      tailPairs = Global.globalPairs cutoff outputs tailPositive
      headCompanion = Fibre.directFibreCompanion fibre headPositive
      tailCompanion = globalDirectCompanion cutoff outputs tailPositive
    in
    trans
      (Global.remainderAppend headPairs tailPairs)
      (trans
        (cong₂ _+_
          (Fibre.allRemainderIsFourCompanion fibre headPositive)
          (globalRemainderIsFourDirectCompanion
            cutoff outputs tailPositive))
        (solve (headCompanion ∷ tailCompanion ∷ [])))

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

round498ExactOutputConcatenationReused : Bool
round498ExactOutputConcatenationReused = true

round498GlobalInstantaneousRemainderIsFourCompanionClosed : Bool
round498GlobalInstantaneousRemainderIsFourCompanionClosed = true

round498CrossOutputCoherenceEstimateRequired : Bool
round498CrossOutputCoherenceEstimateRequired = false

round498LaplaceRequired : Bool
round498LaplaceRequired = false

round498TrajectorySpecializationClosed : Bool
round498TrajectorySpecializationClosed = false

round498IntegratedCompanionWeldClosed : Bool
round498IntegratedCompanionWeldClosed = false

round498ClayPromotion : Bool
round498ClayPromotion = false

round498GlobalInstantaneousRemainderIsFourCompanionClosedIsTrue :
  round498GlobalInstantaneousRemainderIsFourCompanionClosed ≡ true
round498GlobalInstantaneousRemainderIsFourCompanionClosedIsTrue = refl

round498CrossOutputCoherenceEstimateRequiredIsFalse :
  round498CrossOutputCoherenceEstimateRequired ≡ false
round498CrossOutputCoherenceEstimateRequiredIsFalse = refl

round498ClayPromotionIsFalse : round498ClayPromotion ≡ false
round498ClayPromotionIsFalse = refl
