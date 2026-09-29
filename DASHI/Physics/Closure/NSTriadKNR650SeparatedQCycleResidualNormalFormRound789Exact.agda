{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedQCycleResidualNormalFormRound789Exact where

------------------------------------------------------------------------
-- ROUND789 / EXPAND THE THREE-PROFILE q-CYCLE THROUGH THE ACTUAL R760 RESIDUAL
--
-- R788 gives
--
--   sum CycleD = 3 * FullySeparatedD,
--
-- where CycleD samples beta, q beta and q^2 beta.
--
-- R760 gives pointwise
--
--   PairD(gamma)
--     = 3 [N(gamma)+N(swap gamma)] - 2 Pdyad(gamma).
--
-- Because R787 proves the mask is q-invariant, the complete separated cycle
-- therefore has the exact local normal form
--
--   CycleD
--     = 3 * CycleNestedPair - 2 * CycleDyadicProduction
--
-- on the separated family, and is exactly zero on the ccTouched family.
--
-- Folding gives the precise remaining algebraic object:
--
--   3 FullySeparatedD
--     = 3 CycleNestedFold - 2 CycleDyadicProductionFold.
--
-- No estimate, norm, absolute value, or sign is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNR650CCTouchedQInvariantRound787Exact as R787
import DASHI.Physics.Closure.NSTriadKNR650FullySeparatedQOrbitAverageRound788Exact as R788

F : C3.RealField _
F = Rational.rationalRealField

module CycleResidualNormalForm
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra :
      R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (zeroCalculus :
      Endpoint.VectorZeroDerivative Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf)
    (C :
      ModeCarrier.LiteralModeCarrier.LiteralCutoffModeCarrier
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D))
    (R :
      R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D)) where

  module Average = R788.QOrbitAverage
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Average.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module A = Average.At cutoff time S
    module P = A.T.T.P

    items : List Physical.PhysicalTriadIncidence
    items = A.items

    q1 : Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence
    q1 = Orbit.qEnergyLeg

    q2 : Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence
    q2 beta = Orbit.qEnergyLeg (Orbit.qEnergyLeg beta)

    nestedPair :
      Physical.PhysicalTriadIncidence → ℚ
    nestedPair beta =
      P.Base.Base.nestedOrbitCell beta
        + P.Base.Base.nestedOrbitCell (Symmetry.swapTriad beta)

    cycleNestedPair :
      Physical.PhysicalTriadIncidence → ℚ
    cycleNestedPair beta =
      nestedPair beta + nestedPair (q1 beta) + nestedPair (q2 beta)

    cycleDyadicProduction :
      Physical.PhysicalTriadIncidence → ℚ
    cycleDyadicProduction beta =
      P.Base.pairedTwoDifferenceCell beta
        + P.Base.pairedTwoDifferenceCell (q1 beta)
        + P.Base.pairedTwoDifferenceCell (q2 beta)

    maskedCycleNestedPair :
      Physical.PhysicalTriadIncidence → ℚ
    maskedCycleNestedPair beta with R781.ccTouched beta
    ... | true = 0ℚ
    ... | false = cycleNestedPair beta

    maskedCycleDyadicProduction :
      Physical.PhysicalTriadIncidence → ℚ
    maskedCycleDyadicProduction beta with R781.ccTouched beta
    ... | true = 0ℚ
    ... | false = cycleDyadicProduction beta

    q1Mask :
      (beta : Physical.PhysicalTriadIncidence) →
      R781.ccTouched (q1 beta) ≡ R781.ccTouched beta
    q1Mask = R787.ccTouchedQInvariant

    q2Mask :
      (beta : Physical.PhysicalTriadIncidence) →
      R781.ccTouched (q2 beta) ≡ R781.ccTouched beta
    q2Mask beta =
      trans
        (R787.ccTouchedQInvariant (q1 beta))
        (R787.ccTouchedQInvariant beta)

    separatedCycleNormalForm :
      (beta : Physical.PhysicalTriadIncidence) →
      R781.ccTouched beta ≡ false →
      A.cycleCell beta
      ≡
      R744.three * cycleNestedPair beta
        - Fold.two * cycleDyadicProduction beta
    separatedCycleNormalForm beta separated
      rewrite q1Mask beta
            | q2Mask beta
            | separated
            | P.swapPairedResidualNormalForm beta
            | P.swapPairedResidualNormalForm (q1 beta)
            | P.swapPairedResidualNormalForm (q2 beta) =
      solve
        ( R744.three
        ∷ Fold.two
        ∷ nestedPair beta
        ∷ nestedPair (q1 beta)
        ∷ nestedPair (q2 beta)
        ∷ P.Base.pairedTwoDifferenceCell beta
        ∷ P.Base.pairedTwoDifferenceCell (q1 beta)
        ∷ P.Base.pairedTwoDifferenceCell (q2 beta)
        ∷ [])

    touchedCycleZero :
      (beta : Physical.PhysicalTriadIncidence) →
      R781.ccTouched beta ≡ true →
      A.cycleCell beta ≡ 0ℚ
    touchedCycleZero beta touched
      rewrite q1Mask beta
            | q2Mask beta
            | touched =
      refl

    cycleCellNormalForm :
      (beta : Physical.PhysicalTriadIncidence) →
      A.cycleCell beta
      ≡
      R744.three * maskedCycleNestedPair beta
        - Fold.two * maskedCycleDyadicProduction beta
    cycleCellNormalForm beta
      with R781.ccTouched beta in touched
    ... | false =
      separatedCycleNormalForm beta touched
    ... | true =
      trans
        (touchedCycleZero beta touched)
        (sym (solve (R744.three ∷ Fold.two ∷ [])))

    maskedNestedFold : ℚ
    maskedNestedFold =
      R38.foldPower maskedCycleNestedPair items

    maskedProductionFold : ℚ
    maskedProductionFold =
      R38.foldPower maskedCycleDyadicProduction items

    cycleFoldNormalForm :
      A.cycleFold
      ≡
      R744.three * maskedNestedFold
        - Fold.two * maskedProductionFold
    cycleFoldNormalForm =
      go items
      where
      go :
        (xs : List Physical.PhysicalTriadIncidence) →
        R38.foldPower A.cycleCell xs
        ≡
        R744.three * R38.foldPower maskedCycleNestedPair xs
          - Fold.two * R38.foldPower maskedCycleDyadicProduction xs
      go [] = solve []
      go (beta ∷ rest) =
        trans
          (cong (A.cycleCell beta +_) (go rest))
          (trans
            (cong
              (λ selected →
                selected
                  + (R744.three *
                      R38.foldPower maskedCycleNestedPair rest
                    - Fold.two *
                      R38.foldPower maskedCycleDyadicProduction rest))
              (cycleCellNormalForm beta))
            (solve
              ( R744.three
              ∷ Fold.two
              ∷ maskedCycleNestedPair beta
              ∷ maskedCycleDyadicProduction beta
              ∷ R38.foldPower maskedCycleNestedPair rest
              ∷ R38.foldPower maskedCycleDyadicProduction rest
              ∷ [])))

    threeSeparatedFoldNormalForm :
      R744.three * A.T.T.fullySeparatedFold
      ≡
      R744.three * maskedNestedFold
        - Fold.two * maskedProductionFold
    threeSeparatedFoldNormalForm =
      trans
        (sym A.cycleFoldIsThreeSeparatedFold)
        cycleFoldNormalForm

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round789SeparatedCycleExpandedThroughR760 : Bool
round789SeparatedCycleExpandedThroughR760 = true

round789ThreeSeparatedFoldHasCycleNestedMinusProductionForm : Bool
round789ThreeSeparatedFoldHasCycleNestedMinusProductionForm = true

round789IntroducesEstimate : Bool
round789IntroducesEstimate = false

round789CycleNestedPaidByCycleProduction : Bool
round789CycleNestedPaidByCycleProduction = false

round789W2Closed : Bool
round789W2Closed = false

round789ClayPromotion : Bool
round789ClayPromotion = false

round789SeparatedCycleExpandedThroughR760IsTrue :
  round789SeparatedCycleExpandedThroughR760 ≡ true
round789SeparatedCycleExpandedThroughR760IsTrue = refl

round789ThreeSeparatedFoldHasCycleNestedMinusProductionFormIsTrue :
  round789ThreeSeparatedFoldHasCycleNestedMinusProductionForm ≡ true
round789ThreeSeparatedFoldHasCycleNestedMinusProductionFormIsTrue = refl

round789IntroducesEstimateIsFalse :
  round789IntroducesEstimate ≡ false
round789IntroducesEstimateIsFalse = refl

round789CycleNestedPaidByCycleProductionIsFalse :
  round789CycleNestedPaidByCycleProduction ≡ false
round789CycleNestedPaidByCycleProductionIsFalse = refl

round789W2ClosedIsFalse :
  round789W2Closed ≡ false
round789W2ClosedIsFalse = refl

round789ClayPromotionIsFalse :
  round789ClayPromotion ≡ false
round789ClayPromotionIsFalse = refl
