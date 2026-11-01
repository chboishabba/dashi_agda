{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedResidualFactorTwentySevenRound793Exact where

------------------------------------------------------------------------
-- ROUND793 / WELD THE FACTOR-NINE NESTED CYCLE BACK TO THE LIVE W2 RESIDUAL
--
-- R789:
--
--   3 * FullySeparatedD
--     = 3 * MaskedNestedCycle - 2 * MaskedDyadicProductionCycle.
--
-- R792:
--
--   MaskedNestedCycle = 9 * SeparatedPairedBaseProductRule.
--
-- The nested objects are literally the same R700 nestedTriadOrbitResidue
-- instantiated through the live R745/R760 trajectory stack.  Therefore:
--
--   3 * FullySeparatedD
--     = 27 * SeparatedPairedBaseProductRule
--       - 2 * MaskedDyadicProductionCycle.
--
-- This is the sharpest exact separated-family scalar produced so far.  Any
-- further progress must compare/pay the dyadic production cycle against the
-- retained signed paired base product-rule fold (or extract additional exact
-- cancellation from those two same-family carriers).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
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
import DASHI.Physics.Closure.NSTriadKNR650SeparatedQCycleResidualNormalFormRound789Exact as R789
import DASHI.Physics.Closure.NSTriadKNR650SeparatedNestedQCycleFactorNineRound792Exact as R792

F : C3.RealField _
F = Rational.rationalRealField

twentySeven : ℚ
twentySeven = 27

module SeparatedFactorTwentySeven
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

  module Residual = R789.CycleResidualNormalForm
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Residual.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module X = Residual.At cutoff time S
    module P = X.P

    module Cycle = R792.SeparatedNestedQCycle
      P.Base.Base.NestedAt.physicalSystem
      Residual.Average.Three.Two.Paired.Local.O.Combined.Nested.S
      Residual.Average.Three.Two.Paired.Local.O.Combined.Nested.L
      Residual.Average.Three.Two.Paired.Local.O.Combined.Nested.H
      P.Base.Base.NestedAt.allModeTransverse

    items : List Physical.PhysicalTriadIncidence
    items = X.items

    maskedNestedCycleSameObject :
      (beta : Physical.PhysicalTriadIncidence) →
      X.maskedCycleNestedPair beta ≡ Cycle.cycleCell beta
    maskedNestedCycleSameObject beta
      rewrite R787.ccTouchedQInvariant beta
            | R787.ccTouchedQInvariant (Orbit.qEnergyLeg beta)
      with R781.ccTouched beta
    ... | true = refl
    ... | false = refl

    maskedNestedFoldIsCycleFold :
      X.maskedNestedFold ≡ Cycle.cycleFold
    maskedNestedFoldIsCycleFold =
      go items
      where
      go :
        (xs : List Physical.PhysicalTriadIncidence) →
        R38.foldPower X.maskedCycleNestedPair xs
        ≡ R38.foldPower Cycle.cycleCell xs
      go [] = refl
      go (beta ∷ rest) =
        cong₂ _+_
          (maskedNestedCycleSameObject beta)
          (go rest)

    maskedNestedFoldIsNinePairedBase :
      X.maskedNestedFold
      ≡ R792.nine *
          R38.foldPower Cycle.Sep.maskedPairedBaseRow items
    maskedNestedFoldIsNinePairedBase =
      trans
        maskedNestedFoldIsCycleFold
        Cycle.cycleFoldIsNinePairedBase

    separatedResidualFactorTwentySeven :
      R744.three * X.A.T.T.fullySeparatedFold
      ≡
      twentySeven *
        R38.foldPower Cycle.Sep.maskedPairedBaseRow items
        - Fold.two * X.maskedProductionFold
    separatedResidualFactorTwentySeven =
      trans
        X.threeSeparatedFoldNormalForm
        (trans
          (cong
            (λ nested →
              R744.three * nested
                - Fold.two * X.maskedProductionFold)
            maskedNestedFoldIsNinePairedBase)
          (solve
            ( R744.three
            ∷ R792.nine
            ∷ twentySeven
            ∷ R38.foldPower Cycle.Sep.maskedPairedBaseRow items
            ∷ Fold.two
            ∷ X.maskedProductionFold
            ∷ [])))

round793SeparatedResidualFactorTwentySevenClosed : Bool
round793SeparatedResidualFactorTwentySevenClosed = true

round793NestedCycleSameObjectWeldClosed : Bool
round793NestedCycleSameObjectWeldClosed = true

round793IntroducesEstimate : Bool
round793IntroducesEstimate = false

round793DyadicProductionCyclePaid : Bool
round793DyadicProductionCyclePaid = false

round793W2Closed : Bool
round793W2Closed = false

round793ClayPromotion : Bool
round793ClayPromotion = false

round793SeparatedResidualFactorTwentySevenClosedIsTrue :
  round793SeparatedResidualFactorTwentySevenClosed ≡ true
round793SeparatedResidualFactorTwentySevenClosedIsTrue = refl

round793NestedCycleSameObjectWeldClosedIsTrue :
  round793NestedCycleSameObjectWeldClosed ≡ true
round793NestedCycleSameObjectWeldClosedIsTrue = refl

round793IntroducesEstimateIsFalse :
  round793IntroducesEstimate ≡ false
round793IntroducesEstimateIsFalse = refl

round793DyadicProductionCyclePaidIsFalse :
  round793DyadicProductionCyclePaid ≡ false
round793DyadicProductionCyclePaidIsFalse = refl

round793W2ClosedIsFalse :
  round793W2Closed ≡ false
round793W2ClosedIsFalse = refl

round793ClayPromotionIsFalse :
  round793ClayPromotion ≡ false
round793ClayPromotionIsFalse = refl
