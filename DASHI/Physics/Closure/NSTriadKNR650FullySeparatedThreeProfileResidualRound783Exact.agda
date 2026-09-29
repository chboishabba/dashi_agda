{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650FullySeparatedThreeProfileResidualRound783Exact where

------------------------------------------------------------------------
-- ROUND783 / FULLY-SEPARATED RESIDUAL = EXACT THREE BASE-PROFILE FOLDS
--
-- R781 splits the swap-paired W2 residual into
--
--   fullySeparated + ccTouched.
--
-- R782 proves that every incidence surviving the fullySeparated mask has one
-- of exactly three orbit profiles.  Here we reflect that result directly at
-- the scalar carrier level by splitting the fullySeparated residual according
-- to the computed BASE R25 regime:
--
--   FullySeparatedD = LH-D + HL-D + HH-D.
--
-- The comparable base branch contributes exactly zero because any CC base
-- profile is, definitionally, ccTouched.
--
-- This is an exact finite fold partition.  No sign, estimate, norm, or
-- cardinality bound is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as R25
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
import DASHI.Physics.Closure.NSTriadKNR650EnergyOrbitBonyProfileRound775Exact as R775
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781

F : C3.RealField _
F = Rational.rationalRealField

baseComparableTouches :
  (beta : Physical.PhysicalTriadIncidence) →
  Scale.classifyScale R25.literalShellPolicy beta ≡ Scale.comparable →
  R781.ccTouched beta ≡ true
baseComparableTouches beta baseCC
  rewrite R775.orbitProfileBase beta
        | baseCC =
  refl

module ThreeProfileResidual
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

  module Two = R781.TwoFamilyResidual
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Two.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module T = Two.At cutoff time S

    lhCell : Physical.PhysicalTriadIncidence → ℚ
    lhCell beta
      with Scale.classifyScale R25.literalShellPolicy beta
    ... | Scale.lowHigh = T.fullySeparatedCell beta
    ... | Scale.highLow = 0ℚ
    ... | Scale.highHigh = 0ℚ
    ... | Scale.comparable = 0ℚ

    hlCell : Physical.PhysicalTriadIncidence → ℚ
    hlCell beta
      with Scale.classifyScale R25.literalShellPolicy beta
    ... | Scale.lowHigh = 0ℚ
    ... | Scale.highLow = T.fullySeparatedCell beta
    ... | Scale.highHigh = 0ℚ
    ... | Scale.comparable = 0ℚ

    hhCell : Physical.PhysicalTriadIncidence → ℚ
    hhCell beta
      with Scale.classifyScale R25.literalShellPolicy beta
    ... | Scale.lowHigh = 0ℚ
    ... | Scale.highLow = 0ℚ
    ... | Scale.highHigh = T.fullySeparatedCell beta
    ... | Scale.comparable = 0ℚ

    comparableFullySeparatedCellZero :
      (beta : Physical.PhysicalTriadIncidence) →
      Scale.classifyScale R25.literalShellPolicy beta ≡ Scale.comparable →
      T.fullySeparatedCell beta ≡ 0ℚ
    comparableFullySeparatedCellZero beta baseCC
      rewrite baseComparableTouches beta baseCC =
      refl

    fullySeparatedCellSplitsThree :
      (beta : Physical.PhysicalTriadIncidence) →
      T.fullySeparatedCell beta
      ≡ lhCell beta + hlCell beta + hhCell beta
    fullySeparatedCellSplitsThree beta
      with Scale.classifyScale R25.literalShellPolicy beta in base
    ... | Scale.lowHigh = solve (T.fullySeparatedCell beta ∷ [])
    ... | Scale.highLow = solve (T.fullySeparatedCell beta ∷ [])
    ... | Scale.highHigh = solve (T.fullySeparatedCell beta ∷ [])
    ... | Scale.comparable
      rewrite comparableFullySeparatedCellZero beta base =
      refl

    lhFold : ℚ
    lhFold = R38.foldPower lhCell T.P.items

    hlFold : ℚ
    hlFold = R38.foldPower hlCell T.P.items

    hhFold : ℚ
    hhFold = R38.foldPower hhCell T.P.items

    fullySeparatedFoldSplitsThree :
      T.fullySeparatedFold ≡ lhFold + hlFold + hhFold
    fullySeparatedFoldSplitsThree =
      go T.P.items
      where
      go :
        (items : List Physical.PhysicalTriadIncidence) →
        R38.foldPower T.fullySeparatedCell items
        ≡
        R38.foldPower lhCell items
          + R38.foldPower hlCell items
          + R38.foldPower hhCell items
      go [] = refl
      go (beta ∷ rest) =
        trans
          (cong (T.fullySeparatedCell beta +_) (go rest))
          (trans
            (cong
              (_+_
                (R38.foldPower lhCell rest
                  + R38.foldPower hlCell rest
                  + R38.foldPower hhCell rest))
              (fullySeparatedCellSplitsThree beta))
            (solve
              ( lhCell beta
              ∷ hlCell beta
              ∷ hhCell beta
              ∷ R38.foldPower lhCell rest
              ∷ R38.foldPower hlCell rest
              ∷ R38.foldPower hhCell rest
              ∷ [])))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round783FullySeparatedResidualExactlyThreeBaseFolds : Bool
round783FullySeparatedResidualExactlyThreeBaseFolds = true

round783ComparableBaseContributionExactlyZero : Bool
round783ComparableBaseContributionExactlyZero = true

round783ThreeProfileCancellationClosed : Bool
round783ThreeProfileCancellationClosed = false

round783IntroducesEstimate : Bool
round783IntroducesEstimate = false

round783W2Closed : Bool
round783W2Closed = false

round783ClayPromotion : Bool
round783ClayPromotion = false

round783FullySeparatedResidualExactlyThreeBaseFoldsIsTrue :
  round783FullySeparatedResidualExactlyThreeBaseFolds ≡ true
round783FullySeparatedResidualExactlyThreeBaseFoldsIsTrue = refl

round783ComparableBaseContributionExactlyZeroIsTrue :
  round783ComparableBaseContributionExactlyZero ≡ true
round783ComparableBaseContributionExactlyZeroIsTrue = refl

round783ThreeProfileCancellationClosedIsFalse :
  round783ThreeProfileCancellationClosed ≡ false
round783ThreeProfileCancellationClosedIsFalse = refl

round783IntroducesEstimateIsFalse :
  round783IntroducesEstimate ≡ false
round783IntroducesEstimateIsFalse = refl

round783W2ClosedIsFalse :
  round783W2Closed ≡ false
round783W2ClosedIsFalse = refl

round783ClayPromotionIsFalse :
  round783ClayPromotion ≡ false
round783ClayPromotionIsFalse = refl
