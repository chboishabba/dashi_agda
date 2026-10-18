{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact where

------------------------------------------------------------------------
-- ROUND781 / EXACT TWO-FAMILY SPLIT OF THE SWAP-PAIRED W2 RESIDUAL
--
-- R777-R780 classify every separated-base energy orbit.  The invariant that
-- survives swap pairing and retains cyclic information is:
--
--   ccTouched(beta)
--     iff at least one coordinate of Pi(beta) is comparable.
--
-- Define the complementary family as fullySeparated.
--
-- The predicate is exactly swap-invariant because R775 transports profiles by
--
--   (c0,cp,cq) -> (swapClass c0,cq,cp),
--
-- and swapClass fixes comparable.
--
-- The R760 paired residual is then split pointwise and globally as
--
--   PairD = FullySeparatedD + CCTouchedD.
--
-- No sign or estimate is asserted for either family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNPhysicalBonySwapEquivarianceRound129Exact as R129
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
import DASHI.Physics.Closure.NSTriadKNR650SwapPairedResidualCarrierRound760Exact as R760
import DASHI.Physics.Closure.NSTriadKNR650EnergyOrbitBonyProfileRound775Exact as R775

F : C3.RealField _
F = Rational.rationalRealField

orBool : Bool → Bool → Bool
orBool true right = true
orBool false right = right

orBoolComm :
  (left right : Bool) →
  orBool left right ≡ orBool right left
orBoolComm true true = refl
orBoolComm true false = refl
orBoolComm false true = refl
orBoolComm false false = refl

regimeComparable : Scale.ScaleRegime → Bool
regimeComparable Scale.lowHigh = false
regimeComparable Scale.highLow = false
regimeComparable Scale.highHigh = false
regimeComparable Scale.comparable = true

regimeComparableSwapInvariant :
  (regime : Scale.ScaleRegime) →
  regimeComparable (R129.swapRegime regime)
  ≡ regimeComparable regime
regimeComparableSwapInvariant Scale.lowHigh = refl
regimeComparableSwapInvariant Scale.highLow = refl
regimeComparableSwapInvariant Scale.highHigh = refl
regimeComparableSwapInvariant Scale.comparable = refl

profileTouchesComparable :
  R775.EnergyOrbitBonyProfile → Bool
profileTouchesComparable profile =
  orBool
    (regimeComparable (R775.baseClass profile))
    (orBool
      (regimeComparable (R775.pClass profile))
      (regimeComparable (R775.qClass profile)))

profileTouchesComparableSwap :
  (profile : R775.EnergyOrbitBonyProfile) →
  profileTouchesComparable (R775.swapOrbitProfile profile)
  ≡ profileTouchesComparable profile
profileTouchesComparableSwap (R775.orbit-profile base p q)
  rewrite regimeComparableSwapInvariant base
        | orBoolComm (regimeComparable q) (regimeComparable p) =
  refl

ccTouched :
  Physical.PhysicalTriadIncidence → Bool
ccTouched beta =
  profileTouchesComparable (R775.orbitProfile beta)

ccTouchedSwapInvariant :
  (beta : Physical.PhysicalTriadIncidence) →
  ccTouched (Symmetry.swapTriad beta) ≡ ccTouched beta
ccTouchedSwapInvariant beta =
  trans
    (cong profileTouchesComparable (R775.orbitProfileSwap beta))
    (profileTouchesComparableSwap (R775.orbitProfile beta))

module TwoFamilyResidual
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

  module Paired = R760.SwapPairedResidual
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Paired.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module P = Paired.At cutoff time S

    fullySeparatedCell :
      Physical.PhysicalTriadIncidence → ℚ
    fullySeparatedCell beta with ccTouched beta
    ... | true = 0ℚ
    ... | false = P.swapPairedResidualCell beta

    ccTouchedCell :
      Physical.PhysicalTriadIncidence → ℚ
    ccTouchedCell beta with ccTouched beta
    ... | true = P.swapPairedResidualCell beta
    ... | false = 0ℚ

    residualCellSplits :
      (beta : Physical.PhysicalTriadIncidence) →
      P.swapPairedResidualCell beta
      ≡ fullySeparatedCell beta + ccTouchedCell beta
    residualCellSplits beta with ccTouched beta
    ... | true = refl
    ... | false = refl

    pairedResidualCellSwapInvariant :
      (beta : Physical.PhysicalTriadIncidence) →
      P.swapPairedResidualCell (Symmetry.swapTriad beta)
      ≡ P.swapPairedResidualCell beta
    pairedResidualCellSwapInvariant beta
      rewrite R38.swapTriadInvolutiveExact beta =
      solve
        ( P.Base.differenceAlignedCell beta
        ∷ P.Base.differenceAlignedCell (Symmetry.swapTriad beta)
        ∷ [])

    fullySeparatedCellSwapInvariant :
      (beta : Physical.PhysicalTriadIncidence) →
      fullySeparatedCell (Symmetry.swapTriad beta)
      ≡ fullySeparatedCell beta
    fullySeparatedCellSwapInvariant beta
      rewrite ccTouchedSwapInvariant beta
      with ccTouched beta
    ... | true = refl
    ... | false = pairedResidualCellSwapInvariant beta

    ccTouchedCellSwapInvariant :
      (beta : Physical.PhysicalTriadIncidence) →
      ccTouchedCell (Symmetry.swapTriad beta)
      ≡ ccTouchedCell beta
    ccTouchedCellSwapInvariant beta
      rewrite ccTouchedSwapInvariant beta
      with ccTouched beta
    ... | true = pairedResidualCellSwapInvariant beta
    ... | false = refl

    fullySeparatedFold : ℚ
    fullySeparatedFold =
      R38.foldPower fullySeparatedCell P.items

    ccTouchedFold : ℚ
    ccTouchedFold =
      R38.foldPower ccTouchedCell P.items

    completeResidualFoldSplits :
      P.swapPairedResidualFold
      ≡ fullySeparatedFold + ccTouchedFold
    completeResidualFoldSplits =
      go P.items
      where
      go :
        (items : List Physical.PhysicalTriadIncidence) →
        R38.foldPower P.swapPairedResidualCell items
        ≡
        R38.foldPower fullySeparatedCell items
          + R38.foldPower ccTouchedCell items
      go [] = refl
      go (beta ∷ rest) =
        trans
          (cong
            (P.swapPairedResidualCell beta +_)
            (go rest))
          (trans
            (cong
              (_+_
                (R38.foldPower fullySeparatedCell rest
                  + R38.foldPower ccTouchedCell rest))
              (residualCellSplits beta))
            (solve
              ( fullySeparatedCell beta
              ∷ ccTouchedCell beta
              ∷ R38.foldPower fullySeparatedCell rest
              ∷ R38.foldPower ccTouchedCell rest
              ∷ [])))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round781CCTouchedPredicateSwapInvariant : Bool
round781CCTouchedPredicateSwapInvariant = true

round781SwapPairedResidualSplitsIntoTwoOrbitFamilies : Bool
round781SwapPairedResidualSplitsIntoTwoOrbitFamilies = true

round781FullySeparatedFamilyPaid : Bool
round781FullySeparatedFamilyPaid = false

round781CCTouchedFamilyPaid : Bool
round781CCTouchedFamilyPaid = false

round781IntroducesEstimate : Bool
round781IntroducesEstimate = false

round781W2Closed : Bool
round781W2Closed = false

round781ClayPromotion : Bool
round781ClayPromotion = false

round781CCTouchedPredicateSwapInvariantIsTrue :
  round781CCTouchedPredicateSwapInvariant ≡ true
round781CCTouchedPredicateSwapInvariantIsTrue = refl

round781SwapPairedResidualSplitsIntoTwoOrbitFamiliesIsTrue :
  round781SwapPairedResidualSplitsIntoTwoOrbitFamilies ≡ true
round781SwapPairedResidualSplitsIntoTwoOrbitFamiliesIsTrue = refl

round781FullySeparatedFamilyPaidIsFalse :
  round781FullySeparatedFamilyPaid ≡ false
round781FullySeparatedFamilyPaidIsFalse = refl

round781CCTouchedFamilyPaidIsFalse :
  round781CCTouchedFamilyPaid ≡ false
round781CCTouchedFamilyPaidIsFalse = refl

round781IntroducesEstimateIsFalse :
  round781IntroducesEstimate ≡ false
round781IntroducesEstimateIsFalse = refl

round781W2ClosedIsFalse :
  round781W2Closed ≡ false
round781W2ClosedIsFalse = refl

round781ClayPromotionIsFalse :
  round781ClayPromotion ≡ false
round781ClayPromotionIsFalse = refl
