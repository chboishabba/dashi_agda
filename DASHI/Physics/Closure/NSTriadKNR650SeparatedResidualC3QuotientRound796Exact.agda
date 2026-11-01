{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedResidualC3QuotientRound796Exact where

------------------------------------------------------------------------
-- ROUND796 / WELD R795 INTO THE LIVE FULLY-SEPARATED W2 RESIDUAL
--
-- R793:
--
--   3 D_sep = 27 B_sep - 2 P_cycle.
--
-- R795, on the exact same live physical system, gives pointwise
--
--   P_cycle(beta) = 3 Q(beta),
--
-- where Q is the single surviving NS-specific q-quotient production channel.
-- The fully-separated mask is already q-invariant, so this identity survives
-- masking and folding:
--
--   P_cycle,sep = 3 Q_sep.
--
-- Therefore the factor-three common divisor can be cancelled exactly:
--
--   D_sep = 9 B_sep - 2 Q_sep.
--
-- No estimate, norm, positivity, or foreign-carrier identification is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
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
import DASHI.Physics.Closure.NSTriadKNR650DyadicProductionQCycleCollectionRound795Exact as R795
import DASHI.Physics.Closure.NSTriadKNR650SeparatedResidualFactorTwentySevenRound793Exact as R793

F : C3.RealField _
F = Rational.rationalRealField

oneThird : ℚ
oneThird = + 1 / 3

module SeparatedC3Quotient
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

  module Prev = R793.SeparatedFactorTwentySeven
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Prev.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module P = Prev.At cutoff time S
    module X = P.X

    items : List Physical.PhysicalTriadIncidence
    items = P.items

    quotientCell :
      Physical.PhysicalTriadIncidence → ℚ
    quotientCell beta =
      let
        module Q = R795.QCycle
          P.P.Base.system
          (Packet.realityAt S time)
          (Packet.divergenceFreeAt S time)
          beta
      in
      Q.quotientInvariantProduction

    maskedQuotientCell :
      Physical.PhysicalTriadIncidence → ℚ
    maskedQuotientCell beta with R781.ccTouched beta
    ... | true = 0ℚ
    ... | false = quotientCell beta

    productionCycleIsThreeQuotient :
      (beta : Physical.PhysicalTriadIncidence) →
      X.maskedCycleDyadicProduction beta
      ≡ R744.three * maskedQuotientCell beta
    productionCycleIsThreeQuotient beta
      with R781.ccTouched beta in touched
    ... | true = solve (R744.three ∷ [])
    ... | false =
      let
        module Q = R795.QCycle
          P.P.Base.system
          (Packet.realityAt S time)
          (Packet.divergenceFreeAt S time)
          beta
      in
      Q.cycleProductionIsThreeQuotientInvariant

    quotientFold : ℚ
    quotientFold =
      R38.foldPower maskedQuotientCell items

    productionFoldIsThreeQuotientFold :
      X.maskedProductionFold
      ≡ R744.three * quotientFold
    productionFoldIsThreeQuotientFold =
      go items
      where
      go :
        (xs : List Physical.PhysicalTriadIncidence) →
        R38.foldPower X.maskedCycleDyadicProduction xs
        ≡ R744.three * R38.foldPower maskedQuotientCell xs
      go [] = solve []
      go (beta ∷ rest) =
        trans
          (cong₂ _+_
            (productionCycleIsThreeQuotient beta)
            (go rest))
          (solve
            ( R744.three
            ∷ maskedQuotientCell beta
            ∷ R38.foldPower maskedQuotientCell rest
            ∷ []))

    pairedBaseFold : ℚ
    pairedBaseFold =
      R38.foldPower P.Cycle.Sep.maskedPairedBaseRow items

    separatedResidualFactorNine :
      X.A.T.T.fullySeparatedFold
      ≡
      R793.twentySeven / R744.three * pairedBaseFold
        - Fold.two * quotientFold
    separatedResidualFactorNine =
      let
        Dsep = X.A.T.T.fullySeparatedFold
        Bsep = pairedBaseFold
        Qsep = quotientFold

        substituted :
          R744.three * Dsep
          ≡
          R793.twentySeven * Bsep
            - Fold.two * (R744.three * Qsep)
        substituted =
          trans
            P.separatedResidualFactorTwentySeven
            (cong
              (λ selected →
                R793.twentySeven * Bsep - Fold.two * selected)
              productionFoldIsThreeQuotientFold)

        scaled =
          cong (oneThird *_) substituted

        leftMeaning :
          oneThird * (R744.three * Dsep) ≡ Dsep
        leftMeaning = solve (Dsep ∷ R744.three ∷ [])

        rightMeaning :
          oneThird *
            (R793.twentySeven * Bsep
              - Fold.two * (R744.three * Qsep))
          ≡
          R793.twentySeven / R744.three * Bsep
            - Fold.two * Qsep
        rightMeaning =
          solve
            ( R793.twentySeven
            ∷ R744.three
            ∷ Fold.two
            ∷ Bsep
            ∷ Qsep
            ∷ [])
      in
      trans (sym leftMeaning)
        (trans scaled rightMeaning)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round796SeparatedProductionCycleIsThreeQuotientFold : Bool
round796SeparatedProductionCycleIsThreeQuotientFold = true

round796SeparatedResidualFactorTwentySevenReducedToFactorNine : Bool
round796SeparatedResidualFactorTwentySevenReducedToFactorNine = true

round796RemainingSeparatedCarrierHasOneQQuotientProductionChannel : Bool
round796RemainingSeparatedCarrierHasOneQQuotientProductionChannel = true

round796IntroducesEstimate : Bool
round796IntroducesEstimate = false

round796W2Closed : Bool
round796W2Closed = false

round796ClayPromotion : Bool
round796ClayPromotion = false

round796SeparatedProductionCycleIsThreeQuotientFoldIsTrue :
  round796SeparatedProductionCycleIsThreeQuotientFold ≡ true
round796SeparatedProductionCycleIsThreeQuotientFoldIsTrue = refl

round796SeparatedResidualFactorTwentySevenReducedToFactorNineIsTrue :
  round796SeparatedResidualFactorTwentySevenReducedToFactorNine ≡ true
round796SeparatedResidualFactorTwentySevenReducedToFactorNineIsTrue = refl

round796IntroducesEstimateIsFalse :
  round796IntroducesEstimate ≡ false
round796IntroducesEstimateIsFalse = refl

round796W2ClosedIsFalse :
  round796W2Closed ≡ false
round796W2ClosedIsFalse = refl

round796ClayPromotionIsFalse :
  round796ClayPromotion ≡ false
round796ClayPromotionIsFalse = refl
