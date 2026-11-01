{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650GlobalPairedResidualProductRuleRound773Exact where

------------------------------------------------------------------------
-- ROUND773 / GLOBAL SWAP-PAIRED W2 RESIDUAL ON ONE PRODUCT-RULE BASE FOLD
--
-- R760 gives pointwise
--
--   PairD(beta)
--     = 3 [N(beta)+N(swap beta)] - 2 P_dyad(beta).
--
-- R772 proves on the COMPLETE physical enumeration
--
--   sum [N(beta)+N(swap beta)]
--     = 3 sum PairedBaseProductRule(beta).
--
-- Hence exactly
--
--   sum PairD
--     = 9 sum PairedBaseProductRule
--       - 2 sum P_dyad.
--
-- R760 independently proves sum PairD = 2 sum D.  Thus this is a global
-- representation of the same R749 nonlinear residual, not a new estimate.
--
-- The theorem deliberately does not push p/q reindexing through an R25 class
-- selector.  Any class-local gain must be obtained before this global collapse.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

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
import DASHI.Physics.Closure.NSTriadKNR650SwapPairedResidualCarrierRound760Exact as R760
import DASHI.Physics.Closure.NSTriadKNR650GlobalPairedNestedProductRuleRound772Exact as R772

F : C3.RealField _
F = Rational.rationalRealField

nine : ℚ
nine = 9

module GlobalProductRuleResidual
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
    module Base = P.Base

    module G = R772.GlobalPairedNested
      Base.Base.NestedAt.physicalSystem
      Paired.Local.O.Combined.Nested.S
      Paired.Local.O.Combined.Nested.L
      Paired.Local.O.Combined.Nested.H
      Base.Base.NestedAt.allModeTransverse

    items : List Physical.PhysicalTriadIncidence
    items = Physical.physicalTriadEnumeration cutoff

    pairedProductRuleBaseFold : ℚ
    pairedProductRuleBaseFold =
      R38.foldPower G.pairedBaseRow items

    pairedDyadicProductionFold : ℚ
    pairedDyadicProductionFold =
      R38.foldPower Base.pairedTwoDifferenceCell items

    foldPointwiseNormalForm :
      P.swapPairedResidualFold
      ≡
      R744.three *
        R38.foldPower G.pairedOrbitCell items
        - Fold.two * pairedDyadicProductionFold
    foldPointwiseNormalForm =
      go items

      go :
        (xs : List Physical.PhysicalTriadIncidence) →
        R38.foldPower P.swapPairedResidualCell xs
        ≡
        R744.three * R38.foldPower G.pairedOrbitCell xs
          - Fold.two * R38.foldPower Base.pairedTwoDifferenceCell xs
      go [] = solve []
      go (beta ∷ rest) =
        trans
          (cong (P.swapPairedResidualCell beta +_) (go rest))
          (trans
            (cong
              (λ selected →
                selected
                  + (R744.three * R38.foldPower G.pairedOrbitCell rest
                    - Fold.two *
                        R38.foldPower Base.pairedTwoDifferenceCell rest))
              (P.swapPairedResidualNormalForm beta))
            (solve
              ( R744.three
              ∷ Fold.two
              ∷ G.pairedOrbitCell beta
              ∷ Base.pairedTwoDifferenceCell beta
              ∷ R38.foldPower G.pairedOrbitCell rest
              ∷ R38.foldPower Base.pairedTwoDifferenceCell rest
              ∷ [])))

    globalPairedResidualProductRuleNormalForm :
      P.swapPairedResidualFold
      ≡
      nine * pairedProductRuleBaseFold
        - Fold.two * pairedDyadicProductionFold
    globalPairedResidualProductRuleNormalForm
      rewrite Paired.Local.O.Live.Base.systemCutoffAgreement
        Paired.Local.O.state cutoff time =
      trans
        foldPointwiseNormalForm
        (trans
          (cong
            (λ nested →
              R744.three * nested
                - Fold.two * pairedDyadicProductionFold)
            G.completePairedNestedOrbitIsThreePairedBaseRows)
          (solve
            ( R744.three
            ∷ nine
            ∷ pairedProductRuleBaseFold
            ∷ pairedDyadicProductionFold
            ∷ Fold.two
            ∷ [])))

    productRuleNormalFormIsTwiceR749Fold :
      nine * pairedProductRuleBaseFold
        - Fold.two * pairedDyadicProductionFold
      ≡ Fold.two * Base.differenceAlignedFold
    productRuleNormalFormIsTwiceR749Fold =
      trans
        (sym globalPairedResidualProductRuleNormalForm)
        P.swapPairedFoldIsTwiceResidualFold

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round773GlobalPairedResidualHasOneProductRuleBaseFold : Bool
round773GlobalPairedResidualHasOneProductRuleBaseFold = true

round773TwoCyclicRowsRemainAfterCompleteEnumeration : Bool
round773TwoCyclicRowsRemainAfterCompleteEnumeration = false

round773GlobalProductRuleFormIsExactlyTwiceR749Fold : Bool
round773GlobalProductRuleFormIsExactlyTwiceR749Fold = true

round773ClassLocalGainObtainedByGlobalReindexing : Bool
round773ClassLocalGainObtainedByGlobalReindexing = false

round773IntroducesEstimate : Bool
round773IntroducesEstimate = false

round773ClayPromotion : Bool
round773ClayPromotion = false

round773GlobalPairedResidualHasOneProductRuleBaseFoldIsTrue :
  round773GlobalPairedResidualHasOneProductRuleBaseFold ≡ true
round773GlobalPairedResidualHasOneProductRuleBaseFoldIsTrue = refl

round773TwoCyclicRowsRemainAfterCompleteEnumerationIsFalse :
  round773TwoCyclicRowsRemainAfterCompleteEnumeration ≡ false
round773TwoCyclicRowsRemainAfterCompleteEnumerationIsFalse = refl

round773GlobalProductRuleFormIsExactlyTwiceR749FoldIsTrue :
  round773GlobalProductRuleFormIsExactlyTwiceR749Fold ≡ true
round773GlobalProductRuleFormIsExactlyTwiceR749FoldIsTrue = refl

round773ClassLocalGainObtainedByGlobalReindexingIsFalse :
  round773ClassLocalGainObtainedByGlobalReindexing ≡ false
round773ClassLocalGainObtainedByGlobalReindexingIsFalse = refl

round773IntroducesEstimateIsFalse :
  round773IntroducesEstimate ≡ false
round773IntroducesEstimateIsFalse = refl

round773ClayPromotionIsFalse :
  round773ClayPromotion ≡ false
round773ClayPromotionIsFalse = refl
