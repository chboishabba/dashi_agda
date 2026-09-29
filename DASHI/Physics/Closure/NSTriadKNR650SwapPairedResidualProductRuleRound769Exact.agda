{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SwapPairedResidualProductRuleRound769Exact where

------------------------------------------------------------------------
-- ROUND769 / PRODUCT-RULE NORMAL FORM OF THE ACTUAL SWAP-PAIRED W2 CELL
--
-- R760:
--
--   PairD(beta)
--     = 3 [NestedOrbit(beta)+NestedOrbit(swap beta)]
--       - 2 PairedTwoDifference(beta).
--
-- R763:
--
--   NestedOrbit(beta)+NestedOrbit(swap beta)
--     = PairedMaskedBaseProductRuleRow(beta)
--       + 2 MaskedNestedRow(pLeg beta)
--       + 2 MaskedNestedRow(qLeg beta).
--
-- Therefore the actual division-free paired W2 cell has the exact normal form
--
--   PairD(beta)
--     = 3 PairedMaskedBaseProductRuleRow(beta)
--       + 6 MaskedNestedRow(pLeg beta)
--       + 6 MaskedNestedRow(qLeg beta)
--       - 2 PairedTwoDifference(beta).
--
-- This exposes the product-rule cancellation before classwise analysis while
-- preserving the two cyclic nested rows which do not disappear pointwise.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
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
import DASHI.Physics.Closure.NSTriadKNR650SwapPairedNestedOrbitNormalFormRound763Exact as R763
import DASHI.Physics.Closure.NSTriadKNR650SwapPairedThreeClassW2Round765Exact as R765

F : C3.RealField _
F = Rational.rationalRealField

module ProductRulePairedResidual
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

    module OrbitPair = R763.PairedNestedOrbit
      Base.Base.NestedAt.physicalSystem
      Paired.Local.O.Combined.Nested.S
      Paired.Local.O.Combined.Nested.L
      Paired.Local.O.Combined.Nested.H
      Base.Base.NestedAt.allModeTransverse

    productRulePairedResidualCell :
      Physical.PhysicalTriadIncidence → ℚ
    productRulePairedResidualCell beta =
      R744.three * OrbitPair.pairedMaskedBaseRow beta
        + R765.six
            * OrbitPair.N.maskedNestedOuterRow
                (Orbit.pEnergyLeg beta)
        + R765.six
            * OrbitPair.N.maskedNestedOuterRow
                (Orbit.qEnergyLeg beta)
        - Fold.two * Base.pairedTwoDifferenceCell beta

    pairedResidualCellIsProductRuleNormalForm :
      (beta : Physical.PhysicalTriadIncidence) →
      P.swapPairedResidualCell beta
      ≡ productRulePairedResidualCell beta
    pairedResidualCellIsProductRuleNormalForm beta =
      let
        nestedPair =
          Base.Base.nestedOrbitCell beta
            + Base.Base.nestedOrbitCell
                (Symmetry.swapTriad beta)
        prod = Base.pairedTwoDifferenceCell beta

        orbitMeaning =
          OrbitPair.nestedOrbitSwapPairNormalForm beta
      in
      trans
        (P.swapPairedResidualNormalForm beta)
        (trans
          (cong
            (λ nested →
              R744.three * nested - Fold.two * prod)
            orbitMeaning)
          (solve
            ( R744.three
            ∷ R765.six
            ∷ Fold.two
            ∷ OrbitPair.pairedMaskedBaseRow beta
            ∷ OrbitPair.N.maskedNestedOuterRow
                (Orbit.pEnergyLeg beta)
            ∷ OrbitPair.N.maskedNestedOuterRow
                (Orbit.qEnergyLeg beta)
            ∷ prod
            ∷ [])))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round769PairedResidualProductRuleNormalFormClosed : Bool
round769PairedResidualProductRuleNormalFormClosed = true

round769BaseNestedPairConvertedToProductRule : Bool
round769BaseNestedPairConvertedToProductRule = true

round769TwoCyclicNestedRowsRemain : Bool
round769TwoCyclicNestedRowsRemain = true

round769IntroducesEstimate : Bool
round769IntroducesEstimate = false

round769IntroducesNormOrAbsoluteValue : Bool
round769IntroducesNormOrAbsoluteValue = false

round769ClayPromotion : Bool
round769ClayPromotion = false

round769PairedResidualProductRuleNormalFormClosedIsTrue :
  round769PairedResidualProductRuleNormalFormClosed ≡ true
round769PairedResidualProductRuleNormalFormClosedIsTrue = refl

round769BaseNestedPairConvertedToProductRuleIsTrue :
  round769BaseNestedPairConvertedToProductRule ≡ true
round769BaseNestedPairConvertedToProductRuleIsTrue = refl

round769TwoCyclicNestedRowsRemainIsTrue :
  round769TwoCyclicNestedRowsRemain ≡ true
round769TwoCyclicNestedRowsRemainIsTrue = refl

round769IntroducesEstimateIsFalse :
  round769IntroducesEstimate ≡ false
round769IntroducesEstimateIsFalse = refl

round769IntroducesNormOrAbsoluteValueIsFalse :
  round769IntroducesNormOrAbsoluteValue ≡ false
round769IntroducesNormOrAbsoluteValueIsFalse = refl

round769ClayPromotionIsFalse :
  round769ClayPromotion ≡ false
round769ClayPromotionIsFalse = refl
