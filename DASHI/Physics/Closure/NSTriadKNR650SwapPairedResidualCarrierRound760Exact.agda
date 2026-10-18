{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SwapPairedResidualCarrierRound760Exact where

------------------------------------------------------------------------
-- ROUND760 / DIVISION-FREE P/Q-SWAP-PAIRED W2 RESIDUAL CARRIER
--
-- R759 shows that individual LH/HL cells need not agree because all remaining
-- swap asymmetry lives in the nested orbit.  Do not demand pointwise
-- invariance.  Instead pair each incidence with its physical p/q partner:
--
--   PairD(beta) = D(beta) + D(swap beta).
--
-- R758 gives P_dyad(swap beta)=P_dyad(beta), hence pointwise
--
--   PairD(beta)
--     = 3 [N(beta)+N(swap beta)] - 2 P_dyad(beta).
--
-- Since swap is a permutation of the COMPLETE physical enumeration,
--
--   sum PairD = 2 sum D.
--
-- This is the division-free carrier appropriate for combining the exchanged
-- LH/HL classes.  It introduces neither a sign nor an estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
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
import DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceAlignedW2Round749Exact as R749
import DASHI.Physics.Closure.NSTriadKNR650DyadicProductionSwapInvariantRound758Exact as R758

F : C3.RealField _
F = Rational.rationalRealField

module SwapPairedResidual
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

  module Local = R749.DifferenceAligned
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Local.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module Base = Local.At cutoff time S

    items : List Physical.PhysicalTriadIncidence
    items = Physical.physicalTriadEnumeration cutoff

    swapPairedResidualCell :
      Physical.PhysicalTriadIncidence → ℚ
    swapPairedResidualCell beta =
      Base.differenceAlignedCell beta
        + Base.differenceAlignedCell (Symmetry.swapTriad beta)

    productionSwapInvariant :
      (beta : Physical.PhysicalTriadIncidence) →
      Base.pairedTwoDifferenceCell (Symmetry.swapTriad beta)
      ≡ Base.pairedTwoDifferenceCell beta
    productionSwapInvariant beta =
      R758.pairedTwoDifferenceSwapInvariant
        Base.system
        (Packet.realityAt S time)
        (Packet.divergenceFreeAt S time)
        beta

    swapPairedResidualNormalForm :
      (beta : Physical.PhysicalTriadIncidence) →
      swapPairedResidualCell beta
      ≡
      R744.three *
        ( Base.Base.nestedOrbitCell beta
        + Base.Base.nestedOrbitCell (Symmetry.swapTriad beta) )
      - Fold.two * Base.pairedTwoDifferenceCell beta
    swapPairedResidualNormalForm beta =
      let
        n = Base.Base.nestedOrbitCell beta
        ns = Base.Base.nestedOrbitCell (Symmetry.swapTriad beta)
        p = Base.pairedTwoDifferenceCell beta
        ps = Base.pairedTwoDifferenceCell (Symmetry.swapTriad beta)
      in
      trans
        (cong
          (λ selected →
            (R744.three * n - p)
              + (R744.three * ns - selected))
          (productionSwapInvariant beta))
        (solve (R744.three ∷ Fold.two ∷ n ∷ ns ∷ p ∷ []))

    swapPairedResidualFold : ℚ
    swapPairedResidualFold =
      R38.foldPower swapPairedResidualCell items

    foldSwapResidualIsFoldResidual :
      R38.foldPower
        (λ beta →
          Base.differenceAlignedCell (Symmetry.swapTriad beta))
        items
      ≡ Base.differenceAlignedFold
    foldSwapResidualIsFoldResidual =
      trans
        (sym
          (R38.foldMap
            Base.differenceAlignedCell
            Symmetry.swapTriad items))
        (R38.foldPermutationInvariant
          Base.differenceAlignedCell
          (R38.swapTriadEnumerationPermutation cutoff))

    foldPairedLinear :
      swapPairedResidualFold
      ≡
      Base.differenceAlignedFold
        + R38.foldPower
            (λ beta →
              Base.differenceAlignedCell (Symmetry.swapTriad beta))
            items
    foldPairedLinear =
      go items
      where
      go :
        (xs : List Physical.PhysicalTriadIncidence) →
        R38.foldPower swapPairedResidualCell xs
        ≡
        R38.foldPower Base.differenceAlignedCell xs
          + R38.foldPower
              (λ beta →
                Base.differenceAlignedCell (Symmetry.swapTriad beta))
              xs
      go [] = solve []
      go (beta ∷ rest) =
        trans
          (cong (swapPairedResidualCell beta +_) (go rest))
          (solve
            ( Base.differenceAlignedCell beta
            ∷ Base.differenceAlignedCell (Symmetry.swapTriad beta)
            ∷ R38.foldPower Base.differenceAlignedCell rest
            ∷ R38.foldPower
                (λ selected →
                  Base.differenceAlignedCell (Symmetry.swapTriad selected))
                rest
            ∷ []))

    swapPairedFoldIsTwiceResidualFold :
      swapPairedResidualFold
      ≡ Fold.two * Base.differenceAlignedFold
    swapPairedFoldIsTwiceResidualFold =
      trans
        foldPairedLinear
        (trans
          (cong
            (Base.differenceAlignedFold +_)
            foldSwapResidualIsFoldResidual)
          (solve (Fold.two ∷ Base.differenceAlignedFold ∷ [])))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round760SwapPairedResidualPointwiseNormalFormClosed : Bool
round760SwapPairedResidualPointwiseNormalFormClosed = true

round760CompleteSwapPairedFoldIsTwiceR749Fold : Bool
round760CompleteSwapPairedFoldIsTwiceR749Fold = true

round760LHHLCanBeHandledAsUnorderedSwapPairs : Bool
round760LHHLCanBeHandledAsUnorderedSwapPairs = true

round760RequiresPointwiseNestedSwapInvariance : Bool
round760RequiresPointwiseNestedSwapInvariance = false

round760IntroducesDivision : Bool
round760IntroducesDivision = false

round760IntroducesEstimate : Bool
round760IntroducesEstimate = false

round760ResidualNonnegativeClosed : Bool
round760ResidualNonnegativeClosed = false

round760ClayPromotion : Bool
round760ClayPromotion = false

round760SwapPairedResidualPointwiseNormalFormClosedIsTrue :
  round760SwapPairedResidualPointwiseNormalFormClosed ≡ true
round760SwapPairedResidualPointwiseNormalFormClosedIsTrue = refl

round760CompleteSwapPairedFoldIsTwiceR749FoldIsTrue :
  round760CompleteSwapPairedFoldIsTwiceR749Fold ≡ true
round760CompleteSwapPairedFoldIsTwiceR749FoldIsTrue = refl

round760LHHLCanBeHandledAsUnorderedSwapPairsIsTrue :
  round760LHHLCanBeHandledAsUnorderedSwapPairs ≡ true
round760LHHLCanBeHandledAsUnorderedSwapPairsIsTrue = refl

round760RequiresPointwiseNestedSwapInvarianceIsFalse :
  round760RequiresPointwiseNestedSwapInvariance ≡ false
round760RequiresPointwiseNestedSwapInvarianceIsFalse = refl

round760IntroducesDivisionIsFalse :
  round760IntroducesDivision ≡ false
round760IntroducesDivisionIsFalse = refl

round760IntroducesEstimateIsFalse :
  round760IntroducesEstimate ≡ false
round760IntroducesEstimateIsFalse = refl

round760ResidualNonnegativeClosedIsFalse :
  round760ResidualNonnegativeClosed ≡ false
round760ResidualNonnegativeClosedIsFalse = refl

round760ClayPromotionIsFalse :
  round760ClayPromotion ≡ false
round760ClayPromotionIsFalse = refl
