{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SwapPairedThreeClassW2Round765Exact where

------------------------------------------------------------------------
-- ROUND765 / THE DOUBLED R749 W2 RESIDUAL HAS EXACTLY THREE TRIADIC
--            ANALYTIC CHANNELS AFTER P/Q SWAP PAIRING
--
-- R760 defines the division-free paired scalar cell
--
--   PairD(beta) = D(beta)+D(swap beta)
--
-- and proves
--
--   sum PairD = 2 sum D.
--
-- PairD is itself swap invariant by construction.  R764 therefore gives
--
--   PairD_LH = PairD_HL
--
-- on the complete physical enumeration.  Together with the exact four-class
-- partition:
--
--   2 sum D = 2 PairD_LH + PairD_CC + PairD_HH.
--
-- Carrying the viscous margin through gives
--
--   2 Residual_delta
--     = 2 PairD_LH + PairD_CC + PairD_HH
--       + 6 (2 nu-delta) d_N.
--
-- Thus LH and HL are NOT independent analytic leaves on the preferred
-- division-free paired carrier.  No sign or estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_)
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
import DASHI.Physics.Closure.NSTriadKNR650SwapPairedResidualCarrierRound760Exact as R760
import DASHI.Physics.Closure.NSTriadKNR650SwapInvariantFourClassScalarRound764Exact as R764

F : C3.RealField _
F = Rational.rationalRealField

six : ℚ
six = 6

module ThreeClassW2
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

    items = Physical.physicalTriadEnumeration cutoff

    pairedCellSwapInvariant :
      (beta : Physical.PhysicalTriadIncidence) →
      P.swapPairedResidualCell (Symmetry.swapTriad beta)
      ≡ P.swapPairedResidualCell beta
    pairedCellSwapInvariant beta =
      let
        d = Base.differenceAlignedCell beta
        ds = Base.differenceAlignedCell (Symmetry.swapTriad beta)
      in
      trans
        (cong₂ _+_
          refl
          (cong Base.differenceAlignedCell
            (R38.swapTriadInvolutiveExact beta)))
        (solve (d ∷ ds ∷ []))

    lowHighPaired : ℚ
    lowHighPaired =
      R38.foldPower
        (R764.lowHighPart P.swapPairedResidualCell)
        items

    highLowPaired : ℚ
    highLowPaired =
      R38.foldPower
        (R764.highLowPart P.swapPairedResidualCell)
        items

    comparablePaired : ℚ
    comparablePaired =
      R38.foldPower
        (R764.comparablePart P.swapPairedResidualCell)
        items

    highHighPaired : ℚ
    highHighPaired =
      R38.foldPower
        (R764.highHighPart P.swapPairedResidualCell)
        items

    pairedFourClassPartition :
      P.swapPairedResidualFold
      ≡
      lowHighPaired
        + highLowPaired
        + comparablePaired
        + highHighPaired
    pairedFourClassPartition =
      R764.foldFourClassPartition
        P.swapPairedResidualCell items

    lowHighPairedEqualsHighLowPaired :
      lowHighPaired ≡ highLowPaired
    lowHighPairedEqualsHighLowPaired =
      R764.completeLowHighEqualsHighLow
        P.swapPairedResidualCell
        pairedCellSwapInvariant
        cutoff

    pairedFoldThreeClass :
      P.swapPairedResidualFold
      ≡
      Fold.two * lowHighPaired
        + comparablePaired
        + highHighPaired
    pairedFoldThreeClass =
      trans
        pairedFourClassPartition
        (trans
          (cong
            (λ selected →
              lowHighPaired
                + selected
                + comparablePaired
                + highHighPaired)
            (sym lowHighPairedEqualsHighLowPaired))
          (solve
            ( Fold.two
            ∷ lowHighPaired
            ∷ comparablePaired
            ∷ highHighPaired
            ∷ [])))

    twiceOriginalFoldIsThreeClass :
      Fold.two * Base.differenceAlignedFold
      ≡
      Fold.two * lowHighPaired
        + comparablePaired
        + highHighPaired
    twiceOriginalFoldIsThreeClass =
      trans
        (sym P.swapPairedFoldIsTwiceResidualFold)
        pairedFoldThreeClass

    doubledResidualThreeClass :
      (margin : ℚ) →
      Fold.two * Base.differenceAlignedResidual margin
      ≡
      Fold.two * lowHighPaired
        + comparablePaired
        + highHighPaired
        + six
            * Base.Base.retainedCoefficient margin
            * Paired.Local.O.W2.K.dissipationAt cutoff time
    doubledResidualThreeClass margin =
      let
        fold = Base.differenceAlignedFold
        coeff = Base.Base.retainedCoefficient margin
        diss = Paired.Local.O.W2.K.dissipationAt cutoff time
      in
      trans
        (solve
          ( Fold.two
          ∷ fold
          ∷ R744.three
          ∷ coeff
          ∷ diss
          ∷ six
          ∷ []))
        (cong
          (λ nonlinear →
            nonlinear + six * coeff * diss)
          twiceOriginalFoldIsThreeClass)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round765PairedResidualCellSwapInvariant : Bool
round765PairedResidualCellSwapInvariant = true

round765PairedLHEqualsHL : Bool
round765PairedLHEqualsHL = true

round765DoubledW2ResidualHasThreeTriadicChannels : Bool
round765DoubledW2ResidualHasThreeTriadicChannels = true

round765IndependentLHHLAnalyticLeaves : Bool
round765IndependentLHHLAnalyticLeaves = false

round765ThreeClassSignsClosed : Bool
round765ThreeClassSignsClosed = false

round765ResidualNonnegativeClosed : Bool
round765ResidualNonnegativeClosed = false

round765IntroducesEstimate : Bool
round765IntroducesEstimate = false

round765ClayPromotion : Bool
round765ClayPromotion = false

round765PairedResidualCellSwapInvariantIsTrue :
  round765PairedResidualCellSwapInvariant ≡ true
round765PairedResidualCellSwapInvariantIsTrue = refl

round765PairedLHEqualsHLIsTrue :
  round765PairedLHEqualsHL ≡ true
round765PairedLHEqualsHLIsTrue = refl

round765DoubledW2ResidualHasThreeTriadicChannelsIsTrue :
  round765DoubledW2ResidualHasThreeTriadicChannels ≡ true
round765DoubledW2ResidualHasThreeTriadicChannelsIsTrue = refl

round765IndependentLHHLAnalyticLeavesIsFalse :
  round765IndependentLHHLAnalyticLeaves ≡ false
round765IndependentLHHLAnalyticLeavesIsFalse = refl

round765ThreeClassSignsClosedIsFalse :
  round765ThreeClassSignsClosed ≡ false
round765ThreeClassSignsClosedIsFalse = refl

round765ResidualNonnegativeClosedIsFalse :
  round765ResidualNonnegativeClosed ≡ false
round765ResidualNonnegativeClosedIsFalse = refl

round765IntroducesEstimateIsFalse :
  round765IntroducesEstimate ≡ false
round765IntroducesEstimateIsFalse = refl

round765ClayPromotionIsFalse :
  round765ClayPromotion ≡ false
round765ClayPromotionIsFalse = refl
