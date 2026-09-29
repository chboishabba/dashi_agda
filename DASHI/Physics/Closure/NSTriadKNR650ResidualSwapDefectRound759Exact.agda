{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650ResidualSwapDefectRound759Exact where

------------------------------------------------------------------------
-- ROUND759 / ALL LH-HL SWAP ASYMMETRY LIVES IN THE NESTED-ORBIT TERM
--
-- R749:
--
--   D(beta) = 3 * NestedOrbit(beta) - TwoDifference(beta).
--
-- R758 proves the actual two-difference production correction is pointwise
-- invariant under the physical p/q partner swap (under the same standard
-- reality/divergence-free structure already carried by R749).
--
-- Therefore exactly:
--
--   D(swap beta) - D(beta)
--     = 3 * (NestedOrbit(swap beta) - NestedOrbit(beta)).
--
-- No sign or estimate is used.  Hence any failure to collapse the R757
-- LH/HL channels is now localized entirely to the nested commutator orbit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
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
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744
import DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceAlignedW2Round749Exact as R749
import DASHI.Physics.Closure.NSTriadKNR650DyadicProductionSwapInvariantRound758Exact as R758

F : C3.RealField _
F = Rational.rationalRealField

module ResidualSwapDefect
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

    localResidualSwapDefect :
      (beta : Physical.PhysicalTriadIncidence) →
      Base.differenceAlignedCell (Symmetry.swapTriad beta)
        - Base.differenceAlignedCell beta
      ≡
      R744.three *
        ( Base.Base.nestedOrbitCell (Symmetry.swapTriad beta)
        - Base.Base.nestedOrbitCell beta )
    localResidualSwapDefect beta =
      let
        nestedSwap =
          Base.Base.nestedOrbitCell (Symmetry.swapTriad beta)
        nested =
          Base.Base.nestedOrbitCell beta
        prodSwap =
          Base.pairedTwoDifferenceCell (Symmetry.swapTriad beta)
        prod =
          Base.pairedTwoDifferenceCell beta
      in
      trans
        (cong
          (λ selected →
            (R744.three * nestedSwap - selected)
              - (R744.three * nested - prod))
          (productionSwapInvariant beta))
        (solve
          (R744.three ∷ nestedSwap ∷ nested ∷ prod ∷ []))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round759ProductionSwapDefectEliminated : Bool
round759ProductionSwapDefectEliminated = true

round759FullResidualSwapDefectIsThreeNestedSwapDefect : Bool
round759FullResidualSwapDefectIsThreeNestedSwapDefect = true

round759LHHLAsymmetryLocalizedToNestedOrbit : Bool
round759LHHLAsymmetryLocalizedToNestedOrbit = true

round759NestedSwapDefectClosed : Bool
round759NestedSwapDefectClosed = false

round759IntroducesEstimate : Bool
round759IntroducesEstimate = false

round759ClayPromotion : Bool
round759ClayPromotion = false

round759ProductionSwapDefectEliminatedIsTrue :
  round759ProductionSwapDefectEliminated ≡ true
round759ProductionSwapDefectEliminatedIsTrue = refl

round759FullResidualSwapDefectIsThreeNestedSwapDefectIsTrue :
  round759FullResidualSwapDefectIsThreeNestedSwapDefect ≡ true
round759FullResidualSwapDefectIsThreeNestedSwapDefectIsTrue = refl

round759LHHLAsymmetryLocalizedToNestedOrbitIsTrue :
  round759LHHLAsymmetryLocalizedToNestedOrbit ≡ true
round759LHHLAsymmetryLocalizedToNestedOrbitIsTrue = refl

round759NestedSwapDefectClosedIsFalse :
  round759NestedSwapDefectClosed ≡ false
round759NestedSwapDefectClosedIsFalse = refl

round759IntroducesEstimateIsFalse :
  round759IntroducesEstimate ≡ false
round759IntroducesEstimateIsFalse = refl

round759ClayPromotionIsFalse :
  round759ClayPromotion ≡ false
round759ClayPromotionIsFalse = refl
