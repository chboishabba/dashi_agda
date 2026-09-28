{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceAlignedW2Round749Exact where

------------------------------------------------------------------------
-- ROUND749 / REPLACE THE R745 ORIENTED PRODUCTION ORBIT BY R748'S
--            LOCAL TWO-DYADIC-DIFFERENCE CELL
--
-- R745 nonlinear fold:
--
--   sum [ 3 NestedOrbit(beta) - 2 OrientedProductionOrbit(beta) ].
--
-- R748 proves globally:
--
--   sum PairedTwoDifference(beta)
--     = sum PairedProductionOrbit(beta)
--     = 2 * sum OrientedProductionOrbit(beta).
--
-- Hence WITHOUT changing the total W2 residual:
--
--   sum [ 3 NestedOrbit(beta) - PairedTwoDifference(beta) ]
--     = R745.orbitAlignedFold.
--
-- This is the first preferred W2 carrier where BOTH nonlinear pieces are
-- literal local functions of the SAME outer incidence beta and the production
-- part has only two dyadic multiplier-difference channels.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

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
import DASHI.Physics.Closure.NSTriadKNR650OrbitAlignedW2ResidualRound745Exact as R745
import DASHI.Physics.Closure.NSTriadKNR650DyadicPairedProductionDifferenceRound748Exact as R748
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold

F : C3.RealField _
F = Rational.rationalRealField

module DifferenceAligned
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

  module O = R745.OrbitAligned
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = O.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module Base = O.At cutoff time

    system = O.systemAt cutoff time
    items = Physical.physicalTriadEnumeration cutoff

    pairedTwoDifferenceCell :
      Physical.PhysicalTriadIncidence → ℚ
    pairedTwoDifferenceCell =
      R748.pairedProductionTwoDifferenceCell system

    differenceAlignedCell :
      Physical.PhysicalTriadIncidence → ℚ
    differenceAlignedCell beta =
      R744.three * Base.nestedOrbitCell beta
        - pairedTwoDifferenceCell beta

    differenceAlignedFold : ℚ
    differenceAlignedFold =
      R38.foldPower differenceAlignedCell items

    pairedOrbitFoldIsTwoDifferenceFold :
      R38.foldPower (R748.pairedProductionOrbitCell system) items
      ≡
      R38.foldPower pairedTwoDifferenceCell items
    pairedOrbitFoldIsTwoDifferenceFold =
      go items
      where
      reality = Packet.realityAt S time
      divergenceFree = Packet.divergenceFreeAt S time

      go :
        (xs : List Physical.PhysicalTriadIncidence) →
        R38.foldPower (R748.pairedProductionOrbitCell system) xs
        ≡
        R38.foldPower pairedTwoDifferenceCell xs
      go [] = refl
      go (beta ∷ rest) =
        cong₂ _+_
          (R748.pairedProductionOrbitIsTwoDifferences
            system reality divergenceFree beta)
          (go rest)

    pairedTwoDifferenceFoldIsDoubleR744Orbit :
      R38.foldPower pairedTwoDifferenceCell items
      ≡
      Fold.two * O.criticalProductionOrbitAt cutoff time
    pairedTwoDifferenceFoldIsDoubleR744Orbit =
      trans
        (sym pairedOrbitFoldIsTwoDifferenceFold)
        (R748.foldPairedProductionOrbit system)

    differenceAlignedFoldIsR745OrbitAlignedFold :
      differenceAlignedFold ≡ Base.orbitAlignedFold
    differenceAlignedFoldIsR745OrbitAlignedFold =
      let
        nested =
          R38.foldPower Base.nestedOrbitCell items
        paired =
          R38.foldPower pairedTwoDifferenceCell items
        oriented = O.criticalProductionOrbitAt cutoff time

        split :
          differenceAlignedFold
          ≡ R744.three * nested - paired
        split = go items
          where
          go :
            (xs : List Physical.PhysicalTriadIncidence) →
            R38.foldPower differenceAlignedCell xs
            ≡
            R744.three * R38.foldPower Base.nestedOrbitCell xs
              - R38.foldPower pairedTwoDifferenceCell xs
          go [] = solve []
          go (beta ∷ rest) =
            trans
              (cong (differenceAlignedCell beta +_) (go rest))
              (solve
                ( Base.nestedOrbitCell beta
                ∷ pairedTwoDifferenceCell beta
                ∷ R38.foldPower Base.nestedOrbitCell rest
                ∷ R38.foldPower pairedTwoDifferenceCell rest
                ∷ R744.three
                ∷ []))
      in
      trans split
        (trans
          (cong
            (R744.three * nested -_)
            pairedTwoDifferenceFoldIsDoubleR744Orbit)
          (sym Base.foldLinear))

    differenceAlignedResidual :
      ℚ → ℚ
    differenceAlignedResidual margin =
      differenceAlignedFold
        + R744.three
            * Base.retainedCoefficient margin
            * O.W2.K.dissipationAt cutoff time

    differenceAlignedResidualIsR745Residual :
      (margin : ℚ) →
      differenceAlignedResidual margin
      ≡ Base.orbitAlignedResidual margin
    differenceAlignedResidualIsR745Residual margin =
      cong
        (λ nonlinear →
          nonlinear
            + R744.three
                * Base.retainedCoefficient margin
                * O.W2.K.dissipationAt cutoff time)
        differenceAlignedFoldIsR745OrbitAlignedFold

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round749W2NonlinearGapLivesOnOneLocalOuterIncidenceCell : Bool
round749W2NonlinearGapLivesOnOneLocalOuterIncidenceCell = true

round749ProductionPartHasExactlyTwoDyadicDifferenceChannels : Bool
round749ProductionPartHasExactlyTwoDyadicDifferenceChannels = true

round749DifferenceAlignedResidualIsExactlyR745Residual : Bool
round749DifferenceAlignedResidualIsExactlyR745Residual = true

round749IntroducesEstimate : Bool
round749IntroducesEstimate = false

round749ResidualNonnegativeClosed : Bool
round749ResidualNonnegativeClosed = false

round749ClayPromotion : Bool
round749ClayPromotion = false

round749W2NonlinearGapLivesOnOneLocalOuterIncidenceCellIsTrue :
  round749W2NonlinearGapLivesOnOneLocalOuterIncidenceCell ≡ true
round749W2NonlinearGapLivesOnOneLocalOuterIncidenceCellIsTrue = refl

round749ProductionPartHasExactlyTwoDyadicDifferenceChannelsIsTrue :
  round749ProductionPartHasExactlyTwoDyadicDifferenceChannels ≡ true
round749ProductionPartHasExactlyTwoDyadicDifferenceChannelsIsTrue = refl

round749DifferenceAlignedResidualIsExactlyR745ResidualIsTrue :
  round749DifferenceAlignedResidualIsExactlyR745Residual ≡ true
round749DifferenceAlignedResidualIsExactlyR745ResidualIsTrue = refl

round749IntroducesEstimateIsFalse :
  round749IntroducesEstimate ≡ false
round749IntroducesEstimateIsFalse = refl

round749ResidualNonnegativeClosedIsFalse :
  round749ResidualNonnegativeClosed ≡ false
round749ResidualNonnegativeClosedIsFalse = refl

round749ClayPromotionIsFalse :
  round749ClayPromotion ≡ false
round749ClayPromotionIsFalse = refl
