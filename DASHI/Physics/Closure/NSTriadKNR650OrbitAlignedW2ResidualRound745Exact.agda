{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650OrbitAlignedW2ResidualRound745Exact where

------------------------------------------------------------------------
-- ROUND745 / DIVISION-FREE COMMON-CARRIER NORMAL FORM FOR POINTWISE W2
--
-- R744 puts literal critical production on the complete physical triad
-- enumeration with a zero-output mask, then cyclicizes it through the same
-- R38 k/p/q energy-leg action used by R700.
--
-- R723/R701 identify the combined residue with the complete R700 nested orbit.
--
-- Define on ONE physical incidence beta:
--
--   G(beta) = 3 * NestedOrbit(beta) - 2 * ProductionOrbit(beta).
--
-- Since
--
--   sum ProductionOrbit = 3 * S,
--   P = 2 * S,
--
-- and
--
--   sum NestedOrbit = Combined,
--
-- the complete fold satisfies exactly
--
--   sum G = 3 * (Combined - P).
--
-- Therefore for coeff = 2 nu - delta,
--
--   3 * (Combined - PacketStrictSurplus)
--     = sum G + 3 * coeff * d.
--
-- This is the division-free common-carrier form of the stronger pointwise W2
-- producer.  No sign or estimate is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
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
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700
import DASHI.Physics.Closure.NSTriadKNR650PointwiseW2PhysicalPacketCombinedRound741Exact as R741
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744

F : C3.RealField _
F = Rational.rationalRealField

module OrbitAligned
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

  module W2 = R741.PhysicalW2
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = W2.Packet
  module Combined = W2.Combined
  module Live = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf
  module Modes = ModeCarrier.LiteralModeCarrier
    Time initialTime integrateTo VectorDerivativeOf

  state = Live.stateTrajectory (Live.support D)

  systemAt :
    Nat → Time →
    Audit.FiniteComplex3GalerkinSystem F
      (Live.Base.E state)
      (Live.Base.I state)
  systemAt cutoff time =
    Live.Base.systemAt state cutoff time

  criticalProductionIncidenceAt :
    Nat → Time → ℚ
  criticalProductionIncidenceAt cutoff time =
    R38.foldPower
      (R744.maskedProductionCell (systemAt cutoff time))
      (Physical.physicalTriadEnumeration cutoff)

  criticalProductionOrbitAt :
    Nat → Time → ℚ
  criticalProductionOrbitAt cutoff time =
    R38.foldPower
      (R744.productionOrbitCell (systemAt cutoff time))
      (Physical.physicalTriadEnumeration cutoff)

  liveProductionIsTwiceIncidence :
    (cutoff : Nat) (time : Time) →
    W2.K.productionAt cutoff time
    ≡ Fold.two * criticalProductionIncidenceAt cutoff time
  liveProductionIsTwiceIncidence cutoff time
    rewrite Live.Base.systemCutoffAgreement state cutoff time =
    R744.criticalProductionIsTwiceFullMaskedIncidenceFold
      (systemAt cutoff time)
      (Modes.retainedModesExact C cutoff time)

  productionOrbitIsThreeIncidence :
    (cutoff : Nat) (time : Time) →
    criticalProductionOrbitAt cutoff time
    ≡ R744.three * criticalProductionIncidenceAt cutoff time
  productionOrbitIsThreeIncidence cutoff time
    rewrite Live.Base.systemCutoffAgreement state cutoff time =
    R744.foldProductionOrbit (systemAt cutoff time)

  module At
      (cutoff : Nat)
      (time : Time) where

    module CombinedAt = Combined.At cutoff time
    module NestedAt = Combined.Nested.At cutoff time

    system = systemAt cutoff time

    nestedOrbitCell :
      Physical.PhysicalTriadIncidence → ℚ
    nestedOrbitCell =
      NestedAt.Nested.nestedTriadOrbitResidue

    productionOrbitCell :
      Physical.PhysicalTriadIncidence → ℚ
    productionOrbitCell =
      R744.productionOrbitCell system

    orbitAlignedFold : ℚ
    orbitAlignedFold =
      R38.foldPower cleanOrbitAlignedCell
        (Physical.physicalTriadEnumeration cutoff)

    foldLinear :
      orbitAlignedFold
      ≡
      R744.three * NestedAt.nestedOrbitResidue
        - Fold.two * criticalProductionOrbitAt cutoff time
    foldLinear =
      go (Physical.physicalTriadEnumeration cutoff)
      where
      go :
        (items : List Physical.PhysicalTriadIncidence) →
        R38.foldPower cleanOrbitAlignedCell items
        ≡
        R744.three * R38.foldPower nestedOrbitCell items
          - Fold.two * R38.foldPower productionOrbitCell items
      go [] = solve []
      go (beta ∷ rest) =
        trans
          (cong (cleanOrbitAlignedCell beta +_) (go rest))
          (solve
            ( nestedOrbitCell beta
            ∷ productionOrbitCell beta
            ∷ R38.foldPower nestedOrbitCell rest
            ∷ R38.foldPower productionOrbitCell rest
            ∷ R744.three
            ∷ Fold.two
            ∷ []))

    foldIsThreeCombinedMinusThreeProduction :
      orbitAlignedFold
      ≡
      R744.three * Combined.combinedResidueAt cutoff time
        - R744.three * W2.K.productionAt cutoff time
    foldIsThreeCombinedMinusThreeProduction =
      let
        nestedToCombined :
          NestedAt.nestedOrbitResidue
          ≡ Combined.combinedResidueAt cutoff time
        nestedToCombined =
          sym CombinedAt.combinedIsLiteralNestedOrbit

        orbitThree =
          productionOrbitIsThreeIncidence cutoff time

        prodTwo =
          liveProductionIsTwiceIncidence cutoff time

        incidence = criticalProductionIncidenceAt cutoff time
        combined = Combined.combinedResidueAt cutoff time
        production = W2.K.productionAt cutoff time

        twiceOrbitIsThreeProduction :
          Fold.two * criticalProductionOrbitAt cutoff time
          ≡ R744.three * production
        twiceOrbitIsThreeProduction =
          trans
            (cong (Fold.two *_) orbitThree)
            (trans
              (solve
                (Fold.two ∷ R744.three ∷ incidence ∷ []))
              (cong
                (R744.three *_)
                (sym prodTwo)))
      in
      trans
        foldLinear
        (trans
          (cong₂ _-_
            (cong (R744.three *_) nestedToCombined)
            twiceOrbitIsThreeProduction)
          refl)

    retainedCoefficient :
      ℚ → ℚ
    retainedCoefficient margin =
      W2.K.twoNu - margin

    orbitAlignedResidual :
      ℚ → ℚ
    orbitAlignedResidual margin =
      orbitAlignedFold
        + R744.three
            * retainedCoefficient margin
            * W2.K.dissipationAt cutoff time

    residualIsThreeCombinedMinusPacket :
      (S : Packet.LivePhysicalPacketStructure D C cutoff) →
      (margin : ℚ) →
      orbitAlignedResidual margin
      ≡
      R744.three *
        ( Combined.combinedResidueAt cutoff time
        - Packet.physicalPacketStrictSurplusRate
            D cutoff margin time )
    residualIsThreeCombinedMinusPacket S margin =
      let
        production = W2.K.productionAt cutoff time
        diss = W2.K.dissipationAt cutoff time
        combined = Combined.combinedResidueAt cutoff time
        coeff = retainedCoefficient margin
        packet =
          Packet.physicalPacketStrictSurplusRate D cutoff margin time

        packetMeaning :
          packet ≡ production - coeff * diss
        packetMeaning =
          sym
            (W2.literalStrictSurplusIsPhysicalPacket
              cutoff S margin time)
      in
      trans
        (cong
          (λ gap →
            gap + R744.three * coeff * diss)
          foldIsThreeCombinedMinusThreeProduction)
        (trans
          (solve
            ( combined ∷ production ∷ coeff ∷ diss
            ∷ R744.three ∷ []))
          (cong
            (λ value → R744.three * (combined - value))
            (sym packetMeaning)))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round745ProductionAndCombinedShareCompleteOuterCarrier : Bool
round745ProductionAndCombinedShareCompleteOuterCarrier = true

round745OrbitAlignedResidualExact : Bool
round745OrbitAlignedResidualExact = true

round745ResidualUsesNoAbsoluteValue : Bool
round745ResidualUsesNoAbsoluteValue = true

round745ResidualUsesNoEstimate : Bool
round745ResidualUsesNoEstimate = true

round745PointwiseW2Closed : Bool
round745PointwiseW2Closed = false

round745ClayPromotion : Bool
round745ClayPromotion = false

round745ProductionAndCombinedShareCompleteOuterCarrierIsTrue :
  round745ProductionAndCombinedShareCompleteOuterCarrier ≡ true
round745ProductionAndCombinedShareCompleteOuterCarrierIsTrue = refl

round745OrbitAlignedResidualExactIsTrue :
  round745OrbitAlignedResidualExact ≡ true
round745OrbitAlignedResidualExactIsTrue = refl

round745ResidualUsesNoAbsoluteValueIsTrue :
  round745ResidualUsesNoAbsoluteValue ≡ true
round745ResidualUsesNoAbsoluteValueIsTrue = refl

round745ResidualUsesNoEstimateIsTrue :
  round745ResidualUsesNoEstimate ≡ true
round745ResidualUsesNoEstimateIsTrue = refl

round745PointwiseW2ClosedIsFalse :
  round745PointwiseW2Closed ≡ false
round745PointwiseW2ClosedIsFalse = refl

round745ClayPromotionIsFalse :
  round745ClayPromotion ≡ false
round745ClayPromotionIsFalse = refl
