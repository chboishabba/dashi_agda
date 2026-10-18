{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650IntegratedOrbitAlignedW2ResidualRound746Exact where

------------------------------------------------------------------------
-- ROUND746 / INTEGRATE THE R745 COMMON-CARRIER W2 RESIDUAL
--
-- R745 gives pointwise, under the standard R648 packet structure,
--
--   OrbitResidual_N,delta(t)
--     = 3 * (Combined_N(t) - PacketStrictSurplus_N,delta(t)).
--
-- Integrating with the repository's scalar linearity authority gives
--
--   integral OrbitResidual
--     = 3 * (integral Combined - integral PacketStrictSurplus).
--
-- Thus the ORIGINAL integrated W2 payment is exactly equivalent, up to the
-- fixed positive factor 3, to nonnegativity of one signed orbit-aligned
-- spacetime residual.  This file closes the equality; no positivity estimate
-- is manufactured.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

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
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744

F : C3.RealField _
F = Rational.rationalRealField

module IntegratedOrbitAligned
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
  module Combined = O.Combined

  integrateSub :
    (left right : Time → ℚ) →
    (terminal : Time) →
    integrateTo (λ time → left time - right time) terminal
    ≡ integrateTo left terminal - integrateTo right terminal
  integrateSub left right terminal =
    let
      expose :
        integrateTo (λ time → left time - right time) terminal
        ≡
        integrateTo
          (λ time → left time + (- 1) * right time)
          terminal
      expose =
        Energy.integrationCongruent integrationLinearity
          (λ time → solve (left time ∷ right time ∷ []))
          terminal

      split :
        integrateTo
          (λ time → left time + (- 1) * right time)
          terminal
        ≡
        integrateTo left terminal
          + integrateTo (λ time → (- 1) * right time) terminal
      split =
        Energy.integrationAdditive integrationLinearity
          left (λ time → (- 1) * right time) terminal

      scale :
        integrateTo (λ time → (- 1) * right time) terminal
        ≡ (- 1) * integrateTo right terminal
      scale =
        Energy.integrationConstantScale integrationLinearity
          (- 1) right terminal
    in
    trans expose
      (trans split
        (trans
          (cong (integrateTo left terminal +_) scale)
          (solve
            ( integrateTo left terminal
            ∷ integrateTo right terminal
            ∷ []))))

  integratedOrbitAlignedResidual :
    Nat → ℚ → Time → ℚ
  integratedOrbitAlignedResidual cutoff margin terminal =
    integrateTo
      (λ time → O.At.orbitAlignedResidual cutoff time margin)
      terminal

  integratedResidualIsThreeCombinedMinusPacket :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (margin : ℚ) →
    (terminal : Time) →
    integratedOrbitAlignedResidual cutoff margin terminal
    ≡
    R744.three *
      ( Combined.integratedCombinedSelfExternal cutoff terminal
      - Packet.integratedPhysicalPacketStrictSurplus
          D cutoff margin terminal )
  integratedResidualIsThreeCombinedMinusPacket
      cutoff S margin terminal =
    let
      combinedAt = Combined.combinedResidueAt cutoff
      packetAt =
        Packet.physicalPacketStrictSurplusRate D cutoff margin

      pointwise :
        (time : Time) →
        O.At.orbitAlignedResidual cutoff time margin
        ≡
        R744.three * (combinedAt time - packetAt time)
      pointwise time =
        O.At.residualIsThreeCombinedMinusPacket
          cutoff time S margin

      congruent :
        integratedOrbitAlignedResidual cutoff margin terminal
        ≡
        integrateTo
          (λ time →
            R744.three * (combinedAt time - packetAt time))
          terminal
      congruent =
        Energy.integrationCongruent integrationLinearity
          pointwise terminal

      scaled :
        integrateTo
          (λ time →
            R744.three * (combinedAt time - packetAt time))
          terminal
        ≡
        R744.three *
          integrateTo
            (λ time → combinedAt time - packetAt time)
            terminal
      scaled =
        Energy.integrationConstantScale integrationLinearity
          R744.three
          (λ time → combinedAt time - packetAt time)
          terminal

      split :
        integrateTo
          (λ time → combinedAt time - packetAt time)
          terminal
        ≡
        Combined.integratedCombinedSelfExternal cutoff terminal
          - Packet.integratedPhysicalPacketStrictSurplus
              D cutoff margin terminal
      split =
        integrateSub combinedAt packetAt terminal
    in
    trans congruent
      (trans scaled
        (cong (R744.three *_) split))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round746IntegratedOrbitAlignedResidualExact : Bool
round746IntegratedOrbitAlignedResidualExact = true

round746OriginalW2DifferenceLivesOnOneSignedResidualIntegral : Bool
round746OriginalW2DifferenceLivesOnOneSignedResidualIntegral = true

round746IntroducesEstimate : Bool
round746IntroducesEstimate = false

round746IntegratedResidualNonnegativeClosed : Bool
round746IntegratedResidualNonnegativeClosed = false

round746ClayPromotion : Bool
round746ClayPromotion = false

round746IntegratedOrbitAlignedResidualExactIsTrue :
  round746IntegratedOrbitAlignedResidualExact ≡ true
round746IntegratedOrbitAlignedResidualExactIsTrue = refl

round746OriginalW2DifferenceLivesOnOneSignedResidualIntegralIsTrue :
  round746OriginalW2DifferenceLivesOnOneSignedResidualIntegral ≡ true
round746OriginalW2DifferenceLivesOnOneSignedResidualIntegralIsTrue = refl

round746IntroducesEstimateIsFalse :
  round746IntroducesEstimate ≡ false
round746IntroducesEstimateIsFalse = refl

round746IntegratedResidualNonnegativeClosedIsFalse :
  round746IntegratedResidualNonnegativeClosed ≡ false
round746IntegratedResidualNonnegativeClosedIsFalse = refl

round746ClayPromotionIsFalse :
  round746ClayPromotion ≡ false
round746ClayPromotionIsFalse = refl
