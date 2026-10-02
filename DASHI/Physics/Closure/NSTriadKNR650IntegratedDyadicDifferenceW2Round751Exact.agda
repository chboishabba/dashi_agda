{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650IntegratedDyadicDifferenceW2Round751Exact where

------------------------------------------------------------------------
-- ROUND751 / INTEGRATE THE R749 TWO-DIFFERENCE LOCAL W2 CARRIER
--
-- For a fixed cutoff and the standard R648 physical packet structure S,
-- R749 defines at each time
--
--   DifferenceResidual(t)
--     = sum_beta [
--         3 NestedOrbit(beta)
--         - PairedDyadicTwoDifference(beta)
--       ]
--       + 3 (2 nu - delta) d_N(t),
--
-- and proves this is exactly the R745 orbit-aligned residual.
--
-- This owner integrates that literal local carrier and identifies it exactly
-- with R746's canonical integrated residual.  Therefore R747 W2
-- nonnegativity can be searched directly on the R749 local cell.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

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
import DASHI.Physics.Closure.NSTriadKNR650IntegratedOrbitAlignedW2ResidualRound746Exact as R746
import DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceAlignedW2Round749Exact as R749

F : C3.RealField _
F = Rational.rationalRealField

module IntegratedDifference
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

  module G = R746.IntegratedOrbitAligned
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Local = R749.DifferenceAligned
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = G.Packet

  differenceResidualAt :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    ℚ → Time → ℚ
  differenceResidualAt cutoff S margin time =
    Local.At.differenceAlignedResidual cutoff time S margin

  integratedDifferenceResidual :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    ℚ → Time → ℚ
  integratedDifferenceResidual cutoff S margin terminal =
    integrateTo (differenceResidualAt cutoff S margin) terminal

  integratedDifferenceResidualIsR746 :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (margin : ℚ) →
    (terminal : Time) →
    integratedDifferenceResidual cutoff S margin terminal
    ≡ G.integratedOrbitAlignedResidual cutoff margin terminal
  integratedDifferenceResidualIsR746 cutoff S margin terminal =
    Energy.integrationCongruent integrationLinearity
      (λ time →
        Local.At.differenceAlignedResidualIsR745Residual
          cutoff time S margin)
      terminal

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round751IntegratedTwoDifferenceCarrierIsCanonicalR746Residual : Bool
round751IntegratedTwoDifferenceCarrierIsCanonicalR746Residual = true

round751W2CanBeSearchedOnLiteralLocalTwoDifferenceCell : Bool
round751W2CanBeSearchedOnLiteralLocalTwoDifferenceCell = true

round751IntroducesEstimate : Bool
round751IntroducesEstimate = false

round751ResidualNonnegativeClosed : Bool
round751ResidualNonnegativeClosed = false

round751ClayPromotion : Bool
round751ClayPromotion = false

round751IntegratedTwoDifferenceCarrierIsCanonicalR746ResidualIsTrue :
  round751IntegratedTwoDifferenceCarrierIsCanonicalR746Residual ≡ true
round751IntegratedTwoDifferenceCarrierIsCanonicalR746ResidualIsTrue = refl

round751W2CanBeSearchedOnLiteralLocalTwoDifferenceCellIsTrue :
  round751W2CanBeSearchedOnLiteralLocalTwoDifferenceCell ≡ true
round751W2CanBeSearchedOnLiteralLocalTwoDifferenceCellIsTrue = refl

round751IntroducesEstimateIsFalse :
  round751IntroducesEstimate ≡ false
round751IntroducesEstimateIsFalse = refl

round751ResidualNonnegativeClosedIsFalse :
  round751ResidualNonnegativeClosed ≡ false
round751ResidualNonnegativeClosedIsFalse = refl

round751ClayPromotionIsFalse :
  round751ClayPromotion ≡ false
round751ClayPromotionIsFalse = refl
