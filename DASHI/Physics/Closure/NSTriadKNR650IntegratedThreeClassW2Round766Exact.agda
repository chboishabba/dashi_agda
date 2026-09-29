{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650IntegratedThreeClassW2Round766Exact where

------------------------------------------------------------------------
-- ROUND766 / INTEGRATE THE R765 THREE-CLASS DIVISION-FREE W2 CARRIER
--
-- R765 proves pointwise:
--
--   2 * DifferenceResidual_delta(t)
--     =
--       2 * LH_pair(t)
--       + CC_pair(t)
--       + HH_pair(t)
--       + 6 (2 nu-delta) d_N(t).
--
-- Define the right-hand side as ThreeClassResidual_delta(t).  Integration
-- linearity then gives exactly
--
--   IntegratedThreeClassResidual_delta(T)
--     = 2 * R751.integratedDifferenceResidual_delta(T).
--
-- R751 already identifies the latter with the canonical R746 residual.
-- No division or estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_)
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
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNR650IntegratedDyadicDifferenceW2Round751Exact as R751
import DASHI.Physics.Closure.NSTriadKNR650SwapPairedThreeClassW2Round765Exact as R765

F : C3.RealField _
F = Rational.rationalRealField

module IntegratedThreeClass
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

  module Three = R765.ThreeClassW2
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Difference = R751.IntegratedDifference
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Difference.Packet

  threeClassResidualAt :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    ℚ → Time → ℚ
  threeClassResidualAt cutoff S margin time =
    let
      module A = Three.At cutoff time S
    in
    Fold.two * A.lowHighPaired
      + A.comparablePaired
      + A.highHighPaired
      + R765.six
          * A.Base.Base.retainedCoefficient margin
          * Three.Paired.Local.O.W2.K.dissipationAt cutoff time

  threeClassResidualAtIsTwiceDifference :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (margin : ℚ) →
    (time : Time) →
    threeClassResidualAt cutoff S margin time
    ≡ Fold.two * Difference.differenceResidualAt cutoff S margin time
  threeClassResidualAtIsTwiceDifference cutoff S margin time =
    sym
      (Three.At.doubledResidualThreeClass
        cutoff time S margin)

  integratedThreeClassResidual :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    ℚ → Time → ℚ
  integratedThreeClassResidual cutoff S margin terminal =
    integrateTo (threeClassResidualAt cutoff S margin) terminal

  integratedThreeClassResidualIsTwiceDifference :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (margin : ℚ) →
    (terminal : Time) →
    integratedThreeClassResidual cutoff S margin terminal
    ≡
    Fold.two *
      Difference.integratedDifferenceResidual
        cutoff S margin terminal
  integratedThreeClassResidualIsTwiceDifference
      cutoff S margin terminal =
    trans
      (Energy.integrationCongruent integrationLinearity
        (threeClassResidualAtIsTwiceDifference cutoff S margin)
        terminal)
      (Energy.integrationConstantScale integrationLinearity
        Fold.two
        (Difference.differenceResidualAt cutoff S margin)
        terminal)

  integratedThreeClassResidualIsTwiceR746 :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (margin : ℚ) →
    (terminal : Time) →
    integratedThreeClassResidual cutoff S margin terminal
    ≡
    Fold.two *
      Difference.G.integratedOrbitAlignedResidual
        cutoff margin terminal
  integratedThreeClassResidualIsTwiceR746
      cutoff S margin terminal =
    trans
      (integratedThreeClassResidualIsTwiceDifference
        cutoff S margin terminal)
      (cong
        (Fold.two *_)
        (Difference.integratedDifferenceResidualIsR746
          cutoff S margin terminal))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round766ThreeClassResidualIntegratedBeforeEstimate : Bool
round766ThreeClassResidualIntegratedBeforeEstimate = true

round766IntegratedThreeClassIsTwiceR751Residual : Bool
round766IntegratedThreeClassIsTwiceR751Residual = true

round766IntegratedThreeClassIsTwiceCanonicalR746Residual : Bool
round766IntegratedThreeClassIsTwiceCanonicalR746Residual = true

round766IntroducesDivision : Bool
round766IntroducesDivision = false

round766IntroducesEstimate : Bool
round766IntroducesEstimate = false

round766IntegratedThreeClassNonnegativeClosed : Bool
round766IntegratedThreeClassNonnegativeClosed = false

round766ClayPromotion : Bool
round766ClayPromotion = false

round766ThreeClassResidualIntegratedBeforeEstimateIsTrue :
  round766ThreeClassResidualIntegratedBeforeEstimate ≡ true
round766ThreeClassResidualIntegratedBeforeEstimateIsTrue = refl

round766IntegratedThreeClassIsTwiceR751ResidualIsTrue :
  round766IntegratedThreeClassIsTwiceR751Residual ≡ true
round766IntegratedThreeClassIsTwiceR751ResidualIsTrue = refl

round766IntegratedThreeClassIsTwiceCanonicalR746ResidualIsTrue :
  round766IntegratedThreeClassIsTwiceCanonicalR746Residual ≡ true
round766IntegratedThreeClassIsTwiceCanonicalR746ResidualIsTrue = refl

round766IntroducesDivisionIsFalse :
  round766IntroducesDivision ≡ false
round766IntroducesDivisionIsFalse = refl

round766IntroducesEstimateIsFalse :
  round766IntroducesEstimate ≡ false
round766IntroducesEstimateIsFalse = refl

round766IntegratedThreeClassNonnegativeClosedIsFalse :
  round766IntegratedThreeClassNonnegativeClosed ≡ false
round766IntegratedThreeClassNonnegativeClosedIsFalse = refl

round766ClayPromotionIsFalse :
  round766ClayPromotion ≡ false
round766ClayPromotionIsFalse = refl
