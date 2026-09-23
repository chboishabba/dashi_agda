{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNDirectLeafAInitialEndpointAdapterRound594Exact where

------------------------------------------------------------------------
-- ROUND594 / R558-R568 INITIAL ENDPOINT -> R593 UNIFORM BOUND
--
-- R593 still accepts the already-same-object statement
--
--   globalSelfFlux_N(0) <= B_initial
--
-- as a field.  R568 has already proved the stronger per-cutoff endpoint theorem
--
--   globalSelfFlux_N(0)
--     <= twoW_N * (48 * energySquare_N(0))
--
-- on the SAME canonical output list, provided the explicit Fourier unit-gap
-- and mode-radius calibrations are supplied.
--
-- Therefore the remaining source receipt is not a self-flux estimate.  It is
-- only a cutoff-independent envelope for that explicit initial-data expression.
-- This owner performs the exact same-object adapter into R593.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNNormalizedDoubleMixedCellMassRound452Exact as R452
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedDoubleMixedMassRound456Exact as R456
import DASHI.Physics.Closure.NSTriadKNLiveGlobalSelfFluxEndpointWeldRound568Exact as E568
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as FTC564
import DASHI.Physics.Closure.NSTriadKNSignedRateVectorPaymentToR503Exact as Order
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as C568
import DASHI.Physics.Closure.NSTriadKNDirectLeafAStandardReceiptsRound593Exact as R593
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

module Compile
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCrossCalculus :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarAlgebra : R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (integration : R495.IntegrationTransportAuthority Time integrateTo)
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo VectorDerivativeOf)
    (R : R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
      Time initialTime integrateTo VectorDerivativeOf
      (R408.LiteralDynamics.literalPhysicalTrajectory
        Time initialTime integrateTo VectorDerivativeOf D)) where

  module Standard = R593.Compile
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCrossCalculus vectorAlgebra hermitianCalculus
    constantCalculus scalarAlgebra integration D R

  module Comm = C568.LiveCommutatorOnly
    Time initialTime integrateTo VectorDerivativeOf integration

  module EndpointAt (cutoff : Nat) = E568.LiveEndpointWeld
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCrossCalculus vectorAlgebra hermitianCalculus
    constantCalculus scalarAlgebra D R cutoff

  record DirectLeafAEndpointProducer594 : Set₁ where
    field
      scalarFTC594 :
        FTC564.ScalarFundamentalTheorem564
          Time initialTime integrateTo ScalarDerivativeOf

      integrationOrder594 :
        Order.IntegrationOrderAuthority Time integrateTo

      unitGap594 :
        (cutoff : Nat) →
        let module E = EndpointAt cutoff
        in R450.CanonicalFourierUnitGap E.Slice0.PS

      radiusCalibration594 :
        (cutoff : Nat) →
        let module E = EndpointAt cutoff
        in R456.PhysicalModeRadiusCalibration
          (Field30.physicalEmbedding E.Slice0.PS)
          (Field30.physicalInverseSquare E.Slice0.PS)
          E.S

      initialEndpointBound594 : ℚ

      initialEnergySquareEnvelope594 :
        (cutoff : Nat) →
        let
          module E = EndpointAt cutoff
          module G = E.WithEndpointGeometry
            (unitGap594 cutoff)
            (radiusCalibration594 cutoff)
        in
        G.Endpoint.twoW
          * (R452.fortyEight * G.Endpoint.Mass.energySquare)
        ≤ initialEndpointBound594

      commutatorBudget594 :
        Comm.CommutatorOnlySpacetimeBudget568
          (R408.LiteralDynamics.literalPhysicalTrajectory
            Time initialTime integrateTo VectorDerivativeOf D) R

  open DirectLeafAEndpointProducer594 public

  initialSelfFluxUpper594 :
    (P : DirectLeafAEndpointProducer594) →
    (cutoff : Nat) →
    let module T = DASHI.Physics.Closure.NSTriadKNLiveGlobalSelfFluxTangentWeldRound570Exact.TangentWeld
          Time initialTime integrateTo
          VectorDerivativeOf ScalarDerivativeOf
          projectedCrossCalculus vectorAlgebra hermitianCalculus
          constantCalculus scalarAlgebra integration D R cutoff
    in
    T.Global.globalSelfFlux initialTime ≤ initialEndpointBound594 P
  initialSelfFluxUpper594 P cutoff =
    let
      module E = EndpointAt cutoff
      module G = E.WithEndpointGeometry
        (unitGap594 P cutoff)
        (radiusCalibration594 P cutoff)
    in
    ℚP.≤-trans
      G.globalInitialSelfFluxEnergySquareEndpoint568
      (initialEnergySquareEnvelope594 P cutoff)

  toR593Producer594 :
    DirectLeafAEndpointProducer594 →
    Standard.DirectLeafAStandardProducer593
  toR593Producer594 P = record
    { Standard.scalarFTC593 = scalarFTC594 P
    ; Standard.integrationOrder593 = integrationOrder594 P
    ; Standard.initialSelfFluxBound593 = initialEndpointBound594 P
    ; Standard.initialSelfFluxUpper593 = initialSelfFluxUpper594 P
    ; Standard.commutatorBudget593 = commutatorBudget594 P
    }

  toR572Producer594 :
    DirectLeafAEndpointProducer594 →
    Standard.Old.DirectLeafAProducer572
  toR572Producer594 P =
    Standard.toR572Producer593 (toR593Producer594 P)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round594R558R568InitialEndpointAdapterClosed : Bool
round594R558R568InitialEndpointAdapterClosed = true

round594DirectInitialSelfFluxEstimateStillRequired : Bool
round594DirectInitialSelfFluxEstimateStillRequired = false

round594CutoffIndependentInitialEnergyEnvelopeStillProofBearing : Bool
round594CutoffIndependentInitialEnergyEnvelopeStillProofBearing = true

round594FourierUnitGapCalibrationStillExplicit : Bool
round594FourierUnitGapCalibrationStillExplicit = true

round594ModeRadiusCalibrationStillExplicit : Bool
round594ModeRadiusCalibrationStillExplicit = true

round594ScalarFTCStillProofBearing : Bool
round594ScalarFTCStillProofBearing = true

round594NovelR568BudgetStillProofBearing : Bool
round594NovelR568BudgetStillProofBearing = true

round594IntroducesNewNSEstimate : Bool
round594IntroducesNewNSEstimate = false

round594CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round594CurrentGlobalFirstResidualStillLeafA =
  R504.currentFirstTerminalResidual

round594ClayPromotion : Bool
round594ClayPromotion = false

round594R558R568InitialEndpointAdapterClosedIsTrue :
  round594R558R568InitialEndpointAdapterClosed ≡ true
round594R558R568InitialEndpointAdapterClosedIsTrue = refl

round594DirectInitialSelfFluxEstimateStillRequiredIsFalse :
  round594DirectInitialSelfFluxEstimateStillRequired ≡ false
round594DirectInitialSelfFluxEstimateStillRequiredIsFalse = refl

round594CutoffIndependentInitialEnergyEnvelopeStillProofBearingIsTrue :
  round594CutoffIndependentInitialEnergyEnvelopeStillProofBearing ≡ true
round594CutoffIndependentInitialEnergyEnvelopeStillProofBearingIsTrue = refl

round594IntroducesNewNSEstimateIsFalse :
  round594IntroducesNewNSEstimate ≡ false
round594IntroducesNewNSEstimateIsFalse = refl

round594ClayPromotionIsFalse :
  round594ClayPromotion ≡ false
round594ClayPromotionIsFalse = refl
