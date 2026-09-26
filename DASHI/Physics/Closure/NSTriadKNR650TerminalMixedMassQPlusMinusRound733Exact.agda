{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650TerminalMixedMassQPlusMinusRound733Exact where

------------------------------------------------------------------------
-- ROUND733 / R691 TERMINAL MIXED MASS = OLD R227 Q_{+-} COHERENT MASS
--
-- R691/R699's endpoint observable is
--
--   E_M,N(t) = sum_{k != 0} Re <M_k(t), M_k(t)>,
--
-- where M_k is the complete fixed-output fold of D1a.mixedProductCell.
--
-- R227's old Package-A observable is
--
--   Q_+-(N,t) = sum_{k != 0} || sum_{p+q=k} u_p^+ x u_q^- ||^2.
--
-- These are the SAME finite observable:
--
--   * D1a.mixedProductCell is definitionally R224.mixedPlusMinus;
--   * R457 proves Re <v,v> = ||v||^2 on the exact rational C3 carrier;
--   * both owners fold the same canonical nonzero output list.
--
-- This exact weld lets the historical Q_+- analysis speak directly to R731's
-- terminal endpoint.  It does NOT close the endpoint ceiling.  In particular,
-- R241's schematic Q_+- payment assumes a uniform H^(1/2) critical barrier;
-- using that payment to construct A/R723, which is then used with R730 to prove
-- the critical barrier, would be circular.  R238 already records precisely this
-- critical-barrier circularity principle.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityGlobalCompanionRound227Exact as R227
import DASHI.Physics.Closure.NSTriadKNPhysicalDiagonalEnergySquareEndpointRound457Exact as R457
import DASHI.Physics.Closure.NSTriadKNR650GlobalMixedEnergyEndpointUpperRound699Exact as R699
import DASHI.Physics.Closure.NSTriadKNDefectFailureForcesCriticalBarrierRound241Exact as R241
import DASHI.Physics.Closure.NSTriadKNProfileExtractionCircularityRound238Exact as R238

F : C3.RealField _
F = Rational.rationalRealField

module TerminalQPlusMinus
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
    (scalarScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf) where

  module Upper = R699.EndpointUpper
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus
    FTC integrationLinearity integrationTransport D

  module End = Upper.Balance.Local.End

  mixedOutputMass :
    Nat → Z3.FourierMode → Time → ℚ
  mixedOutputMass cutoff output time =
    R227.mixedOutputMass
      End.S
      (End.velocityAt cutoff time)
      cutoff output

  fixedOutputSelfEnergyIsQPlusMinusMass :
    (cutoff : Nat) (output : Z3.FourierMode) (time : Time) →
    End.selfEnergy cutoff output time
    ≡ mixedOutputMass cutoff output time
  fixedOutputSelfEnergyIsQPlusMinusMass cutoff output time =
    R457.selfHermitianIsNorm
      (End.fixedOutputMixedCurve cutoff output time)

  qPlusMinusMassOn :
    Nat → Time → List Z3.FourierMode → ℚ
  qPlusMinusMassOn cutoff time [] = 0
  qPlusMinusMassOn cutoff time (output ∷ rest) =
    mixedOutputMass cutoff output time
      + qPlusMinusMassOn cutoff time rest

  qPlusMinusMassOnIsR227 :
    (cutoff : Nat) (time : Time) (outputs : List Z3.FourierMode) →
    qPlusMinusMassOn cutoff time outputs
    ≡
    R227.globalMixedHelicityMass
      End.S
      (End.velocityAt cutoff time)
      cutoff outputs
  qPlusMinusMassOnIsR227 cutoff time [] = refl
  qPlusMinusMassOnIsR227 cutoff time (output ∷ rest) =
    cong₂ _+_ refl
      (qPlusMinusMassOnIsR227 cutoff time rest)

  globalSelfEnergyIsQPlusMinusMassOn :
    (cutoff : Nat) (time : Time) (outputs : List Z3.FourierMode) →
    Upper.sumSelfEnergy cutoff time outputs
    ≡ qPlusMinusMassOn cutoff time outputs
  globalSelfEnergyIsQPlusMinusMassOn cutoff time [] = refl
  globalSelfEnergyIsQPlusMinusMassOn
      cutoff time (output ∷ rest) =
    trans
      (cong₂ _+_
        (fixedOutputSelfEnergyIsQPlusMinusMass cutoff output time)
        (globalSelfEnergyIsQPlusMinusMassOn cutoff time rest))
      refl

  globalSelfEnergyIsCanonicalR227QPlusMinus :
    (cutoff : Nat) (time : Time) →
    Upper.globalSelfEnergy cutoff time
    ≡
    R227.globalMixedHelicityMass
      End.S
      (End.velocityAt cutoff time)
      cutoff
      (Canonical.nonzeroCutoffModes cutoff)
  globalSelfEnergyIsCanonicalR227QPlusMinus cutoff time =
    trans
      (globalSelfEnergyIsQPlusMinusMassOn
        cutoff time (Canonical.nonzeroCutoffModes cutoff))
      (qPlusMinusMassOnIsR227
        cutoff time (Canonical.nonzeroCutoffModes cutoff))

------------------------------------------------------------------------
-- Status / circularity firewall.
------------------------------------------------------------------------

round733R691EndpointIsCanonicalR227QPlusMinus : Bool
round733R691EndpointIsCanonicalR227QPlusMinus = true

round733R241BarrierToQPlusMinusCompilerExists : Bool
round733R241BarrierToQPlusMinusCompilerExists =
  R241.round241ScalarBarrierToDefectCompilerClosed

round733R241PhysicalCriticalInterpolationInstalled : Bool
round733R241PhysicalCriticalInterpolationInstalled =
  R241.round241PhysicalCriticalInterpolationInstalled

round733UsingCriticalBarrierToPayAEndpointIsNoncircular : Bool
round733UsingCriticalBarrierToPayAEndpointIsNoncircular = false

round733CriticalBarrierCircularityAlreadyRecorded : Bool
round733CriticalBarrierCircularityAlreadyRecorded =
  R238.round238UsingUniformHOneHalfToProduceUniformHOneHalfWouldBeCircular

round733TerminalQPlusMinusCeilingClosedNoncircularly : Bool
round733TerminalQPlusMinusCeilingClosedNoncircularly = false

round733IntroducesEstimate : Bool
round733IntroducesEstimate = false

round733ClayPromotion : Bool
round733ClayPromotion = false

round733R691EndpointIsCanonicalR227QPlusMinusIsTrue :
  round733R691EndpointIsCanonicalR227QPlusMinus ≡ true
round733R691EndpointIsCanonicalR227QPlusMinusIsTrue = refl

round733R241BarrierToQPlusMinusCompilerExistsIsTrue :
  round733R241BarrierToQPlusMinusCompilerExists ≡ true
round733R241BarrierToQPlusMinusCompilerExistsIsTrue =
  R241.round241ScalarBarrierToDefectCompilerClosedIsTrue

round733R241PhysicalCriticalInterpolationInstalledIsFalse :
  round733R241PhysicalCriticalInterpolationInstalled ≡ false
round733R241PhysicalCriticalInterpolationInstalledIsFalse =
  R241.round241PhysicalCriticalInterpolationInstalledIsFalse

round733UsingCriticalBarrierToPayAEndpointIsNoncircularIsFalse :
  round733UsingCriticalBarrierToPayAEndpointIsNoncircular ≡ false
round733UsingCriticalBarrierToPayAEndpointIsNoncircularIsFalse = refl

round733CriticalBarrierCircularityAlreadyRecordedIsTrue :
  round733CriticalBarrierCircularityAlreadyRecorded ≡ true
round733CriticalBarrierCircularityAlreadyRecordedIsTrue =
  R238.round238UsingUniformHOneHalfToProduceUniformHOneHalfWouldBeCircularIsTrue

round733TerminalQPlusMinusCeilingClosedNoncircularlyIsFalse :
  round733TerminalQPlusMinusCeilingClosedNoncircularly ≡ false
round733TerminalQPlusMinusCeilingClosedNoncircularlyIsFalse = refl

round733IntroducesEstimateIsFalse :
  round733IntroducesEstimate ≡ false
round733IntroducesEstimateIsFalse = refl

round733ClayPromotionIsFalse :
  round733ClayPromotion ≡ false
round733ClayPromotionIsFalse = refl
