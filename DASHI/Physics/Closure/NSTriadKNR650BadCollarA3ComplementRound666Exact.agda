{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650BadCollarA3ComplementRound666Exact where

------------------------------------------------------------------------
-- ROUND666 / BAD-COLLAR RESIDUAL IS THE COMPLEMENT OF CENTERED A3
--
-- R664 gives, on one complete physical output fibre,
--
--   Residual
--     = RateSelf + PairDiff
--     = n * WeightedWork.
--
-- The existing centered A3 normal form gives on the SAME fibre
--
--   SignedA3
--     = - n * WeightedWork + RateTotal * W(M,M).
--
-- Hence exactly
--
--   Residual + SignedA3 = RateTotal * W(M,M).
--
-- This is an important sign firewall.  The existing A3 payment compiler is an
-- UPPER payment for SignedA3.  It cannot simply be reused as an upper payment
-- for Residual: that would require a LOWER control on SignedA3 (or an
-- independent payment of the positive self-work complement).
--
-- The theorem below is first proved as generic finite algebra, then attached to
-- the actual R661 trajectory and lifted through the standard integration
-- congruence/additivity authority already isolated by C6.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentWorkDifferenceVectorBridgeExact as Vector
import DASHI.Physics.Closure.NSTriadKNA3CenteredVectorWorkNormalFormExact as Centered

import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNR650BadCollarRateWeightedWorkRound664Exact as R664

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- Generic complete-fibre complement identity.
------------------------------------------------------------------------

fixedOutputResidualPlusSignedA3IsRateSelf :
  (rho : Z3.FourierMode → ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    rate = Pair.cellRate rho
    work = Pair.cellWork mixed value
    n = Pair.natAsRational (length items)
    weighted = Pair.weightedWorkSum rate work items
    residual =
      Pair.rateSum rate items * Work.coherentWork mixed mixed
        + Pair.pairDifferenceWorkSum rate work items
    signedA3 =
      0ℚ - Vector.pairDifferenceVectorWorkSum rate mixed value items
  in
  residual + signedA3
  ≡ Pair.rateSum rate items * Work.coherentWork mixed mixed
fixedOutputResidualPlusSignedA3IsRateSelf
    rho S velocity cutoff output =
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    rate = Pair.cellRate rho
    work = Pair.cellWork mixed value
    n = Pair.natAsRational (length items)
    weighted = Pair.weightedWorkSum rate work items
    self = Work.coherentWork mixed mixed
    rateTotal = Pair.rateSum rate items
    pairDiff = Pair.pairDifferenceWorkSum rate work items
    residual = rateTotal * self + pairDiff
    signedA3 =
      0ℚ - Vector.pairDifferenceVectorWorkSum rate mixed value items

    residualMeaning :
      residual ≡ n * weighted
    residualMeaning =
      R664.fixedOutputRateSelfPlusPairDifferenceIsWeightedWork
        rho S velocity cutoff output

    signedA3Meaning :
      signedA3 ≡ n * (0ℚ - weighted) + rateTotal * self
    signedA3Meaning =
      Centered.fixedOutputSignedA3CenteredNormalForm
        rho S velocity cutoff output
  in
  trans
    (cong₂ _+_ residualMeaning signedA3Meaning)
    (solve (n ∷ weighted ∷ rateTotal ∷ self ∷ []))

------------------------------------------------------------------------
-- Same identity on the actual R661 trajectory.
------------------------------------------------------------------------

module LiveComplement
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
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf) where

  module Weighted = R664.LiveWeightedWork
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC integrationLinearity D

  module End = Endpoint.Endpoint
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC D

  signedA3At :
    Nat → Z3.FourierMode → Time → ℚ
  signedA3At cutoff output time =
    let
      items = Output.physicalOutputFiber cutoff output
      value = D1a.mixedProductCell End.S (End.velocityAt cutoff time)
      mixed = Weighted.Sp.mixedAt cutoff output time
      rate = Pair.cellRate (End.rateAt cutoff time)
    in
    0ℚ - Vector.pairDifferenceVectorWorkSum rate mixed value items

  residualAt :
    Nat → Z3.FourierMode → Time → ℚ
  residualAt cutoff output time =
    Weighted.Sp.rateSelfWorkAt cutoff output time
      + Weighted.Sp.pairDifferenceWorkAt cutoff output time

  liveResidualPlusSignedA3IsRateSelf :
    (cutoff : Nat) (output : Z3.FourierMode) (time : Time) →
    residualAt cutoff output time + signedA3At cutoff output time
    ≡ Weighted.Sp.rateSelfWorkAt cutoff output time
  liveResidualPlusSignedA3IsRateSelf cutoff output time =
    fixedOutputResidualPlusSignedA3IsRateSelf
      (End.rateAt cutoff time)
      End.S
      (End.velocityAt cutoff time)
      cutoff output

  integratedResidualPlusSignedA3 :
    Nat → Z3.FourierMode → Time → ℚ
  integratedResidualPlusSignedA3 cutoff output terminal =
    integrateTo
      (λ time →
        residualAt cutoff output time + signedA3At cutoff output time)
      terminal

  integratedRateSelf :
    Nat → Z3.FourierMode → Time → ℚ
  integratedRateSelf cutoff output terminal =
    integrateTo (Weighted.Sp.rateSelfWorkAt cutoff output) terminal

  liveSpacetimeResidualPlusSignedA3IsRateSelf :
    (cutoff : Nat) (output : Z3.FourierMode) (terminal : Time) →
    integratedResidualPlusSignedA3 cutoff output terminal
    ≡ integratedRateSelf cutoff output terminal
  liveSpacetimeResidualPlusSignedA3IsRateSelf
      cutoff output terminal =
    Energy.integrationCongruent integrationLinearity
      (liveResidualPlusSignedA3IsRateSelf cutoff output)
      terminal

------------------------------------------------------------------------
-- Status / sign-direction firewall.
------------------------------------------------------------------------

round666ResidualA3ComplementIdentityClosed : Bool
round666ResidualA3ComplementIdentityClosed = true

round666LiveResidualA3ComplementIdentityClosed : Bool
round666LiveResidualA3ComplementIdentityClosed = true

round666SpacetimeResidualA3ComplementIdentityClosed : Bool
round666SpacetimeResidualA3ComplementIdentityClosed = true

-- Existing centered-A3 machinery supplies an upper payment for SignedA3.
-- The residual complement would instead need a lower SignedA3 control, or a
-- separate payment of RateTotal * W(M,M).  Do not flip this direction.
round666A3UpperPaymentDirectlyPaysResidual : Bool
round666A3UpperPaymentDirectlyPaysResidual = false

round666SignedA3LowerPaymentClosed : Bool
round666SignedA3LowerPaymentClosed = false

round666RateSelfComplementPaymentClosed : Bool
round666RateSelfComplementPaymentClosed = false

round666CutoffUniformOutputAggregationClosed : Bool
round666CutoffUniformOutputAggregationClosed = false

round666IntroducesNewClayLeaf : Bool
round666IntroducesNewClayLeaf = false

round666C2Closed : Bool
round666C2Closed = false

round666ClayPromotion : Bool
round666ClayPromotion = false

round666ResidualA3ComplementIdentityClosedIsTrue :
  round666ResidualA3ComplementIdentityClosed ≡ true
round666ResidualA3ComplementIdentityClosedIsTrue = refl

round666LiveResidualA3ComplementIdentityClosedIsTrue :
  round666LiveResidualA3ComplementIdentityClosed ≡ true
round666LiveResidualA3ComplementIdentityClosedIsTrue = refl

round666SpacetimeResidualA3ComplementIdentityClosedIsTrue :
  round666SpacetimeResidualA3ComplementIdentityClosed ≡ true
round666SpacetimeResidualA3ComplementIdentityClosedIsTrue = refl

round666A3UpperPaymentDirectlyPaysResidualIsFalse :
  round666A3UpperPaymentDirectlyPaysResidual ≡ false
round666A3UpperPaymentDirectlyPaysResidualIsFalse = refl

round666SignedA3LowerPaymentClosedIsFalse :
  round666SignedA3LowerPaymentClosed ≡ false
round666SignedA3LowerPaymentClosedIsFalse = refl

round666RateSelfComplementPaymentClosedIsFalse :
  round666RateSelfComplementPaymentClosed ≡ false
round666RateSelfComplementPaymentClosedIsFalse = refl

round666CutoffUniformOutputAggregationClosedIsFalse :
  round666CutoffUniformOutputAggregationClosed ≡ false
round666CutoffUniformOutputAggregationClosedIsFalse = refl

round666IntroducesNewClayLeafIsFalse :
  round666IntroducesNewClayLeaf ≡ false
round666IntroducesNewClayLeafIsFalse = refl

round666C2ClosedIsFalse :
  round666C2Closed ≡ false
round666C2ClosedIsFalse = refl

round666ClayPromotionIsFalse :
  round666ClayPromotion ≡ false
round666ClayPromotionIsFalse = refl
