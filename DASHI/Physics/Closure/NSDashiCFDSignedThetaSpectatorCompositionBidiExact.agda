module DASHI.Physics.Closure.NSDashiCFDSignedThetaSpectatorCompositionBidiExact where

------------------------------------------------------------------------
-- DASHICFD SIGNED-THETA x SPECTATOR-COMMUTATOR COMPOSITION BIDI
--
-- PURPOSE
-- -------
-- Record the cross-repository snowball that was hidden by vocabulary changes.
--
-- June 2026 dashiCFD / early DASHI owners separately contained:
--
--   * the fixed-cutoff tail-flux / dissipation theta diagnostic;
--   * the explicit instruction to isolate nonlinear flux and take absolute
--     value only later;
--   * an involution-aware signed cross-shell flip audit that pairs opposite
--     flows before measuring the residual;
--   * a generic strict-margin / theta<1 conditional absorption grammar.
--
-- The later Fourier proof search independently reconstructed the same ordering:
--
--   signed/helical cancellation
--     -> preserve the literal nonseparable spectator resolvent
--     -> aggregate the signed spectator row
--     -> only then estimate / compare with dissipation.
--
-- This module records that methodological and compositional correspondence.
-- It does NOT identify empirical packet signs with Fourier helicity signs, does
-- NOT turn runtime theta evidence into an analytic theorem, and introduces no
-- Clay/regularity promotion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.DashiCFDThetaRuntimeDiagnosticReceipt as CFDTheta
import DASHI.Physics.Closure.ClaySprintFiftyOneSignedTernaryFlipAuditReceipt as CFDSign
import DASHI.Physics.Closure.NSTailFluxIdentityAnalyticTargetReceipt as TailIdentity
import DASHI.Physics.Closure.NSTailFluxAbsorptionMarginReceipt as TailMargin
import DASHI.Physics.Closure.StrictMarginImpliesAbsorptionReceipt as StrictMargin
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventNestedCommutatorBidiExact as SpectatorNested

------------------------------------------------------------------------
-- Historical source coordinates.
------------------------------------------------------------------------

data CompositionStage : Set where
  thetaBarrierDiagnosticFirst : CompositionStage
  signedInvolutionCorrectionSecond : CompositionStage
  analyticAbsoluteValueDelayed : CompositionStage
  strictMarginAbsorptionGrammar : CompositionStage
  FourierSignedCancellation : CompositionStage
  literalSpectatorResolvent : CompositionStage
  signedSpectatorAggregation : CompositionStage
  dissipationComparisonLast : CompositionStage

historicalCompositionOrder : List CompositionStage
historicalCompositionOrder =
  thetaBarrierDiagnosticFirst
  ∷ signedInvolutionCorrectionSecond
  ∷ analyticAbsoluteValueDelayed
  ∷ strictMarginAbsorptionGrammar
  ∷ []

preferredAnalyticCompositionOrder : List CompositionStage
preferredAnalyticCompositionOrder =
  FourierSignedCancellation
  ∷ literalSpectatorResolvent
  ∷ signedSpectatorAggregation
  ∷ dissipationComparisonLast
  ∷ []

------------------------------------------------------------------------
-- Provenance / chronology strings.  These are documentary coordinates, not
-- executable time proofs.
------------------------------------------------------------------------

cfdThetaReceiptDateBrisbane : String
cfdThetaReceiptDateBrisbane = "2026-06-02 12:58 +10"

cfdThetaSweepDateBrisbane : String
cfdThetaSweepDateBrisbane = "2026-06-04 00:15 +10"

cfdSignedFlipDateBrisbane : String
cfdSignedFlipDateBrisbane = "2026-06-04 14:13 +10"

cfdSignedFlipAgdaReceiptDateBrisbane : String
cfdSignedFlipAgdaReceiptDateBrisbane = "2026-06-04 18:50 +10"

------------------------------------------------------------------------
-- BIDI interpretation.
------------------------------------------------------------------------

-- The early analytic target already says the nonlinear flux should be isolated
-- before the absolute value is introduced.  The later Fourier lane realizes
-- the analogous policy by performing the R294/R573 commutator collapse before
-- norm or Schur/Cotlar majorization.

data CompositionOrderReading : Set where
  positiveMajorantTooEarly : CompositionOrderReading
  preserveSignedCarrierUntilAfterCancellation : CompositionOrderReading
  compareResidualWithDissipationOnlyAfterSignedAggregation : CompositionOrderReading

preferredCompositionReading : CompositionOrderReading
preferredCompositionReading =
  preserveSignedCarrierUntilAfterCancellation

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data EmpiricalPacketSignedCarrier : Set where
  empiricalPacketSignedCarrier : EmpiricalPacketSignedCarrier

data FourierHelicalSignedCarrier : Set where
  fourierHelicalSignedCarrier : FourierHelicalSignedCarrier

packetSignIsFourierHelicity : Bool
packetSignIsFourierHelicity = false

runtimeThetaIsAnalyticTheta : Bool
runtimeThetaIsAnalyticTheta = false

cfdDiagnosticProvesR406 : Bool
cfdDiagnosticProvesR406 = false

------------------------------------------------------------------------
-- Audited composition state.
------------------------------------------------------------------------

-- The June owners exist and preserve the relevant semantics, but the audited
-- default-branch search did not locate a single owner importing the Sprint-51
-- signed receipt together with the dashiCFD theta runtime receipt as one signed
-- theta barrier theorem.
auditedDefaultBranchDirectSignedThetaOwnerFound : Bool
auditedDefaultBranchDirectSignedThetaOwnerFound = false

-- The modern branch now does instantiate the literal spectator Cauchy resolvent
-- weight directly into the exact nested weighted commutator before norms.
modernSpectatorResolventNestedCompositionPresent : Bool
modernSpectatorResolventNestedCompositionPresent = true

-- The remaining desired composition is to retain the beta-indexed signed rows
-- through spacetime aggregation and only then use the strict-margin /
-- dissipation comparison.  This module records the route; it does not pretend
-- that analytic payment has been proved here.
signedSpectatorSpacetimePaymentClosedHere : Bool
signedSpectatorSpacetimePaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

packetSignIsFourierHelicityIsFalse : packetSignIsFourierHelicity ≡ false
packetSignIsFourierHelicityIsFalse = refl

runtimeThetaIsAnalyticThetaIsFalse : runtimeThetaIsAnalyticTheta ≡ false
runtimeThetaIsAnalyticThetaIsFalse = refl

modernSpectatorResolventNestedCompositionPresentIsTrue :
  modernSpectatorResolventNestedCompositionPresent ≡ true
modernSpectatorResolventNestedCompositionPresentIsTrue = refl

signedSpectatorSpacetimePaymentClosedHereIsFalse :
  signedSpectatorSpacetimePaymentClosedHere ≡ false
signedSpectatorSpacetimePaymentClosedHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
