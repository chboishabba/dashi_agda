{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNCanonicalOrbitResolvedExternalScalarRound623Exact where

------------------------------------------------------------------------
-- ROUND623 / CANONICAL ORBIT-RESOLVED EXTERNAL SCALAR CONSUMER
--
-- R622 rewrites the COMPLETE fixed-output external R573 nested vector fold
-- onto a canonical orbit-resolved carrier, including the fixed-orbit
-- multiplicity correction.
--
-- The live R545/R573 consumer pairs that force fold with the spectator's
-- literal double mixed cell BEFORE any norm.  Therefore the remaining
-- representation seam is just congruence of the real Hermitian pairing:
--
--   Re < ExternalFold_k , D_beta >
--     = Re < CanonicalOrbitResolvedExternalFold_k , D_beta >.
--
-- This file closes exactly that scalar same-object port.  It introduces no
-- absolute value, shell estimate, spacetime integration or cutoff-uniform
-- payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNR573SelfExternalNestedCompanionSplitRound613Exact as R613
import DASHI.Physics.Closure.NSTriadKNCanonicalOrbitResolvedExternalNestedFoldRound622Exact as R622

F : C3.RealField _
F = Rational.rationalRealField

module CanonicalExternalScalar623
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (W : R294.SwapInvariantCellWeight F)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Split =
    R613.NestedNetworkSplit W S L H system velocityTransverse

  module Canonical =
    R622.CanonicalExternalNested W S L H system velocityTransverse

  fibre :
    Z3.FourierMode →
    List Physical.PhysicalTriadIncidence
  fibre = Canonical.fibre

  externalFold :
    Z3.FourierMode → C3.Complex3 F
  externalFold output =
    R224.foldVector
      Split.externalNestedWeightedCompanionCell
      (fibre output)

  canonicalExternalFold :
    Z3.FourierMode → C3.Complex3 F
  canonicalExternalFold =
    Canonical.canonicalExternalNestedFold

  externalScalar :
    Z3.FourierMode →
    C3.Complex3 F →
    ℚ
  externalScalar output test =
    R179.realHermitianCross (externalFold output) test

  canonicalExternalScalar :
    Z3.FourierMode →
    C3.Complex3 F →
    ℚ
  canonicalExternalScalar output test =
    R179.realHermitianCross (canonicalExternalFold output) test

  externalScalarIsCanonical :
    (output : Z3.FourierMode) →
    (test : C3.Complex3 F) →
    externalScalar output test
    ≡ canonicalExternalScalar output test
  externalScalarIsCanonical output test =
    cong
      (λ force → R179.realHermitianCross force test)
      (Canonical.fixedOutputExternalNestedFoldIsCanonical output)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round623ExternalFoldHermitianScalarSameObjectClosed : Bool
round623ExternalFoldHermitianScalarSameObjectClosed = true

round623CanonicalOrbitResolvedCarrierReachesScalarConsumer : Bool
round623CanonicalOrbitResolvedCarrierReachesScalarConsumer = true

round623RequiresLegacyR112WitnessFamily : Bool
round623RequiresLegacyR112WitnessFamily = false

round623IntroducesNormOrAbsoluteValue : Bool
round623IntroducesNormOrAbsoluteValue = false

round623IntroducesEstimate : Bool
round623IntroducesEstimate = false

round623ExternalScalarAnalyticPaymentClosed : Bool
round623ExternalScalarAnalyticPaymentClosed = false

round623ExternalFoldHermitianScalarSameObjectClosedIsTrue :
  round623ExternalFoldHermitianScalarSameObjectClosed ≡ true
round623ExternalFoldHermitianScalarSameObjectClosedIsTrue = refl

round623CanonicalOrbitResolvedCarrierReachesScalarConsumerIsTrue :
  round623CanonicalOrbitResolvedCarrierReachesScalarConsumer ≡ true
round623CanonicalOrbitResolvedCarrierReachesScalarConsumerIsTrue = refl

round623RequiresLegacyR112WitnessFamilyIsFalse :
  round623RequiresLegacyR112WitnessFamily ≡ false
round623RequiresLegacyR112WitnessFamilyIsFalse = refl

round623IntroducesNormOrAbsoluteValueIsFalse :
  round623IntroducesNormOrAbsoluteValue ≡ false
round623IntroducesNormOrAbsoluteValueIsFalse = refl

round623IntroducesEstimateIsFalse :
  round623IntroducesEstimate ≡ false
round623IntroducesEstimateIsFalse = refl

round623ExternalScalarAnalyticPaymentClosedIsFalse :
  round623ExternalScalarAnalyticPaymentClosed ≡ false
round623ExternalScalarAnalyticPaymentClosedIsFalse = refl
