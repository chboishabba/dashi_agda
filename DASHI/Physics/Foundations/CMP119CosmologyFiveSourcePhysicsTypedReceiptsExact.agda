{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyFiveSourcePhysicsTypedReceiptsExact where

------------------------------------------------------------------------
-- TYPED TERMINAL SOURCE-PHYSICS RECEIPTS.
--
-- This replaces the earlier generic `Set` sockets by the exact mathematical
-- shapes consumed at the five-leaf Pareto frontier.  It deliberately does not
-- manufacture inhabitants: each receipt is evidence-bearing data whose source
-- meaning is fixed outside the receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _<_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedReadoutCovarianceExact as Readout
import DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact as Axis
import DASHI.Physics.Foundations.CMP119CosmologyR144R109DirectTailAnchorExact as Direct
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Hyper
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Additive
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

------------------------------------------------------------------------
-- A1: differentiated change-of-variables / signed B4 readout covariance.
------------------------------------------------------------------------

record A1R144SignedB4SourceReceipt
    (Background : Set)
    (actBackground : Hyper.HypercubicGenerator → Background → Background)
    (readout : Background → K.SymmetricTensorComponent4 → ℝ)
    : Set₁ where
  field
    signedReadoutCovariant :
      ∀ generator background component →
      Readout.signedComponentReadout
        (readout (actBackground generator background))
        (Signed.actSignedComponent
          (Axis.hypercubicSignedAxisAction generator) component)
      ≡
      readout background component

open A1R144SignedB4SourceReceipt public

------------------------------------------------------------------------
-- A2: semantics of the ONE selected source-native R109 insertion.
--
-- `Meaning` is an argument, not a field.  Thus a receipt cannot close A2 by
-- inventing its own semantics relation after seeing the selected observable.
------------------------------------------------------------------------

record A2SelectedR109InsertionSemanticsReceipt
    (source : R109.SourceNativeStressScaleCauchy)
    (Configuration : Set)
    (Meaning :
      Source.LocalInsertionPair (R109.source source) →
      (Configuration → ℝ) → Set)
    : Set₁ where
  field
    selectedObservable : Configuration → ℝ
    selectedInsertionHasMeaning :
      Meaning
        (Source.pair (R109.stressInsertion source))
        selectedObservable

open A2SelectedR109InsertionSemanticsReceipt public

------------------------------------------------------------------------
-- B1: exact canonical direct-tail attachment.
------------------------------------------------------------------------

B1AbsoluteSameSequenceDirectTailReceipt :
  (embedding : Additive.OrderedAdditiveRationalRealEmbedding) →
  (source : R109.SourceNativeStressScaleCauchy) →
  (completedRationalResponse finiteRationalDGamma : ℚ) →
  Nat → Set₁
B1AbsoluteSameSequenceDirectTailReceipt =
  Direct.DirectR144R109TailAnchor

------------------------------------------------------------------------
-- B2: source-native strict Eq.(2.23) envelope actually consumed by the sign
-- route.  Source metric-family calibration must produce these exact scalars;
-- the receipt only records the resulting strict physical inequality.
------------------------------------------------------------------------

record B2Eq223StrictSourceEnvelopeReceipt
    (combinedERBUpper vacuumCoefficient tail : ℚ) : Set where
  field
    strictNegativeEnvelope :
      (combinedERBUpper + vacuumCoefficient) + tail < 0ℚ

open B2Eq223StrictSourceEnvelopeReceipt public

------------------------------------------------------------------------
-- C: Pareto-minimal anomaly fallback.  Equality is deliberately not required.
------------------------------------------------------------------------

record CR136ToSelectedAnomalyDominanceReceipt
    (embedding : Embed.OrderedRationalRealEmbedding)
    (r136Response : ℚ)
    (selectedAnomalyTrace : ℝ)
    : Set₁ where
  field
    embeddedR136BelowSelectedAnomaly :
      Embed.embed embedding r136Response ≤ℝ selectedAnomalyTrace

open CR136ToSelectedAnomalyDominanceReceipt public

------------------------------------------------------------------------
-- Frontier audit.
------------------------------------------------------------------------

typedSourcePhysicsReceiptCount : Nat
typedSourcePhysicsReceiptCount = 5

genericSetValuedReceiptSocketsRemain : Bool
genericSetValuedReceiptSocketsRemain = false

a1ReceiptIsExactSignedB4Covariance : Bool
a1ReceiptIsExactSignedB4Covariance = true

a2MeaningRelationIsExternalParameter : Bool
a2MeaningRelationIsExternalParameter = true

b1ReceiptReusesCanonicalDirectTailAnchor : Bool
b1ReceiptReusesCanonicalDirectTailAnchor = true

b2ReceiptIsStrictCombinedVacuumTailEnvelope : Bool
b2ReceiptIsStrictCombinedVacuumTailEnvelope = true

cReceiptIsOneSidedAnomalyDominance : Bool
cReceiptIsOneSidedAnomalyDominance = true

currentSafeTheoryPaysAllFiveTypedReceipts : Bool
currentSafeTheoryPaysAllFiveTypedReceipts = false
