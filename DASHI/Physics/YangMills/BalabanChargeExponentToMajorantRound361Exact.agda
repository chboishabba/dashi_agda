{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanChargeExponentToMajorantRound361Exact where

------------------------------------------------------------------------
-- ROUND361 / EXPONENT CHARGE -> R354 MAJORANT WITHOUT HIDING SAME-OBJECT WELDS
--
-- R355 produces the source-shaped exponent inequality
--
--   requiredCharge <= combinedCharge.
--
-- R354 consumes a pointwise majorant inequality
--
--   rawMarkedMajorant <= chargedMajorant.
--
-- Since the source majorants are exponential decays, the direction reverses
-- under x |-> exp(-x).  That order theorem is ordinary real analysis, not new
-- Yang--Mills mathematics.  The actual YM/application work is identifying
-- R354's two majorants with the corresponding exponentials on the SAME walk /
-- localization carrier.
--
-- This owner therefore keeps three coordinates distinct:
--   * standard negative-exponential antitonicity;
--   * raw-majorant same-object attachment;
--   * charged-majorant same-object attachment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record NegativeExponentialOrderAuthority : Set₁ where
  field
    negativeExp : ℝ → ℝ
    antitone : ∀ {small large} →
      small ≤ℝ large →
      negativeExp large ≤ℝ negativeExp small

open NegativeExponentialOrderAuthority public

record ChargeExponentMajorantAttachment
    (order : NegativeExponentialOrderAuthority) : Set₁ where
  field
    requiredCharge combinedCharge : ℝ
    rawMarkedMajorant chargedMajorant : ℝ

    requiredChargeBelowCombinedCharge :
      requiredCharge ≤ℝ combinedCharge

    rawMarkedMajorantIsCombinedExponential :
      rawMarkedMajorant ≡ negativeExp order combinedCharge

    chargedMajorantIsRequiredExponential :
      chargedMajorant ≡ negativeExp order requiredCharge

open ChargeExponentMajorantAttachment public

rawMarkedBelowCharged :
  (order : NegativeExponentialOrderAuthority) →
  (dataSet : ChargeExponentMajorantAttachment order) →
  rawMarkedMajorant dataSet ≤ℝ chargedMajorant dataSet
rawMarkedBelowCharged order dataSet =
  subst
    (λ raw → raw ≤ℝ chargedMajorant dataSet)
    (sym (rawMarkedMajorantIsCombinedExponential dataSet))
    (subst
      (λ charged →
        negativeExp order (combinedCharge dataSet) ≤ℝ charged)
      (sym (chargedMajorantIsRequiredExponential dataSet))
      (antitone order (requiredChargeBelowCombinedCharge dataSet)))

------------------------------------------------------------------------
-- Pareto/source accounting.
------------------------------------------------------------------------

negativeExponentialAntitonicityLevel : ProofLevel
negativeExponentialAntitonicityLevel = standardImported

rawMarkedMajorantExponentAttachmentLevel : ProofLevel
rawMarkedMajorantExponentAttachmentLevel = conditional

chargedMajorantExponentAttachmentLevel : ProofLevel
chargedMajorantExponentAttachmentLevel = conditional

chargeToMajorantTransportCompilerLevel : ProofLevel
chargeToMajorantTransportCompilerLevel = machineChecked

freshYMExponentialInequalityRequired : Bool
freshYMExponentialInequalityRequired = false

freshYMExponentialInequalityRequiredIsFalse :
  freshYMExponentialInequalityRequired ≡ false
freshYMExponentialInequalityRequiredIsFalse = refl

sourceChargeAutomaticallyIdentifiesR354Majorants : Bool
sourceChargeAutomaticallyIdentifiesR354Majorants = false

sourceChargeAutomaticallyIdentifiesR354MajorantsIsFalse :
  sourceChargeAutomaticallyIdentifiesR354Majorants ≡ false
sourceChargeAutomaticallyIdentifiesR354MajorantsIsFalse = refl

record Round361Boundary : Set where
  constructor round361-boundary
  field
    exponentialOrderIsStandardAnalysis : Bool
    exponentialOrderIsStandardAnalysisIsTrue :
      exponentialOrderIsStandardAnalysis ≡ true

    rawMajorantAttachmentStillOpen : Bool
    rawMajorantAttachmentStillOpenIsTrue :
      rawMajorantAttachmentStillOpen ≡ true

    chargedMajorantAttachmentStillOpen : Bool
    chargedMajorantAttachmentStillOpenIsTrue :
      chargedMajorantAttachmentStillOpen ≡ true

canonicalRound361Boundary : Round361Boundary
canonicalRound361Boundary =
  round361-boundary true refl true refl true refl

round361FrontierRefinementLevel : ProofLevel
round361FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
