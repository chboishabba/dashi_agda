{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayDenseMarkedSourceF1ProducerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanMarkedLogPartitionConnectedCorrelationCompilerExact as Marked
import DASHI.Physics.YangMills.BalabanStepVMarkedSourceDirectClusteringProducerCurrentExact as Current
import DASHI.Physics.YangMills.YMClayR295MarkedSourceAdapterExact as R295Adapter

------------------------------------------------------------------------
-- DENSE PHYSICAL F1 PRODUCER FROM THE EXISTING MARKED-SOURCE COMPILER
--
-- Corrected min-cut:
--
--   * F1 is a TWO-SLICE transfer/correlation statement.  The source pair must
--     therefore be the selected left observable and its translated/right-slice
--     partner, not the same marked observable inserted twice.
--
--   * The physical target only needs a one-sided calibration
--
--         decayEnvelope(left,right) <= c_k ||psi||^2,
--
--     not equality of the source envelope with that target.
--
-- R295 still supplies the generic marked response and separation-decay theorem;
-- this owner only composes that decay with the translated-pair physical
-- calibration and density in the literal Wilson vacuum complement.
------------------------------------------------------------------------

record DenseMarkedSourceF1Weld
    {Observable Scalar Bound Distance : Set}
    (response : Marked.MarkedTwoSourceResponse Observable Scalar)
    (producer : Marked.SeparationDecayProducer response) : Set₁ where
  field
    DensePhysicalObservable : Set

    -- Selected two-slice source pair.  For the R310/R315 Wilson-cylinder route
    -- these are intended to be decode(psi) and timeTranslate(psi,1).
    leftMarkedObservable :
      DensePhysicalObservable → Observable
    rightMarkedObservable :
      DensePhysicalObservable → Observable

    DenseInPhysicalVacuumComplement : Set
    denseInPhysicalVacuumComplement : DenseInPhysicalVacuumComplement

    SameLiteralWilsonTwoSliceObservables : Set
    sameLiteralWilsonTwoSliceObservables :
      SameLiteralWilsonTwoSliceObservables

    f1TargetBound : DensePhysicalObservable → Bound

    -- Standard order/compiler input.  R295 realizes LessEqual pointwise by
    -- rational <=, where this is ordinary transitivity.
    lessEqualTransitive :
      ∀ {lower middle upper} →
      Marked.LessEqual producer lower middle →
      Marked.LessEqual producer middle upper →
      Marked.LessEqual producer lower upper

    -- Least-privilege physical normalization: only an upper is required.
    sourceEnvelopeBelowPhysicalF1Target :
      (psi : DensePhysicalObservable) →
      Marked.LessEqual producer
        (Marked.decayEnvelope producer
          (Marked.distance producer
            (leftMarkedObservable psi)
            (rightMarkedObservable psi)))
        (f1TargetBound psi)

open DenseMarkedSourceF1Weld public

denseMarkedSourceCorrelationPaysF1 :
  ∀ {Observable Scalar Bound Distance}
    {response : Marked.MarkedTwoSourceResponse Observable Scalar}
    {producer : Marked.SeparationDecayProducer response}
    (weld : DenseMarkedSourceF1Weld response producer)
    (psi : DensePhysicalObservable weld) →
  Marked.LessEqual producer
    (Marked.absoluteValue producer
      (Marked.connectedCorrelation response
        (leftMarkedObservable weld psi)
        (rightMarkedObservable weld psi)))
    (f1TargetBound weld psi)
denseMarkedSourceCorrelationPaysF1 {response = response} {producer = producer} weld psi =
  lessEqualTransitive weld
    (Marked.connectedCorrelationDecayFromMarkedSource producer
      (leftMarkedObservable weld psi)
      (rightMarkedObservable weld psi))
    (sourceEnvelopeBelowPhysicalF1Target weld psi)

------------------------------------------------------------------------
-- Frontier bookkeeping.
------------------------------------------------------------------------

denseMarkedSourceDecayCompilerOwned : Bool
denseMarkedSourceDecayCompilerOwned = true

denseMarkedSourceDecayCompilerOwnedIsTrue :
  denseMarkedSourceDecayCompilerOwned ≡ true
denseMarkedSourceDecayCompilerOwnedIsTrue = refl

fullJointDensityLinfinityRequiredByDenseMarkedRoute : Bool
fullJointDensityLinfinityRequiredByDenseMarkedRoute = false

fullJointDensityLinfinityRequiredByDenseMarkedRouteIsFalse :
  fullJointDensityLinfinityRequiredByDenseMarkedRoute ≡ false
fullJointDensityLinfinityRequiredByDenseMarkedRouteIsFalse = refl

sameObjectEnvelopeToPhysicalL2NormalizationStillRequired : Bool
sameObjectEnvelopeToPhysicalL2NormalizationStillRequired = true

sameObjectEnvelopeToPhysicalL2NormalizationStillRequiredIsTrue :
  sameObjectEnvelopeToPhysicalL2NormalizationStillRequired ≡ true
sameObjectEnvelopeToPhysicalL2NormalizationStillRequiredIsTrue = refl

sameObservableInsertedTwiceIsCorrectF1Pair : Bool
sameObservableInsertedTwiceIsCorrectF1Pair = false

sameObservableInsertedTwiceIsCorrectF1PairIsFalse :
  sameObservableInsertedTwiceIsCorrectF1Pair ≡ false
sameObservableInsertedTwiceIsCorrectF1PairIsFalse = refl

translatedTwoSlicePairRequired : Bool
translatedTwoSlicePairRequired = true

translatedTwoSlicePairRequiredIsTrue :
  translatedTwoSlicePairRequired ≡ true
translatedTwoSlicePairRequiredIsTrue = refl

envelopeEqualityRequired : Bool
envelopeEqualityRequired = false

envelopeEqualityRequiredIsFalse :
  envelopeEqualityRequired ≡ false
envelopeEqualityRequiredIsFalse = refl

oneSidedEnvelopeUpperSuffices : Bool
oneSidedEnvelopeUpperSuffices = true

oneSidedEnvelopeUpperSufficesIsTrue :
  oneSidedEnvelopeUpperSuffices ≡ true
oneSidedEnvelopeUpperSufficesIsTrue = refl

selectedPhysicalMarkedDecayProducerStillRequired : Bool
selectedPhysicalMarkedDecayProducerStillRequired = false

selectedPhysicalMarkedDecayProducerStillRequiredIsFalse :
  selectedPhysicalMarkedDecayProducerStillRequired ≡ false
selectedPhysicalMarkedDecayProducerStillRequiredIsFalse = refl

selectedJSourceApplicationLevel : ProofLevel
selectedJSourceApplicationLevel =
  Current.leastPrivilegeSelectedJSameObjectLocalizationLevel

selectedJPhysicalApplicabilityLevel : ProofLevel
selectedJPhysicalApplicabilityLevel =
  Current.selectedJApplicabilityPhysicalLevel

r295MarkedSourceAdapterLevel : ProofLevel
r295MarkedSourceAdapterLevel = R295Adapter.r295MarkedSourceAdapterLevel

denseMarkedSourceF1CompilerLevel : ProofLevel
denseMarkedSourceF1CompilerLevel = conditional

sameObjectEnvelopeNormalizationLevel : ProofLevel
sameObjectEnvelopeNormalizationLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
