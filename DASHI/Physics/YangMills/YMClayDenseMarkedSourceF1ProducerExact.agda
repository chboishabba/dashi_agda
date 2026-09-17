{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayDenseMarkedSourceF1ProducerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanMarkedLogPartitionConnectedCorrelationCompilerExact as Marked
import DASHI.Physics.YangMills.BalabanStepVMarkedSourceDirectClusteringProducerCurrentExact as Current
import DASHI.Physics.YangMills.YMClayR295MarkedSourceAdapterExact as R295Adapter

------------------------------------------------------------------------
-- DENSE PHYSICAL F1 PRODUCER FROM THE EXISTING MARKED-SOURCE COMPILER
--
-- This is the source-native counterpart of `YMClayDenseL2CorrelationBidiParityExact`.
-- The latter says that a uniform connected-correlation estimate on a dense
-- physical L2_0 algebra extends to the full vacuum complement.  The present
-- owner removes one more fake leaf: the dense correlation estimate itself need
-- not be postulated independently once the existing marked-source response and
-- separation-decay producer are on the SAME literal Wilson observables.
--
-- Existing compiler mathematics:
--
--   mixed d_A d_B log Z
--       = <AB> - <A><B>
--       = connectedCorrelation A B
--
-- and
--
--   |mixed d_A d_B log Z| <= decayEnvelope(distance A B)
--       ->
--   |connectedCorrelation A B| <= decayEnvelope(distance A B).
--
-- R295 is now adapted directly to this generic marked-source ABI by
-- `YMClayR295MarkedSourceAdapterExact`, so the selected marked response/decay
-- producer is not an additional F1 leaf after the canonical R338/R339 -> R295
-- route.  The remaining theorem-bearing weld is the SAME-OBJECT dense/L2
-- normalization:
--
--   decayEnvelope(distance (A_psi) (A_psi))
--       = c_k * ||psi||_2^2
--
-- together with the fact that the selected local/cylinder family is dense in
-- the literal physical vacuum complement.
------------------------------------------------------------------------

record DenseMarkedSourceF1Weld
    {Observable Scalar Bound Distance : Set}
    (response : Marked.MarkedTwoSourceResponse Observable Scalar)
    (producer : Marked.SeparationDecayProducer response) : Set₁ where
  field
    DensePhysicalObservable : Set
    asMarkedObservable : DensePhysicalObservable → Observable

    DenseInPhysicalVacuumComplement : Set
    denseInPhysicalVacuumComplement : DenseInPhysicalVacuumComplement

    SameLiteralWilsonSliceObservable : Set
    sameLiteralWilsonSliceObservable : SameLiteralWilsonSliceObservable

    f1TargetBound : DensePhysicalObservable → Bound

    sourceEnvelopeIsPhysicalF1Target :
      (psi : DensePhysicalObservable) →
      Marked.decayEnvelope producer
        (Marked.distance producer
          (asMarkedObservable psi)
          (asMarkedObservable psi))
      ≡ f1TargetBound psi

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
        (asMarkedObservable weld psi)
        (asMarkedObservable weld psi)))
    (f1TargetBound weld psi)
denseMarkedSourceCorrelationPaysF1 {response = response} {producer = producer} weld psi =
  subst
    (λ upper →
      Marked.LessEqual producer
        (Marked.absoluteValue producer
          (Marked.connectedCorrelation response
            (asMarkedObservable weld psi)
            (asMarkedObservable weld psi)))
        upper)
    (sourceEnvelopeIsPhysicalF1Target weld psi)
    (Marked.connectedCorrelationDecayFromMarkedSource producer
      (asMarkedObservable weld psi)
      (asMarkedObservable weld psi))

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

-- R295 now definitionally supplies the generic response/decay producer used by
-- this module.  The underlying selected-J localization can remain conditional,
-- but there is no second adapter/producer theorem to pay afterwards.
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
