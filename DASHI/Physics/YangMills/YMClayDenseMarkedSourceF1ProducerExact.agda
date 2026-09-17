{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayDenseMarkedSourceF1ProducerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanMarkedLogPartitionConnectedCorrelationCompilerExact as Marked
import DASHI.Physics.YangMills.BalabanStepVMarkedSourceDirectClusteringProducerCurrentExact as Current

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
-- For F1 we choose a dense physical vacuum algebra D and set A=B=psi.  The
-- only additional theorem-bearing weld is then the SAME-OBJECT normalization
--
--   decayEnvelope(distance (A_psi) (A_psi))
--       = c_k * ||psi||_2^2
--
-- (or any definitionally/equationally identical representation of that target).
-- The generic `Bound` carrier below deliberately does not manufacture scalar
-- multiplication; `f1TargetBound` is the already-normalized physical target.
--
-- This is important proof-search compression:
--
--   selected CMP116/CMP109 marked decay
--   + literal Wilson / dense-L2 same-object map
--   + envelope-to-c_k||.||^2 normalization
--      -> dense F1 connected-correlation estimate
--      -> existing dense<->full L2_0 compiler
--      -> transfer decorrelator.
--
-- Therefore a full adjacent-slice Radon--Nikodym L-infinity defect is NOT a
-- primitive requirement on this route.
------------------------------------------------------------------------

record DenseMarkedSourceF1Weld
    {Observable Scalar Bound Distance : Set}
    (response : Marked.MarkedTwoSourceResponse Observable Scalar)
    (producer : Marked.SeparationDecayProducer response) : Set₁ where
  field
    -- Source-native cylinder/local observables selected as the dense physical
    -- vacuum-complement test algebra.
    DensePhysicalObservable : Set
    asMarkedObservable : DensePhysicalObservable → Observable

    -- These witnesses are intentionally explicit.  They stop a generic marked
    -- source family from being silently promoted to the literal Wilson L2_0
    -- carrier merely because its theorem has the right inequality shape.
    DenseInPhysicalVacuumComplement : Set
    denseInPhysicalVacuumComplement : DenseInPhysicalVacuumComplement

    SameLiteralWilsonSliceObservable : Set
    sameLiteralWilsonSliceObservable : SameLiteralWilsonSliceObservable

    -- Physical F1 target for each dense observable.  Semantically this is
    -- c_k * ||psi||_2^2 at the selected cutoff/trajectory point; the cutoff may
    -- already be closed over by `response`/`producer`.
    f1TargetBound : DensePhysicalObservable → Bound

    -- The sole normalization/application weld needed after marked-source decay:
    -- identify the source envelope with the physical L2-normalized F1 target.
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

selectedPhysicalMarkedDecayProducerStillRequired : Bool
selectedPhysicalMarkedDecayProducerStillRequired = true

selectedPhysicalMarkedDecayProducerStillRequiredIsTrue :
  selectedPhysicalMarkedDecayProducerStillRequired ≡ true
selectedPhysicalMarkedDecayProducerStillRequiredIsTrue = refl

-- Current source-facing selected-J payment already isolated by the canonical
-- marked-source producer.  We reference it rather than creating a parallel
-- localization obligation.
selectedJSourceApplicationLevel : ProofLevel
selectedJSourceApplicationLevel =
  Current.leastPrivilegeSelectedJSameObjectLocalizationLevel

selectedJPhysicalApplicabilityLevel : ProofLevel
selectedJPhysicalApplicabilityLevel =
  Current.selectedJApplicabilityPhysicalLevel

-- Source-written in this connector session.  Promote only after an exact-head
-- Agda kernel receipt; no CI/kernel claim is manufactured here.
denseMarkedSourceF1CompilerLevel : ProofLevel
denseMarkedSourceF1CompilerLevel = conditional

sameObjectEnvelopeNormalizationLevel : ProofLevel
sameObjectEnvelopeNormalizationLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
