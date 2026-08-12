module DASHI.Core.ConsumerIndexedRelevanceMeasure where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Consumer-indexed relevance measure.
--
-- The distinguished unit is a normalization convention for the represented
-- epistemic/task carrier.  It is deliberately not an objective-world truth
-- value and not a claim that the represented carrier exhausts reality.
------------------------------------------------------------------------

data EpistemicMassKind : Set where
  candidateWeightMass : EpistemicMassKind
  representedProvenanceMass : EpistemicMassKind
  consumerRelevanceMass : EpistemicMassKind

record ConsumerIndexedRelevanceMeasure
    (Consumer Region Mass : Set) : Set where
  constructor consumerIndexedRelevanceMeasure
  field
    massKind : EpistemicMassKind
    wholeRegion : Region
    zeroMass unitMass : Mass
    combineMass : Mass → Mass → Mass
    relevanceMass : Consumer → Region → Mass
    normalizedWhole :
      (consumer : Consumer) →
      relevanceMass consumer wholeRegion ≡ unitMass

open ConsumerIndexedRelevanceMeasure public

------------------------------------------------------------------------
-- Open-world accounting.
--
-- A runtime projection may retain one region, preserve a model-internal
-- residual, and explicitly reserve mass for possibilities outside the current
-- represented carrier.  The accounting equation says only that the chosen
-- epistemic measure has been normalized and accounted for.
------------------------------------------------------------------------

record OpenWorldMassAccounting
    {Consumer Region Mass : Set}
    (measure : ConsumerIndexedRelevanceMeasure Consumer Region Mass)
    (consumer : Consumer) : Set where
  constructor openWorldMassAccounting
  field
    retainedRegion : Region
    representedResidualRegion : Region
    outsideModelRegion : Region
    partitionReceipt : String
    accountedMass :
      combineMass measure
        (combineMass measure
          (relevanceMass measure consumer retainedRegion)
          (relevanceMass measure consumer representedResidualRegion))
        (relevanceMass measure consumer outsideModelRegion)
      ≡ unitMass measure

open OpenWorldMassAccounting public

record FullRetainedModelMass
    {Consumer Region Mass : Set}
    {measure : ConsumerIndexedRelevanceMeasure Consumer Region Mass}
    {consumer : Consumer}
    (accounting : OpenWorldMassAccounting measure consumer) : Set where
  constructor fullRetainedModelMass
  field
    retainedCarriesUnitMass :
      relevanceMass measure consumer (retainedRegion accounting)
      ≡ unitMass measure

open FullRetainedModelMass public

record ClosedAccountingResiduals
    {Consumer Region Mass : Set}
    {measure : ConsumerIndexedRelevanceMeasure Consumer Region Mass}
    {consumer : Consumer}
    (accounting : OpenWorldMassAccounting measure consumer) : Set where
  constructor closedAccountingResiduals
  field
    representedResidualHasZeroMass :
      relevanceMass measure consumer (representedResidualRegion accounting)
      ≡ zeroMass measure
    outsideModelResidualHasZeroMass :
      relevanceMass measure consumer (outsideModelRegion accounting)
      ≡ zeroMass measure

open ClosedAccountingResiduals public

------------------------------------------------------------------------
-- Authority boundaries.
------------------------------------------------------------------------

data NormalizedMassWorldTruthPermission : Set where

data CandidateNormalizationCompletenessPermission : Set where

normalizedMassCannotAssertWorldTruth :
  NormalizedMassWorldTruthPermission → ⊥
normalizedMassCannotAssertWorldTruth ()

candidateWeightsSummingToUnitCannotProveUniverseComplete :
  CandidateNormalizationCompletenessPermission → ⊥
candidateWeightsSummingToUnitCannotProveUniverseComplete ()

record ConsumerIndexedRelevanceBoundary : Set where
  constructor consumerIndexedRelevanceBoundary
  field
    normalizationIsConsumerIndexed : Bool
    normalizationIsConsumerIndexedIsTrue :
      normalizationIsConsumerIndexed ≡ true
    outsideModelResidualIsRepresentable : Bool
    outsideModelResidualIsRepresentableIsTrue :
      outsideModelResidualIsRepresentable ≡ true
    normalizedMassIsWorldTruth : Bool
    normalizedMassIsWorldTruthIsFalse : normalizedMassIsWorldTruth ≡ false
    normalizedCandidateCarrierIsKnownComplete : Bool
    normalizedCandidateCarrierIsKnownCompleteIsFalse :
      normalizedCandidateCarrierIsKnownComplete ≡ false
    normalizationHasNoWorldTruthPermission :
      NormalizedMassWorldTruthPermission → ⊥
    candidateNormalizationHasNoCompletenessPermission :
      CandidateNormalizationCompletenessPermission → ⊥

open ConsumerIndexedRelevanceBoundary public

canonicalConsumerIndexedRelevanceBoundary : ConsumerIndexedRelevanceBoundary
canonicalConsumerIndexedRelevanceBoundary =
  consumerIndexedRelevanceBoundary
    true refl
    true refl
    false refl
    false refl
    normalizedMassCannotAssertWorldTruth
    candidateWeightsSummingToUnitCannotProveUniverseComplete
