module DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Reasoning.StructuralMetaphorSourceRegistryExact as Sources
import DASHI.Reasoning.StructuralMetaphorTaskCompressionExact as Compression

------------------------------------------------------------------------
-- SOURCE-BOUNDED INTERPRETIVE BRIDGE
--
-- Kimmerer supplies an embodied/conceptual braid of Indigenous knowledge,
-- scientific knowledge and situated story.  Jungić supplies a mathematical-
-- education application of Two-Eyed Seeing.  DASHI supplies the exact finite
-- mathematics below.  No source is credited with these Agda theorems.
------------------------------------------------------------------------

data KnowledgeHistory : Set where
  indigenousHistory scientificHistory : KnowledgeHistory

data SharedEcologicalObservation : Set where
  convergentObservation : SharedEcologicalObservation

data Provenance : Set where
  indigenousProvenance scientificProvenance : Provenance

data CoordinatedUse : Set where
  useDistinctKnowledgesTogether : CoordinatedUse

observeKnowledgeHistory : KnowledgeHistory → SharedEcologicalObservation
observeKnowledgeHistory _ = convergentObservation

provenance : KnowledgeHistory → Provenance
provenance indigenousHistory = indigenousProvenance
provenance scientificHistory = scientificProvenance

sameObservationAcrossHistories :
  observeKnowledgeHistory indigenousHistory
  ≡ observeKnowledgeHistory scientificHistory
sameObservationAcrossHistories = refl

provenanceDiffersAcrossHistories :
  provenance indigenousHistory ≡ provenance scientificHistory → ⊥
provenanceDiffersAcrossHistories ()

sharedObservationDoesNotRecoverProvenance :
  NonFactor.FactorsThrough observeKnowledgeHistory provenance → ⊥
sharedObservationDoesNotRecoverProvenance =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      indigenousHistory
      scientificHistory
      sameObservationAcrossHistories
      provenanceDiffersAcrossHistories)

------------------------------------------------------------------------
-- Interpretive reading: convergence downstairs does not identify histories
-- upstairs.  Coordinated use likewise does not require fusion.
------------------------------------------------------------------------

braidingReading : String
braidingReading =
  "Distinct knowledge histories can converge on a shared practical or ecological observation without becoming identical in provenance, method, relation or authority; their coordinated use is an interpretive bridge, not a braid-group theorem."

twoEyedSeeingReading : String
twoEyedSeeingReading =
  "Two-Eyed Seeing motivates using strengths from Indigenous and Western/mathematical knowledge together while retaining their distinction; DASHI does not infer identity from coordination."

kimmererSource : Sources.SourceReference
kimmererSource = Sources.kimmerer2013

twoEyedSeeingSource : Sources.SourceReference
twoEyedSeeingSource = Sources.jungic2022

------------------------------------------------------------------------
-- No-promotion boundary.
------------------------------------------------------------------------

record KimmererTwoEyedSeeingBoundary : Set where
  constructor kimmererTwoEyedSeeingBoundary
  field
    sharedObservationMeansSameEpistemicHistory : Bool
    sharedObservationMeansSameEpistemicHistoryIsFalse :
      sharedObservationMeansSameEpistemicHistory ≡ false

    coordinatedUseRequiresEpistemicFusion : Bool
    coordinatedUseRequiresEpistemicFusionIsFalse :
      coordinatedUseRequiresEpistemicFusion ≡ false

    kimmererBookContainsDASHIFactorisationProof : Bool
    kimmererBookContainsDASHIFactorisationProofIsFalse :
      kimmererBookContainsDASHIFactorisationProof ≡ false

    kimmererBookContainsArtinBraidGroupTheory : Bool
    kimmererBookContainsArtinBraidGroupTheoryIsFalse :
      kimmererBookContainsArtinBraidGroupTheory ≡ false

    dashiBridgeIsInterpretiveFormalExtension : Bool
    dashiBridgeIsInterpretiveFormalExtensionIsTrue :
      dashiBridgeIsInterpretiveFormalExtension ≡ true

canonicalKimmererTwoEyedSeeingBoundary : KimmererTwoEyedSeeingBoundary
canonicalKimmererTwoEyedSeeingBoundary =
  kimmererTwoEyedSeeingBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
