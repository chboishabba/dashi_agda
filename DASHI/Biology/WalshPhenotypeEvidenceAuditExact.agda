module DASHI.Biology.WalshPhenotypeEvidenceAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.ChegenWalshUndermethylationSourceAtlasExact as Sources

------------------------------------------------------------------------
-- WALSH / CHEGEN PHENOTYPE SOURCE AUDIT
--
-- This owner asks a narrower question than "is undermethylation real?":
-- which Reel-19 traits can be located in Walsh-authored/institutional source
-- material, and which currently remain reel-only in this atlas?
------------------------------------------------------------------------

data PhenotypeTrait : Set where
  highAchievement : PhenotypeTrait
  chronicUnderlyingAnxiety : PhenotypeTrait
  obsessiveTendencies : PhenotypeTrait
  loopingThoughts : PhenotypeTrait
  competitiveness : PhenotypeTrait
  poorStressRecovery : PhenotypeTrait
  seasonalAllergies : PhenotypeTrait
  histamineReactivity : PhenotypeTrait
  perfectionism : PhenotypeTrait
  addictiveTendency : PhenotypeTrait
  sparseBodyHair : PhenotypeTrait
  lowPainTolerance : PhenotypeTrait
  coldHandsFeet : PhenotypeTrait

data SourceLocationStatus : Set where
  locatedInWalshSource : SourceLocationStatus
  partiallyMatchedInWalshSource : SourceLocationStatus
  reelOnlyInCurrentAtlas : SourceLocationStatus
  independentReplicationNotEstablished : SourceLocationStatus

record TraitEvidenceRow : Set where
  constructor traitEvidenceRow
  field
    trait : PhenotypeTrait
    reelSource : Source.AttributedSource
    walshSource : Source.AttributedSource
    locationStatus : SourceLocationStatus
    reelReading : String
    walshReading : String
    independentReplicationLocated : Bool
    independentReplicationLocatedIsFalse :
      independentReplicationLocated ≡ false

open TraitEvidenceRow public

highAchievementRow : TraitEvidenceRow
highAchievementRow =
  traitEvidenceRow
    highAchievement Sources.chegenReel19 Sources.walshSymptomsTraits2015
    locatedInWalshSource
    "Reel 19: high achievement drive."
    "Walsh presentation: high accomplishment."
    false refl

anxietyRow : TraitEvidenceRow
anxietyRow =
  traitEvidenceRow
    chronicUnderlyingAnxiety Sources.chegenReel19 Sources.walshSymptomsTraits2015
    partiallyMatchedInWalshSource
    "Reel 19: chronic underlying anxiety."
    "Walsh presentation: calm exterior but high inner tension; this is related wording, not exact identity with chronic anxiety."
    false refl

obsessiveRow : TraitEvidenceRow
obsessiveRow =
  traitEvidenceRow
    obsessiveTendencies Sources.chegenReel19 Sources.walshSymptomsTraits2015
    locatedInWalshSource
    "Reel 19: obsessive tendencies."
    "Walsh presentation: OCD tendencies."
    false refl

loopingThoughtsRow : TraitEvidenceRow
loopingThoughtsRow =
  traitEvidenceRow
    loopingThoughts Sources.chegenReel19 Sources.walshSymptomsTraits2015
    reelOnlyInCurrentAtlas
    "Reel 19: thoughts that loop without resolution."
    "No exact Walsh-source wording for this trait has been located in the current atlas."
    false refl

competitiveRow : TraitEvidenceRow
competitiveRow =
  traitEvidenceRow
    competitiveness Sources.chegenReel19 Sources.walshSymptomsTraits2015
    locatedInWalshSource
    "Reel 19: strong competitive nature."
    "Walsh presentation: competitive & perfectionistic."
    false refl

stressRecoveryRow : TraitEvidenceRow
stressRecoveryRow =
  traitEvidenceRow
    poorStressRecovery Sources.chegenReel19 Sources.walshSymptomsTraits2015
    reelOnlyInCurrentAtlas
    "Reel 19: terrible stress recovery."
    "No exact Walsh-source trait matching poor stress recovery has been located in the current atlas."
    false refl

seasonalAllergyRow : TraitEvidenceRow
seasonalAllergyRow =
  traitEvidenceRow
    seasonalAllergies Sources.chegenReel19 Sources.walshSymptomsTraits2015
    locatedInWalshSource
    "Reel 19: history of seasonal allergies."
    "Walsh presentation: seasonal allergies (75%)."
    false refl

histamineReactivityRow : TraitEvidenceRow
histamineReactivityRow =
  traitEvidenceRow
    histamineReactivity Sources.chegenReel19 Sources.walshMethylationBrainDisorders
    partiallyMatchedInWalshSource
    "Reel 19: histamine reactivity."
    "Walsh material uses histamine/methylation interpretations, but this audit does not equate the phrase 'histamine reactivity' with one validated assay or trait."
    false refl

perfectionismRow : TraitEvidenceRow
perfectionismRow =
  traitEvidenceRow
    perfectionism Sources.chegenReel19 Sources.walshSymptomsTraits2015
    locatedInWalshSource
    "Reel 19: personal/family history of perfectionism."
    "Walsh presentation: competitive & perfectionistic."
    false refl

addictiveRow : TraitEvidenceRow
addictiveRow =
  traitEvidenceRow
    addictiveTendency Sources.chegenReel19 Sources.walshSymptomsTraits2015
    locatedInWalshSource
    "Reel 19: personal/family history of addiction."
    "Walsh presentation: addictive tendency."
    false refl

sparseBodyHairRow : TraitEvidenceRow
sparseBodyHairRow =
  traitEvidenceRow
    sparseBodyHair Sources.chegenReel19 Sources.walshSymptomsTraits2015
    reelOnlyInCurrentAtlas
    "Reel 19: sparse body hair."
    "No matching trait has been located in the current Walsh source atlas."
    false refl

lowPainToleranceRow : TraitEvidenceRow
lowPainToleranceRow =
  traitEvidenceRow
    lowPainTolerance Sources.chegenReel19 Sources.walshSymptomsTraits2015
    reelOnlyInCurrentAtlas
    "Reel 19: low pain tolerance."
    "No matching trait has been located in the current Walsh source atlas."
    false refl

coldHandsFeetRow : TraitEvidenceRow
coldHandsFeetRow =
  traitEvidenceRow
    coldHandsFeet Sources.chegenReel19 Sources.walshSymptomsTraits2015
    reelOnlyInCurrentAtlas
    "Reel 19: cold hands and feet."
    "No matching trait has been located in the current Walsh source atlas."
    false refl

canonicalTraitEvidenceRows : List TraitEvidenceRow
canonicalTraitEvidenceRows =
  highAchievementRow
  ∷ anxietyRow
  ∷ obsessiveRow
  ∷ loopingThoughtsRow
  ∷ competitiveRow
  ∷ stressRecoveryRow
  ∷ seasonalAllergyRow
  ∷ histamineReactivityRow
  ∷ perfectionismRow
  ∷ addictiveRow
  ∷ sparseBodyHairRow
  ∷ lowPainToleranceRow
  ∷ coldHandsFeetRow
  ∷ []

------------------------------------------------------------------------
-- Source overlap is not validation.
------------------------------------------------------------------------

data WalshSourceOverlapImpliesIndependentReplication : Set where
data SimilarWordingImpliesSameOperationalVariable : Set where
data FamilyHistoryTraitEqualsMeasuredPhenotype : Set where

walshOverlapDoesNotCreateIndependentReplication :
  WalshSourceOverlapImpliesIndependentReplication → ⊥
walshOverlapDoesNotCreateIndependentReplication ()

similarWordingDoesNotCreateOperationalIdentity :
  SimilarWordingImpliesSameOperationalVariable → ⊥
similarWordingDoesNotCreateOperationalIdentity ()

familyHistoryDoesNotEqualMeasuredPhenotype :
  FamilyHistoryTraitEqualsMeasuredPhenotype → ⊥
familyHistoryDoesNotEqualMeasuredPhenotype ()

record PhenotypeAuditBoundary : Set where
  constructor phenotypeAuditBoundary
  field
    sourceOverlapEstablishedForSubset : Bool
    sourceOverlapEstablishedForSubsetIsTrue :
      sourceOverlapEstablishedForSubset ≡ true
    allReelTraitsLocatedInWalshMaterial : Bool
    allReelTraitsLocatedInWalshMaterialIsFalse :
      allReelTraitsLocatedInWalshMaterial ≡ false
    independentReplicationEstablished : Bool
    independentReplicationEstablishedIsFalse :
      independentReplicationEstablished ≡ false
    reading : String

canonicalPhenotypeAuditBoundary : PhenotypeAuditBoundary
canonicalPhenotypeAuditBoundary =
  phenotypeAuditBoundary
    true refl
    false refl
    false refl
    "Several Reel-19 traits substantially overlap Walsh-authored phenotype lists, while several do not yet have a located Walsh-source match. Source overlap establishes attribution lineage only; independent validation/replication remains open."
