module DASHI.Wikimedia.IbrahimTwoEyedZizekLacanIrigarayMaboWoogarooExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Core.SnowballPluralLensInvariantExact as Lens

------------------------------------------------------------------------
-- TWO-EYED / IDEOLOGY / FEMINIST DIFFERENCE / COUNTRY APPLICATION
--
-- Source-bounded inspiration:
-- * Two-Eyed Seeing / Kimmerer and Indigenous-knowledge owners already in DASHI.
-- * Slavoj Zizek, The Pervert's Guide to Ideology (2012), reading John
--   Carpenter's They Live: the sunglasses function as critique-of-ideology
--   glasses; ideology is not merely an external blur but part of the subject's
--   spontaneous relation to social reality. This is an interpretive source,
--   not empirical proof.
-- * Lacan carriers remain source-bounded psychoanalytic grammars.
-- * Luce Irigaray remains the feminist critical/different-grammar lane; shared
--   carrier does not imply shared grammar.
-- * Mabo/Country and Woogaroo are hard application tests for authority/place.
------------------------------------------------------------------------

data PluralCriticalAxis : Set where
  observerPosition : PluralCriticalAxis
  explicitMessage : PluralCriticalAxis
  latentIdeologicalFrame : PluralCriticalAxis
  enjoymentInvestment : PluralCriticalAxis
  alternativeKnowledgeHistory : PluralCriticalAxis
  grammarDifference : PluralCriticalAxis
  placeCountryRelation : PluralCriticalAxis
  communityAuthority : PluralCriticalAxis
  stateInstitutionalAuthority : PluralCriticalAxis
  materialEcologicalObservation : PluralCriticalAxis
  legalRecognition : PluralCriticalAxis
  realisedOutcome : PluralCriticalAxis

criticalRelevant critical : PluralCriticalAxis → Bool
criticalRelevant _ = true

criticalPluralLens : Lens.PluralLens PluralCriticalAxis
criticalPluralLens = Lens.plural-lens criticalRelevant criticalRelevant (λ _ _ → refl)

record TwoEyedIdeologyReading : Set where
  constructor two-eyed-ideology-reading
  field
    oneEyeCanInspectManifestRepresentation : Bool
    secondEyeCanExposeDifferentProjection : Bool
    ideologicalCritiqueAddsHiddenFrameQuestion : Bool
    critiqueLensIsNeutralViewFromNowhere : Bool
    removingOneLensGuaranteesTruth : Bool
    pluralViewsMayStillBeUnequallySupported : Bool
open TwoEyedIdeologyReading public

canonicalTwoEyedIdeologyReading : TwoEyedIdeologyReading
canonicalTwoEyedIdeologyReading =
  two-eyed-ideology-reading true true true false false true

------------------------------------------------------------------------
-- Zizek/They Live x Two-Eyed Seeing:
-- Two-Eyed Seeing is NOT identified with Zizek's ideology glasses. The useful
-- cross-pollination is structural: a visible surface need not exhaust the
-- operative frame, and switching/adding a lens can disclose residual structure.
-- Unlike the movie metaphor, however, DASHI does not posit one privileged pair
-- of glasses that reveals final reality.
------------------------------------------------------------------------

record CriticalLensComparison : Set where
  constructor critical-lens-comparison
  field
    firstProjection : String
    secondProjection : String
    residualQuestion : String
    oneProjectionDeclaredFinal : Bool
    provenanceOfLensRetained : Bool
open CriticalLensComparison public

twoEyedTheyLiveComparison : CriticalLensComparison
twoEyedTheyLiveComparison = critical-lens-comparison
  "manifest/institutionally legible representation"
  "alternative situated or ideology-critical representation"
  "what changes, disappears or becomes newly visible under the second projection?"
  false true

------------------------------------------------------------------------
-- Lacan/Irigaray: preserve incompatible grammar on a shared carrier.
------------------------------------------------------------------------

record GrammarPlurality : Set where
  constructor grammar-plurality
  field
    sharedCarrierAllowed : Bool
    lacanianGrammarRetained : Bool
    irigarayCriticalGrammarRetained : Bool
    feministDifferenceCollapsedIntoLacan : Bool
    disagreementCountsAsDefect : Bool
open GrammarPlurality public

canonicalGrammarPlurality : GrammarPlurality
canonicalGrammarPlurality =
  grammar-plurality true true true false false

------------------------------------------------------------------------
-- Mabo and Woogaroo application tests.
------------------------------------------------------------------------

record PlaceAuthorityApplication : Set where
  constructor place-authority-application
  field
    application : String
    stateOrInstitutionalProjection : String
    countryCommunityProjection : String
    ecologicalMaterialProjection : String
    legalRecognitionProjection : String
    allRelevantAxesMustSurvive : Bool
    stateRecognitionCreatesAntecedentAuthority : Bool
    ecologicalSuccessExhaustsCountry : Bool
open PlaceAuthorityApplication public

maboApplication : PlaceAuthorityApplication
maboApplication = place-authority-application
  "Mabo / Country"
  "Crown/state legal classification and institutional recognition"
  "Country, community, law/authority, history and custodial relation"
  "land/material place and downstream ecological consequences where relevant"
  "doctrinal recognition/correction without origin-of-authority promotion"
  true false false

woogarooApplication : PlaceAuthorityApplication
woogarooApplication = place-authority-application
  "Woogaroo preservation"
  "council/planning/legal/environmental institutional record"
  "situated community and, only where authorised, Indigenous/Country knowledge"
  "forest, creek, habitat, species, hydrology and other source-bound ecological observations"
  "legal preservation/remedy routes"
  true false false

------------------------------------------------------------------------
-- Snowball rule: future consumers may add e.g. disability, gender, class,
-- temporal lineage, sacred/restricted knowledge, economic incentive, species,
-- hydrology, archaeology, etc. They do not require changing the invariant.
------------------------------------------------------------------------

record SnowballApplicationBoundary : Set where
  constructor snowball-application-boundary
  field
    axisVocabularyLocallyExtensible : Bool
    oldRelevantAxesStayRequired : Bool
    twoEyedDoesNotMeanExactlyTwoTotalAxes : Bool
    zizekLensDoesNotCreateFinalTruthView : Bool
    irigarayDifferenceMayRemainNonSynthesised : Bool
    maboCountryAuthorityNonDescentRetained : Bool
    woogarooEcologyDoesNotExhaustCountryCommunity : Bool
open SnowballApplicationBoundary public

canonicalSnowballApplicationBoundary : SnowballApplicationBoundary
canonicalSnowballApplicationBoundary =
  snowball-application-boundary true true true true true true true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data TwoEyedEqualsZizekGlasses : Set where
data IdeologyCritiqueCreatesGodsEyeView : Set where
data IrigarayIsLacanWithDifferentLabels : Set where
data StateRecognitionCreatesCountry : Set where
data WoogarooEcologyExhaustsCommunityAuthority : Set where

twoEyedDoesNotEqualZizekGlasses : TwoEyedEqualsZizekGlasses → ⊥
twoEyedDoesNotEqualZizekGlasses ()

ideologyCritiqueDoesNotCreateGodsEyeView : IdeologyCritiqueCreatesGodsEyeView → ⊥
ideologyCritiqueDoesNotCreateGodsEyeView ()

irigarayDoesNotCollapseIntoLacan : IrigarayIsLacanWithDifferentLabels → ⊥
irigarayDoesNotCollapseIntoLacan ()

stateRecognitionDoesNotCreateCountry : StateRecognitionCreatesCountry → ⊥
stateRecognitionDoesNotCreateCountry ()

woogarooEcologyDoesNotExhaustCommunityAuthority : WoogarooEcologyExhaustsCommunityAuthority → ⊥
woogarooEcologyDoesNotExhaustCommunityAuthority ()
