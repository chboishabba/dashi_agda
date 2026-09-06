module DASHI.Cognition.PNF.SensibLawIndigenousCarbonColonialClassificationCriticalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSourceAuthorityExact as Authority
import DASHI.Cognition.PNF.SensibLawIndigenousCarbonValueProjectionNonFactorabilityExact as Projection
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackAttributedSourceAtlasExact as Sources

------------------------------------------------------------------------
-- BIA supplies an administrative classification.  The critical interpretation
-- below belongs to SensibLaw/DASHI and is not attributed back to BIA.
------------------------------------------------------------------------

data CarbonClassificationPropositionKind : Set where
  agencyClassificationProposition
  criticalInstitutionalInterpretation
  decolonialNormativeInterpretation
  : CarbonClassificationPropositionKind

record CarbonClassificationProposition : Set where
  constructor carbonClassificationProposition
  field
    propositionKind : CarbonClassificationPropositionKind
    propositionReference : String
    sourceReference : String
    sourceSaysThisDirectly : Bool
    worldTruthAdjudicated : Bool
    worldTruthAdjudicatedIsFalse : worldTruthAdjudicated ≡ false
open CarbonClassificationProposition public

biaStoredCarbonNotTrustAsset : CarbonClassificationProposition
biaStoredCarbonNotTrustAsset = carbonClassificationProposition
  agencyClassificationProposition
  "BIA policy classifies carbon/sequestration value as not a trust asset under the specified trust-asset/product framework because carbon is not harvested or extracted and the relevant value derives from storage"
  (Attr.canonicalURL Sources.biaCarbon2023Source)
  true
  false refl

extractiveLegibilityAsymmetry : CarbonClassificationProposition
extractiveLegibilityAsymmetry = carbonClassificationProposition
  criticalInstitutionalInterpretation
  "critical interpretation: an administrative value ontology organised around harvest/extraction can make extractive commodities institutionally legible while leaving non-extractive stewardship value outside the trust-asset category"
  "DASHI/SensibLaw critical synthesis over the BIA administrative classification plus the generic projection-inadequacy theorem"
  false
  false refl

colonialConvenienceHypothesis : CarbonClassificationProposition
colonialConvenienceHypothesis = carbonClassificationProposition
  decolonialNormativeInterpretation
  "decolonial hypothesis: an extraction-shaped administrative classification may reproduce colonial asymmetries by recognising value through extraction while under-recognising value generated through Indigenous stewardship/non-extraction"
  "DASHI/SensibLaw decolonial interpretation; not a proposition asserted by BIA"
  false
  false refl

------------------------------------------------------------------------
-- Structural result: whatever one thinks of the critical interpretation, the
-- agency's binary category is formally too coarse to carry stewardship value.
------------------------------------------------------------------------

biaAuthorityRemainsAdministrativePolicy :
  Authority.authorityKind Authority.biaCarbon2023Authority
  ≡ Authority.officialAdministrativePolicy
biaAuthorityRemainsAdministrativePolicy = refl

biaMetadataDoesNotCreateAuthority :
  Attr.citationCreatesAuthority Sources.biaCarbon2023Source ≡ false
biaMetadataDoesNotCreateAuthority = refl

trustAssetObserverStillCannotCarryStewardshipValue :
  INF.FactorsThrough Projection.trustAssetObserver Projection.stewardshipValueOutcome → ⊥
trustAssetObserverStillCannotCarryStewardshipValue =
  Projection.trustAssetCategoryCannotFactorStewardshipValue

record ExtractiveLegibilityBoundary : Set where
  constructor extractiveLegibilityBoundary
  field
    agencyClassificationEqualsCriticalInterpretation : Bool
    agencyClassificationEqualsCriticalInterpretationIsFalse : agencyClassificationEqualsCriticalInterpretation ≡ false
    agencyClassificationExhaustsValueOntology : Bool
    agencyClassificationExhaustsValueOntologyIsFalse : agencyClassificationExhaustsValueOntology ≡ false
    criticalLensMayInterrogateDistributionalEffects : Bool
    criticalLensMayInterrogateDistributionalEffectsIsTrue : criticalLensMayInterrogateDistributionalEffects ≡ true
    criticalLensAutomaticallyProvesColonialIntent : Bool
    criticalLensAutomaticallyProvesColonialIntentIsFalse : criticalLensAutomaticallyProvesColonialIntent ≡ false
open ExtractiveLegibilityBoundary public

canonicalExtractiveLegibilityBoundary : ExtractiveLegibilityBoundary
canonicalExtractiveLegibilityBoundary = extractiveLegibilityBoundary
  false refl false refl true refl false refl

data BIAClassificationProvesColonialIntent : Set where
data CriticalInterpretationIsBIAAuthorship : Set where
data NonTrustAssetMeansNoEconomicEcologicalCulturalValue : Set where

biaClassificationDoesNotProveColonialIntent : BIAClassificationProvesColonialIntent → ⊥
biaClassificationDoesNotProveColonialIntent ()

criticalInterpretationDoesNotTransferToBia : CriticalInterpretationIsBIAAuthorship → ⊥
criticalInterpretationDoesNotTransferToBia ()

nonTrustAssetDoesNotMeanNoValue : NonTrustAssetMeansNoEconomicEcologicalCulturalValue → ⊥
nonTrustAssetDoesNotMeanNoValue ()
