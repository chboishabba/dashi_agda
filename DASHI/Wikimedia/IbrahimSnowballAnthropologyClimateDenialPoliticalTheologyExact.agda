module DASHI.Wikimedia.IbrahimSnowballAnthropologyClimateDenialPoliticalTheologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Reasoning.FallacyObstructionCatalogue as Fallacy
import DASHI.Governance.AmalekProvenanceRoleBinding as Amalek
import DASHI.Culture.AmalekAuthorityProjectionBoundary as AmalekProjection
import DASHI.Governance.EvidenceGradedGenealogyCasesExact as Genealogy
import DASHI.Interop.GodsEyeViewActivistThreatAtlasExact as Threat
import DASHI.Wikimedia.IbrahimEnglishAnthropologyHumanityBridgeExact as Anthropology
import DASHI.Wikimedia.IbrahimSnowballAIStateMilitaryChipClimateExact as AIClimate

------------------------------------------------------------------------
-- SNOWBALL BACK-PROPAGATION:
-- ANTHROPOLOGY / LOGIC / CLIMATE DENIAL / POLITICAL THEOLOGY
--
-- This owner cross-pollinates existing source-bounded lanes without making a
-- causal master theory. In particular it keeps separate:
--   empirical climate proposition
--   belief/worldview proposition
--   identity/community position
--   rhetoric / political-theology narrative
--   policy preference / mobilisation
--   material interest / institutional genealogy
--   scriptural source and later role-binding
--   supernatural truth claim.
--
-- Public scholarship used as external calibration includes:
--   Jonna Yarrington, "The Poetics of Denial: Epistemic Politics and the
--   Climate Stereotype on Tangier Island, USA", Signs and Society (2026):
--   long-term ethnography treating denial as political/semiotic positioning,
--   not simply absence of climate knowledge.
--   Pew Research Center, "How Religion Intersects With Americans' Views on
--   the Environment" (2022): modest descriptive association between end-times
--   belief and lower climate concern, with substantial within-group variation.
--   Politics and Religion research on religious/secular belief interaction:
--   end-times belief alone does not supply a simple causal explanation once
--   other belief coordinates are included.
--
-- These are anthropology/political-science observations. They do not alter the
-- physical climate evidence surface and do not license religious stereotyping.
------------------------------------------------------------------------

data ClimateBeliefAtomKind : Set where
  physicalClimateClaim
  causalAttributionClaim
  policyPreferenceClaim
  religiousWorldviewClaim
  eschatologicalNarrativeClaim
  identityPositioningClaim
  movementMobilisationClaim
  materialInterestClaim
  scripturalReceptionClaim : ClimateBeliefAtomKind

record ClimateBeliefAttributedAtom : Set where
  constructor climate-belief-attributed-atom
  field
    kind : ClimateBeliefAtomKind
    proposition : String
    sourceRole : String
    sourceReference : String
    scopeReference : String
    excludedPromotion : String
open ClimateBeliefAttributedAtom public

endTimesClimateAssociation : ClimateBeliefAttributedAtom
endTimesClimateAssociation = climate-belief-attributed-atom
  religiousWorldviewClaim
  "US survey data report lower average climate concern among respondents who say humanity is living in the end times, with substantial heterogeneity and no universal individual-level inference."
  "survey/descriptive social-science source"
  "Pew Research Center, How Religion Intersects With Americans' Views on the Environment, 2022"
  "US adult survey population; descriptive association"
  "Does not prove that end-times belief causes climate denial, does not generalise to all Christians, evangelicals, religious people, or countries, and does not modify physical climate evidence."

anthropologicalDenialPositioning : ClimateBeliefAttributedAtom
anthropologicalDenialPositioning = climate-belief-attributed-atom
  identityPositioningClaim
  "Long-term ethnographic work on Tangier Island analyses professed climate denial as political/semiotic positioning rather than reducible to ignorance."
  "ethnographic scholarly interpretation"
  "Jonna Yarrington, The Poetics of Denial: Epistemic Politics and the Climate Stereotype on Tangier Island, USA, Signs and Society, 2026"
  "specific ethnographic community/context"
  "Does not establish that every climate-denial utterance has this function or that empirical climate propositions become culturally relative."

climateDenialGenealogy : ClimateBeliefAttributedAtom
climateDenialGenealogy = climate-belief-attributed-atom
  materialInterestClaim
  "Existing DASHI genealogy records historically documented continuity of actors/strategies across tobacco doubt production and climate-change doubt campaigns."
  "historical genealogy"
  "DASHI.Governance.EvidenceGradedGenealogyCasesExact; Oreskes and Conway source lane"
  "bounded historical continuity, not central-command theory"
  "Does not imply that every climate-sceptical person or religious community is industry-directed."

------------------------------------------------------------------------
-- Regression 1: same empirical stance label cannot determine social meaning.
------------------------------------------------------------------------

data DenialSituatedCase : Set where
  sameDenialSurfaceIdentityPositioning : DenialSituatedCase
  sameDenialSurfaceIndustryNarrative : DenialSituatedCase

data DenialSurface : Set where
  sameClimateDenialLabel : DenialSurface

data DenialSocialReading : Set where
  communityIdentityPositioning : DenialSocialReading
  organisedDoubtProduction : DenialSocialReading

projectDenialSurface : DenialSituatedCase → DenialSurface
projectDenialSurface _ = sameClimateDenialLabel

denialSocialReading : DenialSituatedCase → DenialSocialReading
denialSocialReading sameDenialSurfaceIdentityPositioning = communityIdentityPositioning
denialSocialReading sameDenialSurfaceIndustryNarrative = organisedDoubtProduction

denialMeaningDefect :
  INF.NonFactorabilityWitness projectDenialSurface denialSocialReading
denialMeaningDefect = INF.nonFactorabilityWitness
  sameDenialSurfaceIdentityPositioning
  sameDenialSurfaceIndustryNarrative
  refl
  (λ ())

denialLabelCannotFactorSocialMeaning :
  INF.FactorsThrough projectDenialSurface denialSocialReading → ⊥
denialLabelCannotFactorSocialMeaning =
  INF.witnessRulesOutEveryFlatFactorisation denialMeaningDefect

------------------------------------------------------------------------
-- Regression 2: same end-times/worldview surface cannot determine climate
-- policy preference. This blocks a religious-determinism shortcut.
------------------------------------------------------------------------

data EschatologySituatedCase : Set where
  endTimesWithClimateAction : EschatologySituatedCase
  endTimesWithoutClimateAction : EschatologySituatedCase

data EschatologySurface : Set where
  sameEndTimesBeliefSurface : EschatologySurface

data ClimatePolicyReading : Set where
  supportsClimateAction : ClimatePolicyReading
  opposesOrDeprioritisesClimateAction : ClimatePolicyReading

projectEschatology : EschatologySituatedCase → EschatologySurface
projectEschatology _ = sameEndTimesBeliefSurface

climatePolicyReading : EschatologySituatedCase → ClimatePolicyReading
climatePolicyReading endTimesWithClimateAction = supportsClimateAction
climatePolicyReading endTimesWithoutClimateAction = opposesOrDeprioritisesClimateAction

eschatologyPolicyDefect :
  INF.NonFactorabilityWitness projectEschatology climatePolicyReading
eschatologyPolicyDefect = INF.nonFactorabilityWitness
  endTimesWithClimateAction endTimesWithoutClimateAction refl (λ ())

eschatologyCannotFactorClimatePolicy :
  INF.FactorsThrough projectEschatology climatePolicyReading → ⊥
eschatologyCannotFactorClimatePolicy =
  INF.witnessRulesOutEveryFlatFactorisation eschatologyPolicyDefect

------------------------------------------------------------------------
-- Political-theology / Amalek / Antichrist boundary.
------------------------------------------------------------------------

politicalTheologyBoundary : Threat.ActivistThreatAtlasBoundary
politicalTheologyBoundary = Threat.canonicalActivistThreatAtlasBoundary

amalekBoundary : Amalek.AmalekBoundary
amalekBoundary = Amalek.canonicalAmalekBoundary

amalekAuthorityBoundary : AmalekProjection.AmalekAuthorityProjectionBoundary
amalekAuthorityBoundary = AmalekProjection.canonicalAmalekAuthorityProjectionBoundary

------------------------------------------------------------------------
-- Logic/fallacy audit: these are the main promotions blocked in this seam.
------------------------------------------------------------------------

record PoliticalTheologyClimateLogicBoundary : Set where
  constructor political-theology-climate-logic-boundary
  field
    religiousWorldviewEqualsEmpiricalClimateClaim : Bool
    endTimesBeliefDeterminesClimatePolicy : Bool
    climateDenialLabelDeterminesMotive : Bool
    documentedAssociationCreatesCausation : Bool
    politicalConductProvesAntichristIdentity : Bool
    amalekAnalogyCreatesPopulationIdentity : Bool
    ancientCommandImportsModernPolicy : Bool
    climateScienceRefutesOrProvesTheology : Bool
    anthropologyMakesClimatePhysicsRelative : Bool
    fallacyCatalogueAppliesToPromotion : Bool
    attributionRetainedAcrossEveryCrossPollination : Bool
    currentAxisVocabularyClaimedComplete : Bool
open PoliticalTheologyClimateLogicBoundary public

canonicalPoliticalTheologyClimateLogicBoundary :
  PoliticalTheologyClimateLogicBoundary
canonicalPoliticalTheologyClimateLogicBoundary =
  political-theology-climate-logic-boundary
    false false false false false false false false false true true false

------------------------------------------------------------------------
-- Explicit fallacy-sector reuse. The obstruction is to the argument transport,
-- not proof that the target conclusion is false.
------------------------------------------------------------------------

associationToCauseObstruction : Fallacy.FallacyObstruction
associationToCauseObstruction = Fallacy.correlationPromotedToCause

analogyToIdentityObstruction : Fallacy.FallacyObstruction
analogyToIdentityObstruction = Fallacy.analogyPromotedToDefinition

localReligiousSampleToUniversalObstruction : Fallacy.FallacyObstruction
localReligiousSampleToUniversalObstruction = Fallacy.localToGlobalScopeLeak

worldviewToNecessityObstruction : Fallacy.FallacyObstruction
worldviewToNecessityObstruction = Fallacy.possiblePromotedToNecessary

------------------------------------------------------------------------
-- Upstream/downstream reuse receipts.
------------------------------------------------------------------------

anthropologyPrior : Anthropology.AnthropologyHumanityBoundary
anthropologyPrior = Anthropology.canonicalAnthropologyHumanityBoundary

aiClimatePrior : AIClimate.AIStateMilitaryChipClimateBoundary
aiClimatePrior = AIClimate.canonicalAIStateMilitaryChipClimateBoundary

genealogyPrior : Genealogy.CaseComparisonBoundary
genealogyPrior = Genealogy.canonicalCaseComparisonBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ReligionCausesClimateDenialPermission : Set where
data ClimateDenialMeansReligiousBeliefPermission : Set where
data EndTimesMeansAntiClimatePolicyPermission : Set where
data AntichristNarrativeMeansSupernaturalIdentityPermission : Set where
data AmalekRoleMeansCollectiveEnemyIdentityPermission : Set where

data ClimatePhysicsDeterminesPoliticalTheologyPermission : Set where

religionDoesNotAutoCauseClimateDenial : ReligionCausesClimateDenialPermission → ⊥
religionDoesNotAutoCauseClimateDenial ()

climateDenialDoesNotRevealReligiousBelief : ClimateDenialMeansReligiousBeliefPermission → ⊥
climateDenialDoesNotRevealReligiousBelief ()

endTimesDoesNotDetermineClimatePolicy : EndTimesMeansAntiClimatePolicyPermission → ⊥
endTimesDoesNotDetermineClimatePolicy ()

antichristNarrativeDoesNotCreateSupernaturalIdentity :
  AntichristNarrativeMeansSupernaturalIdentityPermission → ⊥
antichristNarrativeDoesNotCreateSupernaturalIdentity ()

amalekRoleDoesNotCreateCollectiveEnemyIdentity :
  AmalekRoleMeansCollectiveEnemyIdentityPermission → ⊥
amalekRoleDoesNotCreateCollectiveEnemyIdentity ()

climatePhysicsDoesNotAdjudicatePoliticalTheology :
  ClimatePhysicsDeterminesPoliticalTheologyPermission → ⊥
climatePhysicsDoesNotAdjudicatePoliticalTheology ()
