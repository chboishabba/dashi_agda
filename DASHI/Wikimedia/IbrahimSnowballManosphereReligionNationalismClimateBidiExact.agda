module DASHI.Wikimedia.IbrahimSnowballManosphereReligionNationalismClimateBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballManosphereGenderMasculinityYouthInfluenceBidiExact as Gender
import DASHI.Wikimedia.IbrahimSnowballAnthropologyClimateDenialPoliticalTheologyExact as Climate
import DASHI.Wikimedia.IbrahimSnowballReligionEschatologyIdeologyIdentityExact as Religion

------------------------------------------------------------------------
-- BIDI continuation:
-- manosphere / masculinity <-> religion / religious nationalism
-- <-> nationalism / political identity <-> climate-denial discourse.
--
-- This is a source/date-indexed intersection owner, not a master causal model.
-- Religious identity, Christian nationalism, manosphere classification,
-- antisemitic content, masculinity threat, climate denial, policy position and
-- actor motive remain different consumers and require separate payment.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim manosphere/religion/nationalism/climate BIDI"
  "verified external concept identity only"
  label Identity.wikidataQid
  (Identity.verified qid "Wikidata identity inspected 2026-09-10; no membership, causation, motive or authority promotion")

religiousNationalismQid : Identity.ExternalIdentityDemand
religiousNationalismQid = mkQid "religious nationalism" "Q2019152"

christianNationalismQid : Identity.ExternalIdentityDemand
christianNationalismQid = mkQid "Christian nationalism" "Q24905525"

nationalismQid : Identity.ExternalIdentityDemand
nationalismQid = mkQid "nationalism" "Q6235"

climateDenialQid : Identity.ExternalIdentityDemand
climateDenialQid = mkQid "climate change denial" "Q1931364"

antisemitismQid : Identity.ExternalIdentityDemand
antisemitismQid = mkQid "antisemitism" "Q22649"

antiWokeQid : Identity.ExternalIdentityDemand
antiWokeQid = Identity.mkOptionalIdentityDemand
  "Ibrahim manosphere/religion/nationalism/climate BIDI"
  "external concept identity"
  "anti-woke discourse / anti-wokeness"
  Identity.wikidataQid
  (Identity.unresolved "no exact broad concept QID safely promoted in this pass; rhetoric, movement identity and policy position remain separate")

------------------------------------------------------------------------
-- Attributed public scholarship. Each source pays only its own bounded claims.
------------------------------------------------------------------------

remsöClimateMasculinitySource : Attribution.AttributedSource
remsöClimateMasculinitySource = Attribution.mkDOISource
  "Amanda Remsö; Hanna Bäck; Emma Aurora Renström"
  "Gender differences in climate change denial in Sweden: the role of threatened masculinity"
  "Frontiers in Psychology"
  "2024"
  "10.3389/fpsyg.2024.1450230"
  "https://doi.org/10.3389/fpsyg.2024.1450230"
  Attribution.academicArticleSource
  "three cross-sectional Swedish surveys associating threatened-masculinity measures with climate-change denial; does not establish causal direction or a universal manosphere mechanism"
  Attribution.publicAttribution

wagonerReligiousNationalismSource : Attribution.AttributedSource
wagonerReligiousNationalismSource = Attribution.mkDOISource
  "Joseph A. Wagoner; Moussa Diarra; Barbara Barbieri"
  "Different images of God predict religious nationalism among Christians"
  "Political Psychology"
  "2025"
  "10.1111/pops.13087"
  "https://doi.org/10.1111/pops.13087"
  Attribution.academicArticleSource
  "study of relationships between images of God and religious nationalism among Christian respondents; does not make Christianity identical to nationalism"
  Attribution.publicAttribution

kimChristianNationalismSource : Attribution.AttributedSource
kimChristianNationalismSource = Attribution.mkDOISource
  "Seungju Kim; Peter J. Jankowski; David C. Wang; Hannah Hawkins et al."
  "Patterns of Christian Nationalist Engagement and Connections to Spirituality"
  "Pastoral Psychology 74:821-841"
  "2025"
  "10.1007/s11089-025-01241-3"
  "https://doi.org/10.1007/s11089-025-01241-3"
  Attribution.academicArticleSource
  "latent-profile study of 746 emerging Christian religious/spiritual leaders showing heterogeneous engagement with Christian-nationalist items; does not define all Christian identity or leadership"
  Attribution.publicAttribution

aarReligionManosphereSource : Attribution.AttributedSource
aarReligionManosphereSource = Attribution.mkNoDOISource
  "American Academy of Religion Annual Meeting contributors"
  "Religion and the Manosphere: Masculinist Futures in Digital Religious Spaces"
  "AAR Annual Meeting program session"
  "2026"
  "https://papers.aarweb.org/papers-session/111433-religion-and-manosphere-masculinist-futures-digital-religious-spaces"
  Attribution.academicArticleSource
  "conference-program evidence that scholars are analysing source-specific intersections between religion, masculinity, nationalism and manosphere discourse; individual papers retain separate authorship and evidentiary status"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Regression 1: religious identity cannot recover religious nationalism.
------------------------------------------------------------------------

data ReligionNationalismCase : Set where
  sameReligionNoNationalism sameReligionNationalistFrame : ReligionNationalismCase

data ReligionSurface : Set where sameReligiousIdentity : ReligionSurface
data ReligiousNationalismReading : Set where nationalismNotPaid nationalismPaid : ReligiousNationalismReading

religionSurface : ReligionNationalismCase → ReligionSurface
religionSurface _ = sameReligiousIdentity

religiousNationalismReading : ReligionNationalismCase → ReligiousNationalismReading
religiousNationalismReading sameReligionNoNationalism = nationalismNotPaid
religiousNationalismReading sameReligionNationalistFrame = nationalismPaid

religionNationalismDefect : INF.NonFactorabilityWitness religionSurface religiousNationalismReading
religionNationalismDefect = INF.nonFactorabilityWitness
  sameReligionNoNationalism sameReligionNationalistFrame refl (λ ())

religiousIdentityCannotFactorReligiousNationalism :
  INF.FactorsThrough religionSurface religiousNationalismReading → ⊥
religiousIdentityCannotFactorReligiousNationalism =
  INF.witnessRulesOutEveryFlatFactorisation religionNationalismDefect

------------------------------------------------------------------------
-- Regression 2: masculinity-threat surface cannot recover climate position.
-- Cross-sectional association is retained as evidence, not deterministic cause.
------------------------------------------------------------------------

data MasculinityClimateCase : Set where
  sameMasculinityConcernClimateAction sameMasculinityConcernClimateDenial : MasculinityClimateCase

data MasculinityConcernSurface : Set where sameMasculinityConcern : MasculinityConcernSurface
data ClimatePosition : Set where climateActionPosition climateDenialPosition : ClimatePosition

masculinityConcernSurface : MasculinityClimateCase → MasculinityConcernSurface
masculinityConcernSurface _ = sameMasculinityConcern

climatePosition : MasculinityClimateCase → ClimatePosition
climatePosition sameMasculinityConcernClimateAction = climateActionPosition
climatePosition sameMasculinityConcernClimateDenial = climateDenialPosition

masculinityClimateDefect : INF.NonFactorabilityWitness masculinityConcernSurface climatePosition
masculinityClimateDefect = INF.nonFactorabilityWitness
  sameMasculinityConcernClimateAction sameMasculinityConcernClimateDenial refl (λ ())

masculinityConcernCannotFactorClimatePosition :
  INF.FactorsThrough masculinityConcernSurface climatePosition → ⊥
masculinityConcernCannotFactorClimatePosition =
  INF.witnessRulesOutEveryFlatFactorisation masculinityClimateDefect

------------------------------------------------------------------------
-- Regression 3: manosphere/network classification cannot recover religious or
-- nationalist identity. The AAR cases motivate searching the intersection,
-- not promoting the intersection to every person or subcommunity.
------------------------------------------------------------------------

data NetworkReligionCase : Set where
  sameNetworkReligiousNationalistUse sameNetworkNoReligiousNationalismPaid : NetworkReligionCase

data NetworkSurface : Set where sameManosphereNetworkSurface : NetworkSurface
data ReligionPoliticalRole : Set where religiousNationalistRole roleUnresolved : ReligionPoliticalRole

networkSurface : NetworkReligionCase → NetworkSurface
networkSurface _ = sameManosphereNetworkSurface

religionPoliticalRole : NetworkReligionCase → ReligionPoliticalRole
religionPoliticalRole sameNetworkReligiousNationalistUse = religiousNationalistRole
religionPoliticalRole sameNetworkNoReligiousNationalismPaid = roleUnresolved

networkReligionDefect : INF.NonFactorabilityWitness networkSurface religionPoliticalRole
networkReligionDefect = INF.nonFactorabilityWitness
  sameNetworkReligiousNationalistUse sameNetworkNoReligiousNationalismPaid refl (λ ())

manosphereCannotFactorReligiousNationalism :
  INF.FactorsThrough networkSurface religionPoliticalRole → ⊥
manosphereCannotFactorReligiousNationalism =
  INF.witnessRulesOutEveryFlatFactorisation networkReligionDefect

------------------------------------------------------------------------
-- Regression 4: shared grievance/threat rhetoric cannot recover prejudice type.
-- Antifeminism, antisemitism, anti-diversity and climate denial are distinct
-- proposition families even when a source documents overlap in a discourse.
------------------------------------------------------------------------

data GrievanceCase : Set where
  sameGrievanceAntifeminist sameGrievanceAntisemitic : GrievanceCase

data GrievanceSurface : Set where sameThreatGrievanceSurface : GrievanceSurface
data PrejudiceReading : Set where antifeministReading antisemiticReading : PrejudiceReading

grievanceSurface : GrievanceCase → GrievanceSurface
grievanceSurface _ = sameThreatGrievanceSurface

prejudiceReading : GrievanceCase → PrejudiceReading
prejudiceReading sameGrievanceAntifeminist = antifeministReading
prejudiceReading sameGrievanceAntisemitic = antisemiticReading

grievancePrejudiceDefect : INF.NonFactorabilityWitness grievanceSurface prejudiceReading
grievancePrejudiceDefect = INF.nonFactorabilityWitness
  sameGrievanceAntifeminist sameGrievanceAntisemitic refl (λ ())

grievanceCannotFactorPrejudiceType :
  INF.FactorsThrough grievanceSurface prejudiceReading → ⊥
grievanceCannotFactorPrejudiceType =
  INF.witnessRulesOutEveryFlatFactorisation grievancePrejudiceDefect

------------------------------------------------------------------------
-- Existing BIDI owners remain authoritative for their own surfaces.
------------------------------------------------------------------------

genderBoundary : Gender.ManosphereGenderMasculinityYouthBoundary
genderBoundary = Gender.canonicalManosphereGenderMasculinityYouthBoundary

climateBoundary : Climate.PoliticalTheologyClimateLogicBoundary
climateBoundary = Climate.canonicalPoliticalTheologyClimateLogicBoundary

religionBoundary : Religion.ReligionEschatologyIdeologySnowballBoundary
religionBoundary = Religion.canonicalReligionEschatologyIdeologySnowballBoundary

------------------------------------------------------------------------
-- Reverse constraints back into broad graph nodes.
------------------------------------------------------------------------

record ReligionNationalismClimateReverseConstraint : Set where
  constructor religion-nationalism-climate-reverse-constraint
  field
    parentNode : String
    childWitness : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open ReligionNationalismClimateReverseConstraint public

religionConstraint : ReligionNationalismClimateReverseConstraint
religionConstraint = religion-nationalism-climate-reverse-constraint
  "Religion"
  "heterogeneous Christian-nationalism engagement plus manosphere/religion case studies"
  "religious identity, doctrine, institution, nationalism, gender politics and online-network role remain separate"
  false

masculinityConstraint : ReligionNationalismClimateReverseConstraint
masculinityConstraint = religion-nationalism-climate-reverse-constraint
  "Masculinity"
  "threatened-masculinity/climate association"
  "gender identity, threat perception, men's-rights identification, climate belief and causal mechanism remain separately payable"
  false

climateConstraint : ReligionNationalismClimateReverseConstraint
climateConstraint = religion-nationalism-climate-reverse-constraint
  "Climate-denial discourse"
  "gender/religion/nationalism intersections"
  "empirical climate proposition, denial label, social identity, motive, industry genealogy and theology remain distinct"
  false

nationalismConstraint : ReligionNationalismClimateReverseConstraint
nationalismConstraint = religion-nationalism-climate-reverse-constraint
  "Nationalism"
  "religious-nationalist and digital-masculinity cases"
  "national identity, religious identity, political ideology, movement participation and state policy remain distinct"
  false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ChristianityCreatesChristianNationalism : Set where
data ManosphereCreatesReligiousNationalism : Set where
data MasculinityThreatCreatesClimateDenial : Set where
data ClimateDenialCreatesManosphereMembership : Set where
data ChristianNationalismCreatesAntisemitism : Set where
data AntisemitismCreatesReligiousIdentity : Set where
data AntiWokeLabelCreatesPolicyPosition : Set where

christianityDoesNotCreateChristianNationalism : ChristianityCreatesChristianNationalism → ⊥
christianityDoesNotCreateChristianNationalism ()

manosphereDoesNotCreateReligiousNationalism : ManosphereCreatesReligiousNationalism → ⊥
manosphereDoesNotCreateReligiousNationalism ()

masculinityThreatDoesNotCreateClimateDenial : MasculinityThreatCreatesClimateDenial → ⊥
masculinityThreatDoesNotCreateClimateDenial ()

climateDenialDoesNotCreateManosphereMembership : ClimateDenialCreatesManosphereMembership → ⊥
climateDenialDoesNotCreateManosphereMembership ()

christianNationalismDoesNotCreateAntisemitism : ChristianNationalismCreatesAntisemitism → ⊥
christianNationalismDoesNotCreateAntisemitism ()

antisemitismDoesNotCreateReligiousIdentity : AntisemitismCreatesReligiousIdentity → ⊥
antisemitismDoesNotCreateReligiousIdentity ()

antiWokeLabelDoesNotCreatePolicyPosition : AntiWokeLabelCreatesPolicyPosition → ⊥
antiWokeLabelDoesNotCreatePolicyPosition ()

record ManosphereReligionNationalismClimateBoundary : Set where
  constructor manosphere-religion-nationalism-climate-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    unresolvedAntiWokeIdentityRetained : Bool
    religiousIdentityDoesNotDetermineNationalism : Bool
    networkClassificationDoesNotDetermineReligion : Bool
    masculinityThreatDoesNotDetermineClimatePosition : Bool
    associationDoesNotCreateDeterministicCause : Bool
    grievanceSurfaceDoesNotDeterminePrejudiceType : Bool
    climatePhysicsRemainsIndependentOfIdentityClassification : Bool
    sourceDateAndRoleTravelWithIntersections : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open ManosphereReligionNationalismClimateBoundary public

canonicalManosphereReligionNationalismClimateBoundary :
  ManosphereReligionNationalismClimateBoundary
canonicalManosphereReligionNationalismClimateBoundary =
  manosphere-religion-nationalism-climate-boundary
    true true true true true true true true true true false
