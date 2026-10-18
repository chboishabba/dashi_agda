module DASHI.Governance.CheRevolutionaryAuthorityCriteriaExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- CHE / REVOLUTIONARY AUTHORITY CRITERIA
--
-- The contested label "authoritarian" is not emitted as a verdict.  Concrete
-- institutional/practice coordinates are separately sourced and can be
-- supplied to whatever explicit classification rule a consumer declares.
------------------------------------------------------------------------

chePlanningSource : Source.AttributedSource
chePlanningSource = Source.mkDOISource
  "Helen Yaffe"
  "Che as minister: the promotion of science and technology for Cuba's socialist development"
  "Globalizations"
  "2022"
  "10.1080/14747731.2022.2111078"
  "https://www.tandfonline.com/doi/full/10.1080/14747731.2022.2111078"
  Source.academicArticleSource
  "scholarly source on Guevara's Budgetary Finance System, administrative control, moral incentives and socialist development strategy"
  Source.publicAttribution

cheLawValueSource : Source.AttributedSource
cheLawValueSource = Source.mkDOISource
  "Helen Yaffe"
  "A message to the Global South? Che Guevara's view on the NEP and the law of value"
  "Third World Quarterly"
  "2023"
  "10.1080/01436597.2022.2106965"
  "https://www.tandfonline.com/doi/abs/10.1080/01436597.2022.2106965"
  Source.academicArticleSource
  "scholarly source: Guevara treated centralised planning as a defining category of socialism and rejected reliance on the law of value for socialist construction"
  Source.publicAttribution

pbsLaCabana : Source.AttributedSource
pbsLaCabana = Source.mkNoDOISource
  "PBS American Experience"
  "Che Guevara (1928-1967)"
  "PBS"
  ""
  "https://www.pbs.org/wgbh/americanexperience/features/castro-che-guevara-1928-1967/"
  (Source.namedSourceKind "reference work")
  "secondary biographical source documenting Guevara's La Cabana prison responsibility; numerical and due-process claims require source-sensitive treatment"
  Source.publicAttribution

cubaConstitution2019 : Source.AttributedSource
cubaConstitution2019 = Source.mkNoDOISource
  "Republic of Cuba"
  "Constitution of the Republic of Cuba (2019)"
  "Constitute Project carrier"
  "2019"
  "https://www.constituteproject.org/constitution/Cuba_2019"
  Source.governmentSource
  "later constitutional state structure: Communist Party is the unique superior leading force; this does not by itself prove Guevara authored that later constitutional form"
  Source.publicAttribution

data AuthorityCoordinate : Set where
  centralisedEconomicPlanning : AuthorityCoordinate
  administrativeControl : AuthorityCoordinate
  revolutionaryTribunalResponsibility : AuthorityCoordinate
  capitalPunishmentRole : AuthorityCoordinate
  singlePartyStateStructure : AuthorityCoordinate
  oppositionPluralismConstraint : AuthorityCoordinate

record CoordinateReceipt : Set where
  constructor coordinate-receipt
  field
    coordinate : AuthorityCoordinate
    actorOrStateRef : String
    source : Source.AttributedSource
    reading : String
    paid : Bool
    paidIsTrue : paid ≡ true
    actorAuthoredLaterStateStructure : Bool
    actorAuthoredLaterStateStructureIsFalse :
      actorAuthoredLaterStateStructure ≡ false

open CoordinateReceipt public

cheCentralPlanning : CoordinateReceipt
cheCentralPlanning =
  coordinate-receipt
    centralisedEconomicPlanning
    "Ernesto Che Guevara"
    cheLawValueSource
    "Guevara treated centralised planning as a defining category of socialist construction."
    true refl
    false refl

cheAdministrativeControl : CoordinateReceipt
cheAdministrativeControl =
  coordinate-receipt
    administrativeControl
    "Ernesto Che Guevara"
    chePlanningSource
    "The Budgetary Finance System used administrative control and moral incentives within Guevara's socialist-development model."
    true refl
    false refl

cheTribunalResponsibility : CoordinateReceipt
cheTribunalResponsibility =
  coordinate-receipt
    revolutionaryTribunalResponsibility
    "Ernesto Che Guevara"
    pbsLaCabana
    "Secondary biography documents Guevara's command responsibility at La Cabana and involvement in revolutionary justice; exact counts and legal characterisations remain contested."
    true refl
    false refl

laterCubanPartyStructure : CoordinateReceipt
laterCubanPartyStructure =
  coordinate-receipt
    singlePartyStateStructure
    "Republic of Cuba, later constitutional order"
    cubaConstitution2019
    "Article 5 identifies the Communist Party of Cuba as unique and the superior driving force of society and the state."
    true refl
    false refl

data ClassificationLabel : Set where
  liberalDemocraticAuthoritarianLabel : ClassificationLabel
  marxistLeninistRevolutionaryStateLabel : ClassificationLabel
  antiColonialLiberationLabel : ClassificationLabel

record ClassificationRule : Set where
  constructor classification-rule
  field
    label : ClassificationLabel
    requiredCoordinates : List AuthorityCoordinate
    ruleSourceRef : String
    ruleDeclaredByConsumer : Bool
    ruleDeclaredByConsumerIsTrue :
      ruleDeclaredByConsumer ≡ true

record ClassificationBoundary : Set where
  constructor classification-boundary
  field
    coordinatesAreFactsNotVerdicts : Bool
    laterCubanStructureNotAutomaticallyCheAuthorship : Bool
    revolutionaryJustificationDoesNotEraseCoerciveStructure : Bool
    coerciveStructureDoesNotDetermineMotive : Bool
    contextDoesNotEraseAction : Bool
    classificationRequiresExplicitRule : Bool

canonicalBoundary : ClassificationBoundary
canonicalBoundary =
  classification-boundary true true true true true true

data MarxistTheoryNecessitatesEveryCoerciveAct : Set where
data AntiImperialMotiveErasesInstitutionalCoercion : Set where
data LaterCubanConstitutionEqualsChePersonalDoctrine : Set where
data CoordinateListAutomaticallyProducesPoliticalLabel : Set where

marxismDoesNotNecessitateEveryAct :
  MarxistTheoryNecessitatesEveryCoerciveAct → ⊥
marxismDoesNotNecessitateEveryAct ()

motiveDoesNotEraseStructure :
  AntiImperialMotiveErasesInstitutionalCoercion → ⊥
motiveDoesNotEraseStructure ()

laterStateDoesNotEqualPersonalDoctrine :
  LaterCubanConstitutionEqualsChePersonalDoctrine → ⊥
laterStateDoesNotEqualPersonalDoctrine ()

coordinatesDoNotAutoClassify :
  CoordinateListAutomaticallyProducesPoliticalLabel → ⊥
coordinatesDoNotAutoClassify ()

planningSnowball : Snowball.SourceRoleSnowballReceipt chePlanningSource
planningSnowball = Snowball.canonicalSourceRoleSnowballReceipt chePlanningSource
