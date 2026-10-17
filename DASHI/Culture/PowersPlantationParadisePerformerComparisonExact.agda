module DASHI.Culture.PowersPlantationParadisePerformerComparisonExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Culture.PowersPlantationParadiseSourceAtlasExact as Atlas
import DASHI.Culture.PowersPlantationParadiseMinetteMicrohistoryExact as Minette

------------------------------------------------------------------------
-- MINETTE / LISE DESCRIPTIVE COMPARISON
--
-- The two half-sisters provide a valuable same-family descriptive comparison,
-- but not a matched causal counterfactual. Their routes, repertoire and venue
-- histories differ, and no exchangeability/ignorability assumption is supplied.
------------------------------------------------------------------------

prestTransnationalPerformanceSource : Source.AttributedSource
prestTransnationalPerformanceSource =
  Source.mkNoDOISource
    "Julia Prest"
    "Performance, Race and Transnational Theatre in the Eighteenth-Century French Caribbean"
    "chapter in Colonialism and Slavery in Performance: Theatre and the Eighteenth-Century French Caribbean, Liverpool University Press"
    "2022"
    "https://research-repository.st-andrews.ac.uk/bitstream/10023/25703/1/Prest_2022_Chapter_Performance_CC.pdf"
    Source.academicChapterSource
    "scholarly same-object source for Lise's 1786 Saint-Marc performance and its Affiches americaines coordinate; the chapter explicitly treats the audience-effect question as not knowable from the surviving record"
    Source.publicAttribution

record PerformerEventReceipt : Set where
  constructor performer-event-receipt
  field
    performerReference : String
    relationReference : String
    dateReference : String
    venueReference : String
    roleReference : String
    eventReference : String
    source : Source.AttributedSource
    citedPrimaryCoordinate : String
    primaryOriginalInspectedHere : Bool
    primaryOriginalInspectedHereIsFalse : primaryOriginalInspectedHere ≡ false

open PerformerEventReceipt public

liseSaintMarc1786Receipt : PerformerEventReceipt
liseSaintMarc1786Receipt =
  performer-event-receipt
    "Lise, named performer of colour and younger half-sister of Minette"
    "same maternal family / different observed theatrical trajectory"
    "performance 6 February 1786; announcement 28 January 1786"
    "Saint-Marc"
    "Thérèse in Les Amours de Mirebalais / Jeannot et Thérèse, described in the newspaper as a black parody of Le Devin du village"
    "Prest identifies this as the recorded case of Lise, one of only two named actor-performers of colour, taking the lead role understood as black alongside an otherwise white public-stage tradition"
    prestTransnationalPerformanceSource
    "Affiches americaines, 28 January 1786"
    false refl

record PerformerTrajectorySurface : Set where
  constructor performer-trajectory-surface
  field
    performerReference : String
    familyReference : String
    venueCircuitReference : String
    rolePatternReference : String
    economicReference : String
    sourceReference : String

open PerformerTrajectorySurface public

minetteTrajectorySurface : PerformerTrajectorySurface
minetteTrajectorySurface =
  performer-trajectory-surface
    "Minette"
    "half-sister of Lise; same maternal family"
    "predominantly documented in Port-au-Prince"
    "solo roles largely treated as white-coded/default-white in the surviving performance analysis"
    "benefit performances plus 1784 three-year contract at 8000 livres/year with documented nonpayment"
    "Prest 2017/2019, Camier, Colonial Networks and cited primary coordinates"

liseTrajectorySurface : PerformerTrajectorySurface
liseTrajectorySurface =
  performer-trajectory-surface
    "Lise"
    "younger half-sister of Minette; same maternal family"
    "documented in Les Cayes, Léogane, Saint-Marc and Port-au-Prince"
    "includes the 6 February 1786 Thérèse role explicitly understood as black in the source analysis"
    "no Minette-like salary/settlement receipt is paid in this owner"
    "Prest 2017 and 2022 with Affiches americaines 28 January 1786 coordinate"

data SiblingComparisonPaysCausalCounterfactual : Set where

siblingComparisonDoesNotPayCausalCounterfactual :
  SiblingComparisonPaysCausalCounterfactual → ⊥
siblingComparisonDoesNotPayCausalCounterfactual ()

data SharedFamilyImpliesMatchedExposure : Set where

sharedFamilyDoesNotImplyMatchedExposure :
  SharedFamilyImpliesMatchedExposure → ⊥
sharedFamilyDoesNotImplyMatchedExposure ()

record PowersPerformerComparisonBoundary : Set where
  constructor powers-performer-comparison-boundary
  field
    liseNamedEventSameObjectPaid : Bool
    liseNamedEventSameObjectPaidIsTrue : liseNamedEventSameObjectPaid ≡ true
    minetteLiseDescriptiveComparisonPaid : Bool
    minetteLiseDescriptiveComparisonPaidIsTrue :
      minetteLiseDescriptiveComparisonPaid ≡ true
    sameFamilyCreatesCausalExchangeability : Bool
    sameFamilyCreatesCausalExchangeabilityIsFalse :
      sameFamilyCreatesCausalExchangeability ≡ false
    descriptiveComparisonPaysTreatmentEffect : Bool
    descriptiveComparisonPaysTreatmentEffectIsFalse :
      descriptiveComparisonPaysTreatmentEffect ≡ false
    newspaperCoordinateEqualsPrimaryInspection : Bool
    newspaperCoordinateEqualsPrimaryInspectionIsFalse :
      newspaperCoordinateEqualsPrimaryInspection ≡ false

canonicalPowersPerformerComparisonBoundary : PowersPerformerComparisonBoundary
canonicalPowersPerformerComparisonBoundary =
  powers-performer-comparison-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
