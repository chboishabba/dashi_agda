module DASHI.Biology.LysergicPriorArtAttributedCrosswalkExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Sources
import DASHI.Core.ScientificMechanismEvidenceBidiExact as Science
import DASHI.Biology.LysergicPriorArtFiniteCore as Core
import DASHI.Biology.Wong2022LysergicAcidEvidenceExact as Wong
import DASHI.Biology.Wong2022ScientificMetabolicBridgeExact as WongScience

------------------------------------------------------------------------
-- SOURCE-PINNED / NON-OPERATIONAL PRIOR-ART LINEAGE
--
-- 2014 research article by Sarah L. Robinson and Daniel G. Panaccione:
--   Heterologous Expression of Lysergic Acid and Novel Ergot
--   Alkaloids in Aspergillus fumigatus.
--   Applied and Environmental Microbiology 80(20):6465-6472.
--   DOI 10.1128/AEM.02137-14.
--
-- Associated 2015 publication by inventors Daniel G. Panaccione and
-- Sarah L. Robinson, assignee West Virginia University:
--   WO2015195535A2, published 2015-12-23,
--   priority claimed 2014-06-16 via US provisional 62/012,658.
--
-- 2022 independent paper: Wong, Lim, Tan, Go, Bell, Freemont, Yew,
--   DOI 10.1038/s41467-022-28386-6.
--
-- Preserve the distinct publication, patent, and host contexts.
-- No design, pathway instructions, gene constructs or protocols here.
------------------------------------------------------------------------

robinsonPanaccione2014 : Sources.AttributedSource
robinsonPanaccione2014 =
  Sources.mkDOISource
    "Sarah L. Robinson; Daniel G. Panaccione"
    "Heterologous expression of lysergic acid and novel ergot alkaloids in Aspergillus fumigatus"
    "Applied and Environmental Microbiology 80(20):6465-6472; PMID 25107976"
    "2014"
    "10.1128/AEM.02137-14"
    "https://doi.org/10.1128/AEM.02137-14"
    Sources.academicArticleSource
    "Reports prior experimental work in a filamentous fungal host. Its acknowledgement identifies provisional patent 62/012,658. Its observations are source-reported and not equivalent to the 2022 yeast system."
    Sources.publicAttribution

panaccioneRobinsonPatent2015 : Sources.AttributedSource
panaccioneRobinsonPatent2015 =
  Sources.mkNoDOISource
    "Daniel G. Panaccione; Sarah L. Robinson (inventors)"
    "Production of lysergic acid by genetic modification of a fungus"
    "WO2015195535A2; PCT/US2015/035784; West Virginia University (original assignee)"
    "2015"
    "https://patents.google.com/patent/WO2015195535A2/en"
    (Sources.namedSourceKind "patent publication")
    "Patent claims/disclosure concerning a filamentous fungal context. Claim language, legal status and source discussion do not themselves prove experiments, validity, safety, freedom to operate, quantitative yields or yeast equivalence."
    Sources.publicAttribution

historicalLysergicSourceAtlas : Sources.AttributedSourceAtlas
historicalLysergicSourceAtlas =
  Sources.mkSourceAtlas
    "2014 article - 2015 patent - 2022 yeast article attributed lineage"
    "Robinson and Panaccione (research/invention); Wong and collaborators (2022 research); DASHI (bounded crosswalk)"
    (robinsonPanaccione2014
      ∷ panaccioneRobinsonPatent2015
      ∷ Wong.wongEtAl2022
      ∷ [])
    "Non-operational source chronology and scientific-claim boundaries; source repetition is not independent validation, legal clearance, chemical same-object or physical flux calibration."

------------------------------------------------------------------------
-- The patent priority date is older than online publication of the
-- 2014 paper, although the research appeared publicly earlier than
-- the 2015 WO publication. These are different date coordinates.
------------------------------------------------------------------------

record DocumentChronology : Set where
  constructor documentChronology
  field
    provisionalApplicationNumber : String
    patentPriorityAsDisplayed : String
    researchArticleOnlineDate : String
    patentApplicationFiledAsDisplayed : String
    patentWOA2PublishedAsDisplayed : String
    laterYeastArticlePublished : String
    source : Sources.AttributedSource

patentFamilyChronology : DocumentChronology
patentFamilyChronology =
  documentChronology
    "US 62/012,658"
    "2014-06-16"
    "2014-09-19"
    "2015-06-15"
    "2015-12-23"
    "2022-02-07"
    panaccioneRobinsonPatent2015

------------------------------------------------------------------------
-- Source role is preserved by the existing scientific-evidence owner.
-- Patent claim: *reported by patent* / source interpretation.
-- 2014 journal: observation reported by original authors.
-- 2022 journal: existing owner, no new empirical claim.
------------------------------------------------------------------------

research2014Observation : Science.ScientificMechanismReceipt
research2014Observation =
  Science.scientific-mechanism-receipt
    "Robinson and Panaccione (2014) filamentous fungal study"
    "The 2014 original paper reports fungal ergot-alkaloid production evidence in a non-yeast host."
    Science.experimentalObservation
    Science.sourceBacked
    "https://doi.org/10.1128/AEM.02137-14"
    "Original authored research, not independently replicated by this formalisation or a result for the 2022 yeast carrier."

patent2015Disclosure : Science.ScientificMechanismReceipt
patent2015Disclosure =
  Science.scientific-mechanism-receipt
    "Panaccione and Robinson WO2015195535A2"
    "The patent publishes claims concerning lysergic-acid and other ergot-alkaloid production in a fungal context."
    Science.sourceInterpretation
    Science.sourceBacked
    "https://patents.google.com/patent/WO2015195535A2/en"
    "Patent-disclosed claims only. No automatic scientific confirmation, legal opinion, yield inference or equivalence with Wong yeast."

threeSourceScientificContext : List Science.ScientificMechanismReceipt
threeSourceScientificContext =
  research2014Observation
  ∷ patent2015Disclosure
  ∷ WongScience.productionObservation
  ∷ []

------------------------------------------------------------------------
-- The 2014 journal explicitly references the provisional application.
-- Citation correspondence is not a claim-chart infringement opinion,
-- nor is it a proof that all patent claims were experimentally paid.
------------------------------------------------------------------------

record ThreeSourcePriorArtCrosswalk : Set where
  constructor threeSourcePriorArtCrosswalk
  field
    originalResearch : Sources.AttributedSource
    relatedPatent : Sources.AttributedSource
    laterIndependentResearch : Sources.AttributedSource

    researchHost : Core.HostContext
    patentHost : Core.HostContext
    yeastHost : Core.HostContext

    acknowledgedProvisionalIdentifier : String
    patentClaimCategory : Core.ScientificClaimCategory
    researchClaimCategory : Core.ScientificClaimCategory
    yeastClaimCategory : Core.ScientificClaimCategory

    sameGeneralChemistrySubject : Bool
    sameGeneralChemistrySubjectIsTrue :
      sameGeneralChemistrySubject ≡ true

    sameHostAndProtocolProven : Bool
    sameHostAndProtocolProvenIsFalse :
      sameHostAndProtocolProven ≡ false

    identicalMeasuredEndpointProven : Bool
    identicalMeasuredEndpointProvenIsFalse :
      identicalMeasuredEndpointProven ≡ false

    patentClaimIndependentlyValidated : Bool
    patentClaimIndependentlyValidatedIsFalse :
      patentClaimIndependentlyValidated ≡ false

    completeNoveltyAnalysisPaid : Bool
    completeNoveltyAnalysisPaidIsFalse :
      completeNoveltyAnalysisPaid ≡ false

threeSourcePriorArt : ThreeSourcePriorArtCrosswalk
threeSourcePriorArt =
  threeSourcePriorArtCrosswalk
    robinsonPanaccione2014
    panaccioneRobinsonPatent2015
    Wong.wongEtAl2022
    Core.filamentousFungalSystem
    Core.filamentousFungalSystem
    Core.yeastSystem
    "62/012,658"
    Core.inventionClaim
    Core.authorReportedObservation
    Core.authorReportedObservation
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Google Patents gives international WO-family status "Ceased".
-- It explicitly disclaims legal certainty. National branches can vary.
-- Neither a database status nor age of a claim is a legal conclusion.
------------------------------------------------------------------------

record PatentStatusUncertainty : Set where
  constructor patentStatusUncertainty
  field
    familyDocument : Sources.AttributedSource
    databaseStatusAsShown : String
    statusProvenance : String
    legalConclusionTier : Core.LegalInterpretationKind

    territoryByTerritoryFamilyReviewPaid : Bool
    territoryByTerritoryFamilyReviewPaidIsFalse :
      territoryByTerritoryFamilyReviewPaid ≡ false

    freedomToOperateOpinionPaid : Bool
    freedomToOperateOpinionPaidIsFalse :
      freedomToOperateOpinionPaid ≡ false

patentFamilyStatusAsDisplayed : PatentStatusUncertainty
patentFamilyStatusAsDisplayed =
  patentStatusUncertainty
    panaccioneRobinsonPatent2015
    "Ceased (WO international family, Google Patents label as displayed)"
    "Google Patents machine-indexed status; verify each jurisdiction and official register independently."
    Core.databaseStatusLabel
    false refl
    false refl

------------------------------------------------------------------------
-- Explicit non-promotion receipts from canonical attributed-source core.
------------------------------------------------------------------------

patentCitationImportsNoProof :
  Sources.citationImportsProof panaccioneRobinsonPatent2015 ≡ false
patentCitationImportsNoProof = refl

researchCitationImportsNoProof :
  Sources.citationImportsProof robinsonPanaccione2014 ≡ false
researchCitationImportsNoProof = refl

lineageAtlasCreatesNoAuthority :
  Sources.atlasCreatesAuthority historicalLysergicSourceAtlas ≡ false
lineageAtlasCreatesNoAuthority = refl
