module DASHI.Policy.ABC730PalestinianIncidenceSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact as Obligation
import DASHI.Policy.ABC730UnintendedConsequencesSnowballEvidenceExact as Mechanism
import DASHI.Policy.ABC730IbrahimSnowballAttributionExact as Snowball

------------------------------------------------------------------------
-- Palestinian-incidence snowball.
--
-- The purpose is not to infer the sign of the 2026 ban. It identifies a real
-- labour-incidence channel and records exactly what would still be required to
-- turn that channel into a policy counterfactual.
------------------------------------------------------------------------

data IncidenceEvidenceClass : Set where
  primaryOfficialStatistic : IncidenceEvidenceClass
  primaryMicrodataMetadata : IncidenceEvidenceClass
  intergovernmentalEconomicStudy : IncidenceEvidenceClass
  peerReviewedQualitativeStudy : IncidenceEvidenceClass
  peerReviewedStructuralStudy : IncidenceEvidenceClass

data IncidencePayment : Set where
  exposurePopulationPaid : IncidencePayment
  structuralDependencePaid : IncidencePayment
  mechanismCandidatePaid : IncidencePayment
  exportDependenceUnpaid : IncidencePayment
  sanctionPassThroughUnpaid : IncidencePayment
  netEffectUnpaid : IncidencePayment

record IncidenceReceipt : Set where
  constructor incidenceReceipt
  field
    receiptId : String
    source : Source.AttributedSource
    deweyParent : String
    qidReference : String
    stableIdentifier : String
    evidenceClass : IncidenceEvidenceClass
    payment : IncidencePayment
    boundedFinding : String
    residual : String

open IncidenceReceipt public

pcbsQ4Source : Source.AttributedSource
pcbsQ4Source = Source.mkNoDOISource
  "Palestinian Central Bureau of Statistics"
  "Labour Force Survey / Q4 2025 labour market release"
  "PCBS"
  "2026"
  "https://pcbs.gov.ps/en/post-details/?postId=23457"
  Source.governmentSource
  "primary Palestinian official statistics on employment in Israel and Israeli settlements"
  Source.publicAttribution

pcbsSettlementWorkers : IncidenceReceipt
pcbsSettlementWorkers = incidenceReceipt
  "ABC730-incidence:pcbs-settlement-workers-q4-2025"
  pcbsQ4Source
  "331"
  "qid-unresolved-for-PCBS-institution"
  "PCBS:Q4-2025:postId-23457"
  primaryOfficialStatistic
  exposurePopulationPaid
  "PCBS reports about 20,400 West Bank workers employed in Israeli settlements in Q4 2025, within about 51,000 employed in Israel and Israeli settlements combined."
  "This establishes a settlement-employment exposure population. It does not identify export destination, Australian/UK trade dependence, firm-level sanction exposure, displacement/reallocation or net Palestinian welfare effect."

pcbsMicrodataSource : Source.AttributedSource
pcbsMicrodataSource = Source.mkNoDOISource
  "Palestinian Central Bureau of Statistics"
  "West Bank and Gaza - Labor Force Survey 2025"
  "PCBS Microdata Catalog"
  "2026"
  "https://microdata.pcbs.gov.ps/PCBS-Metadata-en-v5.2/index.php/catalog/746"
  Source.datasetSource
  "primary survey metadata with variables explicitly distinguishing work in Israel or settlements"
  Source.publicAttribution

pcbsMicrodataStructure : IncidenceReceipt
pcbsMicrodataStructure = incidenceReceipt
  "ABC730-incidence:pcbs-lfs-2025-microdata"
  pcbsMicrodataSource
  "331"
  "qid-unresolved-for-PCBS-institution"
  "PSE-PCBS-LFS-2025-V1.0"
  primaryMicrodataMetadata
  mechanismCandidatePaid
  "The 2025 PCBS Labour Force Survey includes variables concerning employment in Israel or settlements and duration/permit status, providing a carrier for more granular incidence analysis."
  "Microdata analysis is still required to isolate settlement employment by industry, employer/export orientation, locality and household dependence. Metadata alone does not pay those aggregates."

unctad2026Source : Source.AttributedSource
unctad2026Source = Source.mkNoDOISource
  "UN Trade and Development (UNCTAD)"
  "The cumulative economic cost of occupation for the Palestinian people (2000-2024) and the long road to recovery"
  "UNCTAD"
  "2026"
  "https://unctad.org/publication/cumulative-economic-cost-occupation-palestinian-people-2000-2024-and-long-road-recovery"
  Source.intergovernmentalSource
  "intergovernmental economic study of West Bank restrictions, trade/labour access and settlement economy"
  Source.publicAttribution

unctadDependencyContext : IncidenceReceipt
unctadDependencyContext = incidenceReceipt
  "ABC730-incidence:unctad-occupation-cost-2026"
  unctad2026Source
  "330"
  "qid-unresolved-for-document-object"
  "UNCTAD:cumulative-economic-cost-occupation:2026"
  intergovernmentalEconomicStudy
  structuralDependencePaid
  "UNCTAD documents major Palestinian economic losses associated with occupation/restrictions and a very large economic value produced by settlements in occupied East Jerusalem and Area C over 2000-2024."
  "This establishes macroeconomic asymmetry and entanglement, not the marginal effect of a settlement-import ban in Australia or the UK."

maharmeh2026Source : Source.AttributedSource
maharmeh2026Source = Source.attributedSource
  "Ihab Maharmeh"
  "The Politics of labour: everyday practices of Palestinian workers in the settler economy"
  "journal article"
  "2026"
  "10.1080/2158379X.2025.2612489"
  "https://doi.org/10.1080/2158379X.2025.2612489"
  Source.academicSource
  "peer-reviewed qualitative study of Palestinian workers in the settler economy; mechanism/context, not a sanctions impact evaluation"
  Source.publicAttribution

maharmehLabourEntanglement : IncidenceReceipt
maharmehLabourEntanglement = incidenceReceipt
  "ABC730-incidence:maharmeh-2026"
  maharmeh2026Source
  "331"
  "qid-unresolved-for-article-object"
  "doi:10.1080/2158379X.2025.2612489"
  peerReviewedQualitativeStudy
  structuralDependencePaid
  "The study documents Palestinian labour embedded in the settler economy and analyses that labour relationship as a site of dependence, domination and everyday resistance."
  "The study is qualitative and is not an estimate of job losses, welfare incidence or causal effects from the 2026 UK/Australian policy counterfactual."

hackl2022Source : Source.AttributedSource
hackl2022Source = Source.attributedSource
  "Andreas Hackl"
  "Occupied labour: dispossession through incorporation among Palestinian workers in Israel"
  "journal article"
  "2022"
  "10.1080/2201473X.2022.2032545"
  "https://doi.org/10.1080/2201473X.2022.2032545"
  Source.academicSource
  "peer-reviewed structural account of Palestinian labour incorporation; background mechanism only"
  Source.publicAttribution

hacklIncorporationContext : IncidenceReceipt
hacklIncorporationContext = incidenceReceipt
  "ABC730-incidence:hackl-2022"
  hackl2022Source
  "331"
  "qid-unresolved-for-article-object"
  "doi:10.1080/2201473X.2022.2032545"
  peerReviewedStructuralStudy
  structuralDependencePaid
  "The article analyses economic incorporation of occupied Palestinian labour and challenges simple claims that employment integration itself establishes Palestinian prosperity."
  "It predates the 2026 policy and does not identify settlement-export exposure or a sanction effect size."

allIncidenceReceipts : List IncidenceReceipt
allIncidenceReceipts =
  pcbsSettlementWorkers ∷ pcbsMicrodataStructure ∷ unctadDependencyContext ∷
  maharmehLabourEntanglement ∷ hacklIncorporationContext ∷ []

------------------------------------------------------------------------
-- The exact Palestinian consequence state after this snowball.
------------------------------------------------------------------------

record PalestinianConsequenceState : Set where
  constructor palestinianConsequenceState
  field
    settlementEmploymentExposureExists : Bool
    settlementEmploymentExposureSourcePaid : Bool
    labourDependenceMechanismExists : Bool
    labourDependenceMechanismSourcePaid : Bool
    shareOfExposedJobsDependentOnSanctionedExportsPaid : Bool
    directJobLossFromBanPaid : Bool
    substitutionOrReallocationPaid : Bool
    domesticPalestinianProductionOffsetPaid : Bool
    householdIncomeEffectPaid : Bool
    netPalestinianEffectSignPaid : Bool

canonicalPalestinianConsequenceState : PalestinianConsequenceState
canonicalPalestinianConsequenceState =
  palestinianConsequenceState true true true true false false false false false false

------------------------------------------------------------------------
-- Next snowball leaves. Acquisition can happen in parallel; payment cannot.
------------------------------------------------------------------------

record PalestinianIncidenceFrontier : Set where
  constructor palestinianIncidenceFrontier
  field
    firmLevelSettlementExportExposure : String
    workerIndustryEmployerCrossTab : String
    destinationSpecificSettlementTrade : String
    wageHouseholdDependence : String
    replacementEmploymentPathways : String
    PalestinianProducerSubstitution : String
    paymentOrderCanBeSkipped : Bool

canonicalPalestinianIncidenceFrontier : PalestinianIncidenceFrontier
canonicalPalestinianIncidenceFrontier = palestinianIncidenceFrontier
  "identify settlement firms exporting goods/services to UK/Australia and their Palestinian worker counts"
  "analyse PCBS microdata or equivalent primary data by settlement/industry/employer where available"
  "measure UK/Australia destination share of settlement output rather than total Israel bilateral trade"
  "estimate household income dependence for exposed Palestinian workers"
  "test whether reduced settlement demand displaces workers, moves production/employment, or is replaced by other labour"
  "test whether Palestinian-origin producers gain, lose or remain unaffected when settlement goods are differentiated"
  false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SettlementEmploymentProvesBanHarmsPalestinians : Set where
settlementEmploymentDoesNotProveBanHarmsPalestinians : SettlementEmploymentProvesBanHarmsPalestinians → ⊥
settlementEmploymentDoesNotProveBanHarmsPalestinians ()

data StructuralDependenceDeterminesPolicySign : Set where
structuralDependenceDoesNotDeterminePolicySign : StructuralDependenceDeterminesPolicySign → ⊥
structuralDependenceDoesNotDeterminePolicySign ()

data DOIImportsCausalEffect : Set where
doiDoesNotImportCausalEffect : DOIImportsCausalEffect → ⊥
doiDoesNotImportCausalEffect ()

data PrimaryStatisticPaysCounterfactual : Set where
primaryStatisticDoesNotPayCounterfactual : PrimaryStatisticPaysCounterfactual → ⊥
primaryStatisticDoesNotPayCounterfactual ()

palestinianMechanismAnchor : Obligation.PolicyEffectObligation
palestinianMechanismAnchor = Obligation.palestinianMechanism

mechanismFrontierAnchor : Mechanism.SnowballFrontier
mechanismFrontierAnchor = Mechanism.canonicalSnowballFrontier

snowballBoundaryAnchor : Snowball.SnowballAttributionBoundary
snowballBoundaryAnchor = Snowball.canonicalSnowballAttributionBoundary
