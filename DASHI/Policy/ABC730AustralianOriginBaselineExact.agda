module DASHI.Policy.ABC730AustralianOriginBaselineExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Policy.ABC730AustralianImplementationSnowballExact as Australia
import DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact as Obligation

------------------------------------------------------------------------
-- Australian origin-classification baseline.
--
-- Existing Australian import/origin systems prove that origin-related
-- documentary obligations already exist. They do NOT prove that current
-- systems identify Israeli settlement production as a sub-country origin.
------------------------------------------------------------------------

data OriginEvidenceClass : Set where
  primaryBorderGuidance : OriginEvidenceClass
  primaryConsumerRegulatorGuidance : OriginEvidenceClass
  primaryFoodImportGuidance : OriginEvidenceClass

data OriginPayment : Set where
  importDeclarationInfrastructurePaid : OriginPayment
  countryOriginLabellingPaid : OriginPayment
  preferentialOriginAdvicePaid : OriginPayment
  importedFoodOriginCompliancePaid : OriginPayment
  settlementSubcountryClassifierUnpaid : OriginPayment
  incrementalDocumentBurdenUnpaid : OriginPayment
  incrementalSystemsCostUnpaid : OriginPayment

record OriginBaselineReceipt : Set where
  constructor originBaselineReceipt
  field
    receiptId : String
    source : Source.AttributedSource
    deweyParent : String
    qidReference : String
    stableIdentifier : String
    canonicalLink : String
    evidenceClass : OriginEvidenceClass
    payment : OriginPayment
    boundedFinding : String
    residual : String

open OriginBaselineReceipt public

abfImportDeclarationSource : Source.AttributedSource
abfImportDeclarationSource = Source.mkNoDOISource
  "Australian Border Force"
  "Import declarations"
  "Australian Border Force"
  "2026"
  "https://www.abf.gov.au/imports/Pages/How-to-import/Import-declarations.aspx"
  Source.governmentSource
  "primary guidance on Australian import declaration infrastructure and importer responsibility"
  Source.publicAttribution

abfImportDeclarationReceipt : OriginBaselineReceipt
abfImportDeclarationReceipt = originBaselineReceipt
  "ABC730-origin:abf-import-declaration"
  abfImportDeclarationSource
  "382.7"
  "Q17000879"
  "abf:import-declarations:2026"
  "https://www.abf.gov.au/imports/Pages/How-to-import/Import-declarations.aspx"
  primaryBorderGuidance
  importDeclarationInfrastructurePaid
  "Australia already requires importers or their agents to lodge declarations for relevant imports, with tariff classification/customs value and importer responsibility."
  "The ordinary declaration surface does not by itself establish a field or documentary rule distinguishing production inside an Israeli settlement from production elsewhere in Israel."

abfOriginAdviceSource : Source.AttributedSource
abfOriginAdviceSource = Source.mkNoDOISource
  "Australian Border Force"
  "Free Trade Agreements Origin Advice"
  "Australian Border Force"
  "2026"
  "https://www.abf.gov.au/importing-exporting-and-manufacturing/fta/origin-advice"
  Source.governmentSource
  "primary guidance showing that ABF already adjudicates documentary origin questions for preferential trade arrangements"
  Source.publicAttribution

abfOriginAdviceReceipt : OriginBaselineReceipt
abfOriginAdviceReceipt = originBaselineReceipt
  "ABC730-origin:abf-origin-advice"
  abfOriginAdviceSource
  "382.7"
  "Q17000879"
  "abf:origin-advice:2026"
  "https://www.abf.gov.au/importing-exporting-and-manufacturing/fta/origin-advice"
  primaryBorderGuidance
  preferentialOriginAdvicePaid
  "ABF already operates a written Origin Advice mechanism for deciding whether specified goods originate for preferential customs purposes."
  "A preferential-country-origin decision is not the same object as identifying settlement-place origin for a prohibition; required legal tests, evidence and administrative cost remain open."

acccOriginSource : Source.AttributedSource
acccOriginSource = Source.mkNoDOISource
  "Australian Competition and Consumer Commission"
  "Country of origin food labelling"
  "ACCC"
  "2026"
  "https://www.accc.gov.au/business/advertising-and-promotions/country-of-origin-food-labelling"
  Source.governmentSource
  "primary regulator guidance on mandatory country-of-origin labelling for most food offered for retail sale"
  Source.publicAttribution

acccCountryOriginReceipt : OriginBaselineReceipt
acccCountryOriginReceipt = originBaselineReceipt
  "ABC730-origin:accc-country-labelling"
  acccOriginSource
  "381.3"
  "Q4056089"
  "accc:country-origin-food-labelling:2026"
  "https://www.accc.gov.au/business/advertising-and-promotions/country-of-origin-food-labelling"
  primaryConsumerRegulatorGuidance
  countryOriginLabellingPaid
  "Most retail food in Australia already carries country-of-origin information under the Country of Origin Food Labelling Information Standard."
  "Country-level labels do not necessarily identify sub-country place of production or settlement status, and some food categories/circumstances have different labelling requirements."

daffImportFoodSource : Source.AttributedSource
daffImportFoodSource = Source.mkNoDOISource
  "Australian Department of Agriculture, Fisheries and Forestry"
  "How to import food into Australia - a step-by-step guide"
  "DAFF"
  "2026"
  "https://www.agriculture.gov.au/biosecurity-trade/import/goods/food/how"
  Source.governmentSource
  "primary imported-food guidance linking import compliance with country-of-origin labelling and other documentary requirements"
  Source.publicAttribution

daffImportedFoodReceipt : OriginBaselineReceipt
daffImportedFoodReceipt = originBaselineReceipt
  "ABC730-origin:daff-import-food"
  daffImportFoodSource
  "382.7"
  "qid-unresolved-for-DAFF"
  "daff:import-food-guide:2026"
  "https://www.agriculture.gov.au/biosecurity-trade/import/goods/food/how"
  primaryFoodImportGuidance
  importedFoodOriginCompliancePaid
  "Australian food importers already operate within biosecurity, food-standard and country-of-origin compliance systems."
  "This pays baseline compliance infrastructure, not the incremental cost or feasibility of a settlement-specific prohibition."

allOriginBaselineReceipts : List OriginBaselineReceipt
allOriginBaselineReceipts =
  abfImportDeclarationReceipt ∷ abfOriginAdviceReceipt ∷
  acccCountryOriginReceipt ∷ daffImportedFoodReceipt ∷ []

record AustralianOriginCapabilityState : Set where
  constructor australianOriginCapabilityState
  field
    importDeclarationSystemExists : Bool
    originAdjudicationSystemExists : Bool
    retailCountryOriginLabellingExists : Bool
    importedFoodOriginComplianceExists : Bool
    settlementSubcountryOriginFieldExistsPaid : Bool
    settlementProductionLocationEvidenceStandardPaid : Bool
    importerIncrementalCostPaid : Bool
    customsIncrementalCostPaid : Bool
    enforcementErrorRatePaid : Bool

canonicalAustralianOriginCapabilityState : AustralianOriginCapabilityState
canonicalAustralianOriginCapabilityState =
  australianOriginCapabilityState true true true true false false false false false

data ExistingCountryOriginSystemProvesSettlementClassifier : Set where
existingCountryOriginSystemDoesNotProveSettlementClassifier : ExistingCountryOriginSystemProvesSettlementClassifier → ⊥
existingCountryOriginSystemDoesNotProveSettlementClassifier ()

data ExistingImportDeclarationProvesLowIncrementalCost : Set where
existingImportDeclarationDoesNotProveLowIncrementalCost : ExistingImportDeclarationProvesLowIncrementalCost → ⊥
existingImportDeclarationDoesNotProveLowIncrementalCost ()

data CountryLabelEqualsProductionLocation : Set where
countryLabelDoesNotEqualProductionLocation : CountryLabelEqualsProductionLocation → ⊥
countryLabelDoesNotEqualProductionLocation ()

implementationAnchor : Australia.AustralianImplementationFrontier
implementationAnchor = Australia.canonicalAustralianImplementationFrontier

businessObligationAnchor : Obligation.PolicyEffectObligation
businessObligationAnchor = Obligation.businessMechanism
