module DASHI.Economics.AICoreWeaveAssetLifeObsolescenceBoundary20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AICoreWeaveCapexDecompositionNonidentifiability20261012Exact as Decomposition

------------------------------------------------------------------------
-- COREWEAVE ACCOUNTING LIFE / ECONOMIC OBSOLESCENCE BOUNDARY
--
-- CoreWeave's 2025 Form 10-K pays an entity-specific accounting useful-life
-- coordinate for technology equipment and an accounting treatment for ordinary
-- maintenance/repairs.  Those facts materially narrow the replacement-capex
-- acquisition problem, but they do not identify the economic retirement age,
-- installed-age distribution, refresh cadence or replacement-capex amount.
------------------------------------------------------------------------

secFilingKind : Source.SourceKind
secFilingKind = Source.namedSourceKind "primary SEC filing"

coreWeave2025AnnualReportSource : Source.AttributedSource
coreWeave2025AnnualReportSource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Annual report for year ended December 31 2025"
  "SEC Form 10-K"
  "2026"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000104/crwv-20251231.htm"
  secFilingKind
  "primary carrier for straight-line property/equipment depreciation, six-year technology-equipment estimated useful life, the 2023 five-to-six-year estimate change, and expensing of maintenance/repairs that do not extend asset lives"
  Source.publicAttribution

record AssetLifeObservation : Set where
  constructor asset-life-observation
  field
    company : String
    assetClass : String
    priorUsefulLifeMonths : Nat
    currentUsefulLifeMonths : Nat
    estimateChangeEffectiveYear : Nat
    straightLineDepreciation : Bool
    maintenanceRepairsNotExtendingLifeExpensed : Bool
    sourcePaid : Bool
    economicObsolescenceLifeIdentified : Bool
    installedAgeDistributionIdentified : Bool
    replacementScheduleIdentified : Bool
    replacementCapexAmountIdentified : Bool
    source : Source.AttributedSource

open AssetLifeObservation public

coreWeaveTechnologyEquipmentLife : AssetLifeObservation
coreWeaveTechnologyEquipmentLife = asset-life-observation
  "CoreWeave"
  "technology equipment used in data centers"
  60
  72
  2023
  true
  true
  true
  false
  false
  false
  false
  coreWeave2025AnnualReportSource

technologyEquipmentUsefulLifeMonthsIs72 :
  currentUsefulLifeMonths coreWeaveTechnologyEquipmentLife ≡ 72
technologyEquipmentUsefulLifeMonthsIs72 = refl

priorUsefulLifeMonthsWas60 :
  priorUsefulLifeMonths coreWeaveTechnologyEquipmentLife ≡ 60
priorUsefulLifeMonthsWas60 = refl

maintenanceRepairsExpensedIsPaid :
  maintenanceRepairsNotExtendingLifeExpensed coreWeaveTechnologyEquipmentLife ≡ true
maintenanceRepairsExpensedIsPaid = refl

installedAgeDistributionStillOpen :
  installedAgeDistributionIdentified coreWeaveTechnologyEquipmentLife ≡ false
installedAgeDistributionStillOpen = refl

replacementScheduleStillOpen :
  replacementScheduleIdentified coreWeaveTechnologyEquipmentLife ≡ false
replacementScheduleStillOpen = refl

------------------------------------------------------------------------
-- Cross-pollination into the capex-decomposition no-go.
------------------------------------------------------------------------

capexDecompositionStillNonIdentified : Bool
capexDecompositionStillNonIdentified =
  Decomposition.maintenanceReplacementStillRequiresExternalCoordinate

data AccountingLifeDeterminesEconomicObsolescencePermission : Set where
data AccountingLifeDeterminesInstalledAgeDistributionPermission : Set where
data AccountingLifeDeterminesReplacementCapexPermission : Set where

data ExpensedMaintenanceDeterminesCapitalisedReplacementPermission : Set where

accountingLifeDoesNotIdentifyEconomicObsolescence :
  AccountingLifeDeterminesEconomicObsolescencePermission → ⊥
accountingLifeDoesNotIdentifyEconomicObsolescence ()

accountingLifeDoesNotIdentifyInstalledAgeDistribution :
  AccountingLifeDeterminesInstalledAgeDistributionPermission → ⊥
accountingLifeDoesNotIdentifyInstalledAgeDistribution ()

accountingLifeDoesNotIdentifyReplacementCapex :
  AccountingLifeDeterminesReplacementCapexPermission → ⊥
accountingLifeDoesNotIdentifyReplacementCapex ()

expensedMaintenanceDoesNotIdentifyCapitalisedReplacement :
  ExpensedMaintenanceDeterminesCapitalisedReplacementPermission → ⊥
expensedMaintenanceDoesNotIdentifyCapitalisedReplacement ()

record ReplacementAcquisitionResidual : Set where
  constructor replacement-acquisition-residual
  field
    entityAccountingLifePaid : Bool
    aggregateCapexPaid : Bool
    maintenanceAccountingPolicyPaid : Bool
    installedAgeDistributionPaid : Bool
    retirementRefreshHistoryPaid : Bool
    growthVsReplacementCapitalisationPaid : Bool
    economicObsolescenceCalibrationPaid : Bool

open ReplacementAcquisitionResidual public

coreWeaveReplacementResidual : ReplacementAcquisitionResidual
coreWeaveReplacementResidual = replacement-acquisition-residual
  true true true false false false false

boundary : String
boundary =
  "CoreWeave's primary filing pays a six-year accounting useful life for technology equipment and states that ordinary maintenance/repairs not extending asset lives are expensed. This narrows the replacement-capex acquisition programme but does not identify economic obsolescence, installed asset ages, retirement/refresh timing, or capitalised replacement amounts. The aggregate-capex decomposition remains non-identifiable until those same-object coordinates are acquired."
