module DASHI.Economics.AICoreWeaveThreeClockCapitalRecovery20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AIAccountingFinancingLifeGap20261012Exact as Life
import DASHI.Economics.AICoreWeaveVintageWall20261014Exact as Wall
import DASHI.Economics.AICompanyReturnRolloverTrajectory2026Exact as Company
import DASHI.Economics.AICoreWeaveSameObjectFinancingClock20261016Exact as SameObject

secFilingKind : Source.SourceKind
secFilingKind = Source.namedSourceKind "primary SEC filing"

coreWeave2025ContractSource : Source.AttributedSource
coreWeave2025ContractSource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Annual report / shareholder materials for year ended December 31 2025"
  "SEC-filed annual-report surface"
  "2026"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000193/formars.pdf"
  secFilingKind
  "primary carrier for USD60.7B remaining performance obligations at 2025-12-31 and committed-contract weighted-average duration of approximately five years"
  Source.publicAttribution

------------------------------------------------------------------------
-- CLOCKS WITH CORRECTED AUTHORITY
--
-- A generic 36-48 month lender/collateral horizon remains a market scenario,
-- not a CoreWeave same-object financing-life observation.
-- CoreWeave's own filed GPU-backed agreements publicly use contractual
-- depreciation bases spanning 5.5-6.5 years, commonly six years.
------------------------------------------------------------------------

record ThreeClockWedge : Set where
  constructor three-clock-wedge
  field
    genericMarketHorizonLowerMonths : Nat
    genericMarketHorizonUpperMonths : Nat
    contractClockMonths : Nat
    bookClockMonths : Nat
    genericMarketBelowContract : Bool
    contractBelowBook : Bool
    genericMarketClockSameObject : Bool
    sameDefinitionAcrossClocks : Bool
    sameAssetPopulationAcrossClocks : Bool
    contractRealisationPaid : Bool
    retirementAtGenericMarketHorizonPaid : Bool

open ThreeClockWedge public

-- Compatibility aliases preserve downstream API while the names make clear
-- that the 36-48 month quantity is no longer a same-object CoreWeave fact.
lenderLowerMonths : ThreeClockWedge → Nat
lenderLowerMonths = genericMarketHorizonLowerMonths

lenderUpperMonths : ThreeClockWedge → Nat
lenderUpperMonths = genericMarketHorizonUpperMonths

lenderBelowContract : ThreeClockWedge → Bool
lenderBelowContract = genericMarketBelowContract

retirementAtLenderHorizonPaid : ThreeClockWedge → Bool
retirementAtLenderHorizonPaid = retirementAtGenericMarketHorizonPaid

coreWeaveThreeClockWedge : ThreeClockWedge
coreWeaveThreeClockWedge = three-clock-wedge
  36 48 60 72
  true true false false false false false

lenderLowerMonthsIs36 : genericMarketHorizonLowerMonths coreWeaveThreeClockWedge ≡ 36
lenderLowerMonthsIs36 = refl

contractClockMonthsIs60 : contractClockMonths coreWeaveThreeClockWedge ≡ 60
contractClockMonthsIs60 = refl

bookClockMonthsIs72 : bookClockMonths coreWeaveThreeClockWedge ≡ 72
bookClockMonthsIs72 = refl

selectedClockOrderingPaid :
  (genericMarketBelowContract coreWeaveThreeClockWedge ≡ true) ×
  (contractBelowBook coreWeaveThreeClockWedge ≡ true)
selectedClockOrderingPaid = refl , refl

genericClockNotSameObject : genericMarketClockSameObject coreWeaveThreeClockWedge ≡ false
genericClockNotSameObject = refl

sameObjectCoreWeaveFinancingClockPaid :
  SameObject.commonObservedContractualGPUUsefulLifeMonths SameObject.coreWeaveSameObjectFinancingClock ≡ 72
sameObjectCoreWeaveFinancingClockPaid = SameObject.sameObjectSixYearDepreciationPaid

oldAccountingFinancingGapNotPromotable :
  SameObject.old24To36MonthMismatchPromotable SameObject.coreWeaveSameObjectFinancingClock ≡ false
oldAccountingFinancingGapNotPromotable = SameObject.old24To36MonthMismatchNotPromotable

record CalendarOverlap : Set where
  constructor calendar-overlap
  field
    throughYear : Nat
    debtPrincipalDueMillionUSD : Nat
    debtDueShareBp : Nat
    selectedCapacityIn36MonthWindowMW : Nat
    selectedCapacityWindowShareBp : Nat
    sameAssetsIdentified : Bool
    sameFinancingFacilitiesIdentified : Bool
    provesRefinancingStress : Bool

open CalendarOverlap public

coreWeave2028CalendarOverlap : CalendarOverlap
coreWeave2028CalendarOverlap = calendar-overlap
  2028
  15013
  (Company.dueThrough2028ShareBp Company.coreWeavePrincipalMaturities)
  (Wall.cumulative36MonthWindowByEnd2028MW Wall.coreWeaveSelectedVintageWall)
  (Wall.selectedCumulativeShareBp Wall.coreWeaveSelectedVintageWall)
  false false false

debtDueThrough2028ShareBpIs4223 : debtDueShareBp coreWeave2028CalendarOverlap ≡ 4223
debtDueThrough2028ShareBpIs4223 = refl

capacity36MonthWindowThrough2028ShareBpIs5666 : selectedCapacityWindowShareBp coreWeave2028CalendarOverlap ≡ 5666
capacity36MonthWindowThrough2028ShareBpIs5666 = refl

data CalendarOverlapImpliesSameAssetsPermission : Set where
data ThreeClockWedgeImpliesImpairmentPermission : Set where
data ContractDurationImpliesCashRealisationPermission : Set where

calendarOverlapDoesNotIdentifySameAssets : CalendarOverlapImpliesSameAssetsPermission → ⊥
calendarOverlapDoesNotIdentifySameAssets ()

threeClockWedgeDoesNotCreateImpairment : ThreeClockWedgeImpliesImpairmentPermission → ⊥
threeClockWedgeDoesNotCreateImpairment ()

contractDurationDoesNotCreateCashRealisation : ContractDurationImpliesCashRealisationPermission → ⊥
contractDurationDoesNotCreateCashRealisation ()

boundary : String
boundary =
  "The earlier 36-48 month lender/collateral clock is retained only as a generic market stress scenario. Primary CoreWeave credit agreements now pay the stronger same-object fact: contractual GPU/Infrastructure depreciation bases span about 66-78 months and commonly use 72 months, including a six-year basis for contributed used GPUs. Therefore 36-48 < 60 < 72 is an arithmetic ordering across heterogeneous observations, not a CoreWeave lender/contract/book-life wedge, and the earlier 24-36 month CoreWeave accounting-versus-financing mismatch is not promotable. The selected 36-month vintage wall remains a scenario exposure calendar only. Shared timing still does not identify the same assets, facilities, lenders or customer contracts and does not prove refinancing stress, impairment or contract realisation."
