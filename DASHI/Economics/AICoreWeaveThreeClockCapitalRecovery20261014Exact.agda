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
-- THREE CLOCKS
--
-- 1. lender/collateral horizon: secondary market practice, 36-48 months;
-- 2. customer-contract duration: CoreWeave primary filing, about 60 months;
-- 3. accounting useful life: CoreWeave primary filing, 72 months.
--
-- Different semantics remain explicit. Ordering their horizons does not make
-- them one economic-life measure, nor identify the same financed assets.
------------------------------------------------------------------------

record ThreeClockWedge : Set where
  constructor three-clock-wedge
  field
    lenderLowerMonths : Nat
    lenderUpperMonths : Nat
    contractClockMonths : Nat
    bookClockMonths : Nat
    lenderBelowContract : Bool
    contractBelowBook : Bool
    sameDefinitionAcrossClocks : Bool
    sameAssetPopulationAcrossClocks : Bool
    contractRealisationPaid : Bool
    retirementAtLenderHorizonPaid : Bool

open ThreeClockWedge public

coreWeaveThreeClockWedge : ThreeClockWedge
coreWeaveThreeClockWedge = three-clock-wedge
  36 48 60 72
  true true false false false false

lenderLowerMonthsIs36 : lenderLowerMonths coreWeaveThreeClockWedge ≡ 36
lenderLowerMonthsIs36 = refl

contractClockMonthsIs60 : contractClockMonths coreWeaveThreeClockWedge ≡ 60
contractClockMonthsIs60 = refl

bookClockMonthsIs72 : bookClockMonths coreWeaveThreeClockWedge ≡ 72
bookClockMonthsIs72 = refl

selectedClockOrderingPaid :
  (lenderBelowContract coreWeaveThreeClockWedge ≡ true) ×
  (contractBelowBook coreWeaveThreeClockWedge ≡ true)
selectedClockOrderingPaid = refl , refl

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

debtDueThrough2028ShareBpIs4223 :
  debtDueShareBp coreWeave2028CalendarOverlap ≡ 4223
debtDueThrough2028ShareBpIs4223 = refl

capacity36MonthWindowThrough2028ShareBpIs5666 :
  selectedCapacityWindowShareBp coreWeave2028CalendarOverlap ≡ 5666
capacity36MonthWindowThrough2028ShareBpIs5666 = refl

data CalendarOverlapImpliesSameAssetsPermission : Set where
data ThreeClockWedgeImpliesImpairmentPermission : Set where
data ContractDurationImpliesCashRealisationPermission : Set where

calendarOverlapDoesNotIdentifySameAssets :
  CalendarOverlapImpliesSameAssetsPermission → ⊥
calendarOverlapDoesNotIdentifySameAssets ()

threeClockWedgeDoesNotCreateImpairment :
  ThreeClockWedgeImpliesImpairmentPermission → ⊥
threeClockWedgeDoesNotCreateImpairment ()

contractDurationDoesNotCreateCashRealisation :
  ContractDurationImpliesCashRealisationPermission → ⊥
contractDurationDoesNotCreateCashRealisation ()

boundary : String
boundary =
  "CoreWeave's public evidence supports three distinct clocks: a generic lender/collateral GPU horizon of roughly 36-48 months, CoreWeave committed contracts averaging about 60 months at year-end 2025, and a 72-month accounting useful life for technology equipment. The selected ordering 36-48 < 60 < 72 is therefore source-bounded but semantically heterogeneous. Separately, USD15.013B of principal (42.23 percent of the June-2026 maturity schedule) is due through 2028, while 850 MW (56.66 percent of the selected June-2026 1.5GW capacity floor) has entered the selected 36-month vintage window by end-2028. Shared calendar timing does not identify the same assets, facilities, lenders or customer contracts and does not itself prove refinancing stress, impairment or contract realisation."
