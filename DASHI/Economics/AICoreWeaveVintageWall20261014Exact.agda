module DASHI.Economics.AICoreWeaveVintageWall20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICoreWeaveOSINTCapacityVintage20261014Exact as Capacity
import DASHI.Economics.AIAccountingFinancingLifeGap20261012Exact as LifeGap

------------------------------------------------------------------------
-- CAPACITY-VINTAGE WALL UNDER SELECTED 36/48-MONTH FINANCING HORIZONS
--
-- This composes source-paid capacity vintages with the separately acquired
-- lender-style 36-48 month collateral/economic horizon only as a scenario map.
-- It dates when cohorts ENTER those horizon windows. It does not assert that
-- CoreWeave retires, replaces, impairs or refinances equipment on those dates.
------------------------------------------------------------------------

record VintageWallScenario : Set where
  constructor vintage-wall-scenario
  field
    selectedCapacityMW : Nat
    alreadyOr2026At36MonthsMW : Nat
    y2027At36MonthsMW : Nat
    y2028At36MonthsMW : Nat
    h12029At36MonthsMW : Nat
    alreadyOr2026At48MonthsMW : Nat
    y2027At48MonthsMW : Nat
    y2028At48MonthsMW : Nat
    y2029At48MonthsMW : Nat
    h12030At48MonthsMW : Nat
    cumulative36MonthWindowByEnd2028MW : Nat
    cumulative48MonthWindowByEnd2029MW : Nat
    selectedCumulativeShareBp : Nat
    replacementForecast : Bool
    impairmentForecast : Bool
    refinancingForecast : Bool

open VintageWallScenario public

coreWeaveSelectedVintageWall : VintageWallScenario
coreWeaveSelectedVintageWall = vintage-wall-scenario
  1500
  70 290 490 650
  10 60 290 490 650
  850 850 5666
  false false false

cumulative36MonthWindowByEnd2028Is850 :
  cumulative36MonthWindowByEnd2028MW coreWeaveSelectedVintageWall ≡ 850
cumulative36MonthWindowByEnd2028Is850 = refl

cumulative48MonthWindowByEnd2029Is850 :
  cumulative48MonthWindowByEnd2029MW coreWeaveSelectedVintageWall ≡ 850
cumulative48MonthWindowByEnd2029Is850 = refl

selectedShareBpIs5666 :
  selectedCumulativeShareBp coreWeaveSelectedVintageWall ≡ 5666
selectedShareBpIs5666 = refl

selectedCapacityMatchesOSINTFloor :
  selectedCapacityMW coreWeaveSelectedVintageWall ≡
  Capacity.conservativeTotalActiveMW Capacity.coreWeaveJune2026CapacityVintage
selectedCapacityMatchesOSINTFloor = refl

data VintageWallImpliesReplacementForecastPermission : Set where
data VintageWallImpliesImpairmentPermission : Set where
data VintageWallImpliesRefinancingPermission : Set where

vintageWallDoesNotCreateReplacementForecast :
  VintageWallImpliesReplacementForecastPermission → ⊥
vintageWallDoesNotCreateReplacementForecast ()

vintageWallDoesNotCreateImpairment : VintageWallImpliesImpairmentPermission → ⊥
vintageWallDoesNotCreateImpairment ()

vintageWallDoesNotCreateRefinancing : VintageWallImpliesRefinancingPermission → ⊥
vintageWallDoesNotCreateRefinancing ()

boundary : String
boundary =
  "Composing the selected June-2026 1.5GW capacity-vintage floor with a 36-month scenario places roughly 70 MW in/by 2026, 290 MW in 2027, 490 MW in 2028 and 650 MW in H1-2029; the analogous 48-month wall shifts those waves about one year later. Thus 850 MW, 56.66 percent of the selected capacity floor, has entered the 36-month window by end-2028 and the 48-month window by end-2029. These are exposure-calendar coordinates only. They do not predict replacement, impairment, refinancing, residual value or actual economic obsolescence."
