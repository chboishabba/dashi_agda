module DASHI.Physics.Photovoltaic.PV369G173MultiJunctionLossFrontierExact where

-- PV P5/P7: exact rational-grid bookkeeping for the already-owned
-- exploratory ASTM G173 one-sun radiative model. All percentages below
-- have units 0.001 percentage point of incident AM1.5G energy.
-- The prior optimizer was numerical/noncertified; do NOT upgrade these
-- numbers to certified optima, actual devices, or a material/369 proof.
--
-- Reuses PV369NetHalfThresholdExact for the strict 50% threshold and
-- original Circuit36927RecoveryEnergyBoundExact for inductive <=.
-- No thermal/chemical co-product counted in electric numerator.
-- Agda Golden kernel typecheck still OPEN.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Photovoltaic.PV369NetHalfThresholdExact as Net

solarUnitGrid halfSolarUnits : Nat
solarUnitGrid = 100000
halfSolarUnits = 50000

data Contacts : Set where
  twoTerminal independentTerminal : Contacts

data Junctions : Set where
  oneJ twoJ threeJ fourJ fiveJ : Junctions

-- Percent x 1000, from previous UNVERIFIED-GLOBAL-OPTIMUM G173 model.
modelGrossElectricalUnits : Contacts -> Junctions -> Nat
modelGrossElectricalUnits twoTerminal oneJ = 33773
modelGrossElectricalUnits twoTerminal twoJ = 45824
modelGrossElectricalUnits twoTerminal threeJ = 51741
modelGrossElectricalUnits twoTerminal fourJ = 52162
modelGrossElectricalUnits twoTerminal fiveJ = 53553
modelGrossElectricalUnits independentTerminal oneJ = 33773
modelGrossElectricalUnits independentTerminal twoJ = 46177
modelGrossElectricalUnits independentTerminal threeJ = 51867
modelGrossElectricalUnits independentTerminal fourJ = 56077
modelGrossElectricalUnits independentTerminal fiveJ = 58532

-- Source-preserving strict net integer budget, no hidden subtraction.
-- Losses are counted in SOLAR percentage-point units, not as a
-- percentage of gross electrical output. The actual physical loss source
-- would still require aperture, contact and optical measurements.
record ModelNetLossBudget : Set where
  field
    contacts : Contacts
    numberOfJunctions : Junctions
    opticalLoss nonradiativeLoss mismatchOrConverterLoss : Nat
    contactLoss thermalAndAuxLoss modeledNetElectric : Nat
    sourceEnergyBalance :
      modelGrossElectricalUnits contacts numberOfJunctions
      ≡ modeledNetElectric +
       (opticalLoss + (nonradiativeLoss +
       (mismatchOrConverterLoss + (contactLoss + thermalAndAuxLoss))))

    strictlyExceedsHalfSolar :
      Bound._≤_ (suc halfSolarUnits) modeledNetElectric

-- 2T3J: 51.741% - 1.740% = 50.001% strictly PASS (MODEL ONLY).
twoTerminalThreeJModelSafe : ModelNetLossBudget
twoTerminalThreeJModelSafe = record
  { contacts = twoTerminal
  ; numberOfJunctions = threeJ
  ; opticalLoss = 600
  ; nonradiativeLoss = 700
  ; mismatchOrConverterLoss = 200
  ; contactLoss = 100
  ; thermalAndAuxLoss = 140
  ; modeledNetElectric = 50001
  ; sourceEnergyBalance = refl
  ; strictlyExceedsHalfSolar = Bound.≤-append 50001 0
  }

-- 4T4J: 56.077% - 6.076% = 50.001% strictly PASS (MODEL ONLY).
fourTerminalFourJModelSafe : ModelNetLossBudget
fourTerminalFourJModelSafe = record
  { contacts = independentTerminal
  ; numberOfJunctions = fourJ
  ; opticalLoss = 1000
  ; nonradiativeLoss = 1500
  ; mismatchOrConverterLoss = 900
  ; contactLoss = 1000
  ; thermalAndAuxLoss = 1676
  ; modeledNetElectric = 50001
  ; sourceEnergyBalance = refl
  ; strictlyExceedsHalfSolar = Bound.≤-append 50001 0
  }

-- At loss exactly 1.741 or 6.077 percentage points, net is 50.000%;
-- both FAIL the strict threshold by the prior existing generic no-go.
twoTerminalThreeJHeadroom : 50000 + 1741 ≡ modelGrossElectricalUnits twoTerminal threeJ
twoTerminalThreeJHeadroom = refl

fourTerminalFourJHeadroom : 50000 + 6077 ≡ modelGrossElectricalUnits independentTerminal fourJ
fourTerminalFourJHeadroom = refl

fourTerminalFiveJHeadroom : 50000 + 8532 ≡ modelGrossElectricalUnits independentTerminal fiveJ
fourTerminalFiveJHeadroom = refl

exactHalfFails : Bound._≤_ (suc halfSolarUnits) halfSolarUnits -> Net.False
exactHalfFails = Net.successorNotLeItself halfSolarUnits

-- These witnesses describe ARITHMETIC on a previous numerical output, not
-- a real module or experimentally certified one-sun architecture.
