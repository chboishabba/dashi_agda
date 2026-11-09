module DASHI.Chemistry.HydrogenFuelCycleNISTThermochemistryExact where

-- Scientific attribution (not device claims):
-- NIST Chemistry WebBook water (H2O) liquid standard enthalpy of formation:
-- -285.830 ± 0.040 kJ/mol at 298.15 K, CODATA Review / Cox, Wagman et al.
-- https://webbook.nist.gov/cgi/cbook.cgi?ID=C7732185&Mask=187&Units=SI
-- NIST Chemistry WebBook methane standard gas combustion enthalpy:
-- -890.35 ± 0.30 kJ/mol, Prosen and Rossini (1945), as indexed by NIST.
-- https://webbook.nist.gov/cgi/cbook.cgi?ID=C74828&Mask=1
--
-- Source datum magnitudes below are the positive HHV magnitudes of
-- EXOTHERMIC combustion enthalpies. They are reported reference-state
-- metrological quantities, NOT exact physical constants.
-- Classical chemical reactions and NIST compilation are not credited
-- to McLaren, the user, or ChatGPT. The typed numeric integration is
-- user-directed and ChatGPT-drafted (2026-11-09).

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
import DASHI.Physics.Units.SI as SI
import DASHI.Chemistry.HydrogenFuelCycleMolarThermochemistryExact as Thermo

record ReportedHHV : Set where
  constructor reported-hhv
  field
    magnitudeJPerMole : Nat
    uncertaintyJPerMole : Nat
    lowerJPerMole : Nat
    upperJPerMole : Nat
    lowerPlusUncertainty :
      lowerJPerMole + uncertaintyJPerMole ≡ magnitudeJPerMole
    magnitudePlusUncertainty :
      magnitudeJPerMole + uncertaintyJPerMole ≡ upperJPerMole
    sourceURL : String
    referenceState : String
    literatureAttribution : String

open ReportedHHV public

nistHydrogenHHV : ReportedHHV
nistHydrogenHHV = reported-hhv
  285830 40 285790 285870 refl refl
  "https://webbook.nist.gov/cgi/cbook.cgi?ID=C7732185&Mask=187&Units=SI"
  "H2(g) + 1/2 O2(g) -> H2O(l); standard reference 298.15 K"
  "NIST WebBook CODATA Review; Cox, Wagman et al. (1984)"

nistMethaneHHV : ReportedHHV
nistMethaneHHV = reported-hhv
  890350 300 890050 890650 refl refl
  "https://webbook.nist.gov/cgi/cbook.cgi?ID=C74828&Mask=1"
  "CH4(g) + 2 O2(g) -> CO2(g) + 2 H2O(l); standard reference"
  "NIST WebBook: Prosen and Rossini (1945) combustion measurement"

hydrogenHHVTyped :
  SI.Quantity SI.MolarEnergy SI.unitScale
hydrogenHHVTyped =
  SI.posQ (magnitudeJPerMole nistHydrogenHHV)

methaneHHVTyped :
  SI.Quantity SI.MolarEnergy SI.unitScale
methaneHHVTyped =
  SI.posQ (magnitudeJPerMole nistMethaneHHV)

-- 4 moles of H2 contain more HHV energy than 1 mole of CH4
-- under the stated reference-state conventions; the difference includes
-- exothermic methanation heat and is not free synthetic fuel.
fourHydrogenVersusMethaneHHVDifference :
  magnitudeJPerMole nistMethaneHHV + 252970
    ≡ 4 * magnitudeJPerMole nistHydrogenHHV
fourHydrogenVersusMethaneHHVDifference = refl

-- The stated uncertainties cannot reverse the basic inequality here.
-- These are bounds on quoted thermochemical numbers, not a complete
-- process-efficiency/temperature/pressure uncertainty analysis.
conservativeHHVGap :
  upperJPerMole nistMethaneHHV + 252510
    ≡ 4 * lowerJPerMole nistHydrogenHHV
conservativeHHVGap = refl

-- Source-controlled molecular H2 energy for an integral amount-of-substance
-- representation. An actual device still needs a flow meter and conversion
-- from time-integrated flow to moles with gas composition and calibration.
nistHydrogenBulkHHV :
  Nat → SI.Quantity SI.Energy SI.unitScale
nistHydrogenBulkHHV moles =
  SI.posQ (moles * magnitudeJPerMole nistHydrogenHHV)

-- This NIST compilation does not provide the reactor operating
-- temperature/pressure, HHV-versus-LHV field convention or device efficacy.
