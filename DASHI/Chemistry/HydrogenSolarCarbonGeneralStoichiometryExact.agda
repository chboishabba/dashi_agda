module DASHI.Chemistry.HydrogenSolarCarbonGeneralStoichiometryExact where

-- General power-station carbon recycling source integration (2026-11-10).
-- User-directed application: co-located PV; water electrolysis; exhaust/DAC
-- CO2 converted to additional hydrocarbon fuel, reducing virgin extraction.
-- Car battery-powered hydrogen assistance is a distinct application.
--
-- Attribution: empirical atomic numbers and mass convention remain owned
-- by existing DASHI Atomic369, periodic and SI modules; conventional
-- combustion, water electrolysis, and hydrogenation equations are scientific
-- prior art, not original to the user, ChatGPT, McLaren or this module.
-- A balanced net reaction is not proof that a reactor produces C_xH_(2b).

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

import DASHI.Physics.Units.SI as SI
import DASHI.Chemistry.HydrogenFuelCycleAtomicIdentityExact as Atomic
import DASHI.Chemistry.HydrogenFuelCycleTwoApplicationsExact as Applications

-- A general saturated/unsaturated or cyclic idealised hydrocarbon formula.
-- x counts carbon atoms, 2b hydrogen atoms. The even-hydrogen family
-- includes methane (x=1,b=2), alkanes (b=x+1), many liquid surrogates.
-- Odd-hydrogen pseudo-formulas need a doubled/formal-rational carrier.
record Hydrocarbon : Set where
  constructor hydrocarbon
  field
    carbon : Nat
    hydrogenPairs : Nat
open Hydrocarbon public

-- Use TWO molecules to keep every oxygen coefficient integral.
-- Net synthesis:
--   2x CO2 + 2b H2O -> 2 CxH(2b) + (2x+b) O2.
-- Combustion is exactly the reverse net atom ledger.
--
-- Mechanism decomposition:
--   electrolysis: (4x+2b) H2O -> (4x+2b) H2 +(2x+b) O2
--   hydrogenation: 2x CO2 +(4x+2b) H2 ->
--                  2 CxH(2b) +4x H2O
--   net after cancelling 4x recycled water: 2b H2O consumed.

co2Feed : Hydrocarbon → Nat
co2Feed f = 2 * carbon f

grossElectrolysisWater : Hydrocarbon → Nat
grossElectrolysisWater f = 4 * carbon f + 2 * hydrogenPairs f

producedHydrogen : Hydrocarbon → Nat
producedHydrogen = grossElectrolysisWater

electrolyserOxygen : Hydrocarbon → Nat
electrolyserOxygen f = 2 * carbon f + hydrogenPairs f

synthesisWaterReturn : Hydrocarbon → Nat
synthesisWaterReturn f = 4 * carbon f

netWater : Hydrocarbon → Nat
netWater f = 2 * hydrogenPairs f

synthesisedHydrocarbonMolecules : Nat
synthesisedHydrocarbonMolecules = 2

-- The oxygen released by water splitting exactly matches the amount
-- needed for stoichiometric combustion of the regenerated hydrocarbon.
oxygenClosesCombustion :
  (f : Hydrocarbon) →
  electrolyserOxygen f ≡ 2 * carbon f + hydrogenPairs f
oxygenClosesCombustion f = refl

-- Gross electrolyser intake = net water + water recovered from synthesis.
grossWaterEqualsNetPlusRecovered :
  (f : Hydrocarbon) →
  grossElectrolysisWater f
    ≡ netWater f + synthesisWaterReturn f
grossWaterEqualsNetPlusRecovered f =
  solve 2
    (λ x b → ((con 4 :* x) :+ (con 2 :* b))
      := ((con 2 :* b) :+ (con 4 :* x)))
    refl (carbon f) (hydrogenPairs f)

-- Total input atom counts for 2x CO2 + 2b H2O:
-- C=2x, H=4b, O=4x+2b.
-- Output for 2 CxH2b + (2x+b) O2:
-- C=2x, H=4b, O=2*(2x+b).
netCarbonConserved :
  (f : Hydrocarbon) →
  2 * carbon f ≡ synthesisedHydrocarbonMolecules * carbon f
netCarbonConserved f = refl

netHydrogenConserved :
  (f : Hydrocarbon) →
  2 * netWater f
    ≡ synthesisedHydrocarbonMolecules * (2 * hydrogenPairs f)
netHydrogenConserved f = refl

netOxygenConserved :
  (f : Hydrocarbon) →
  2 * co2Feed f + netWater f ≡ 2 * electrolyserOxygen f
netOxygenConserved f =
  solve 2
    (λ x b →
      ((con 2 :* (con 2 :* x)) :+ (con 2 :* b))
      := (con 2 :* ((con 2 :* x) :+ b)))
    refl (carbon f) (hydrogenPairs f)

-- Exact two-molecule molecule counts for a methane synthesis route:
-- 2 CO2 + 4 H2O -> 2 CH4 + 4 O2.
methane : Hydrocarbon
methane = hydrocarbon 1 2

methaneHydrogenDemand :
  producedHydrogen methane ≡ 8
methaneHydrogenDemand = refl

methaneGrossWater :
  grossElectrolysisWater methane ≡ 8
methaneGrossWater = refl

methaneNetWater :
  netWater methane ≡ 4
methaneNetWater = refl

methaneCO2Feed :
  co2Feed methane ≡ 2
methaneCO2Feed = refl

methaneOxygen :
  electrolyserOxygen methane ≡ 4
methaneOxygen = refl

-- SI and atomic dimensions are inherited, not reimplemented.
hydrogenProtonIdentity = Atomic.hAtomicNumberMatchesTarget
carbonProtonIdentity = Atomic.cAtomicNumberMatchesTarget
oxygenProtonIdentity = Atomic.oAtomicNumberMatchesTarget

record HydrocarbonSynthesisReceipt (f : Hydrocarbon) : Set₁ where
  field
    carbonSourceAndIdentity : Applications.CarbonOrigin
    solarInputMeasured : SI.Measurement SI.Energy SI.unitScale
    molecularProductIdentityAssay : Set
    hydrogenActualFlowAndConversion : Set
    waterAndOxygenProcessStreamsMeasured : Set
    measuredCarbonCaptureYield : Set
    catalyticKineticFeasibility : Set
    heatingValueAndUncertaintySource : Set
    recycleProcessHeatAndStorageBoundary : Set
