module DASHI.Chemistry.HydrogenFuelCycleMolarThermochemistryExact where

-- Attribution: water electrolysis and Sabatier reaction stoichiometry are
-- classical chemical prior art, not Michael McLaren discoveries.
-- SI energy/amount dimensions are BIPM definitions; existing DASHI SI owner
-- is reused. H2 HHV and any production conversion coefficients MUST come
-- from separately identified thermochemical/instrument sources.
-- The typed integration was user-directed and ChatGPT-drafted (2026-11-09).

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (false)
open import Data.Nat.Base using (_≤_)
open import Data.Nat.Properties as NP using (m≤m+n)
open import Relation.Binary.PropositionalEquality using (sym; subst)
import DASHI.Physics.Units.SI as SI
import DASHI.Chemistry.HydrogenFuelCycleExact as Fuel

-- The existing SI registry carries J and mol as DIFFERENT dimensions.
-- The chemistry production formula multiplies a numerical mol count by
-- J/mol, so the product can be injected as SI.Energy without pretending
-- the molar-energy value is itself a bulk joule measurement.

record MolarHHVSource : Set where
  field
    h2HHVJPerMole : Nat
    h2HHV : SI.Quantity SI.MolarEnergy SI.unitScale
    h2HHVMatches : h2HHV ≡ SI.posQ h2HHVJPerMole
    publication : String
    referenceLocator : String
    heatingValueDefinition : String
    referenceStateAndPhase : String
    uncertaintyAndCoverage : Set

open MolarHHVSource public

hydrogenBulkEnergy :
  Nat → MolarHHVSource → SI.Quantity SI.Energy SI.unitScale
hydrogenBulkEnergy hydrogenMoles source =
  SI.posQ (hydrogenMoles * h2HHVJPerMole source)

-- A meter's accumulated flow is not the actual amount unless it
-- is traceable to a calibrated amount-unit conversion and a run interval.
record HydrogenFlowReceipt : Set₁ where
  field
    source : MolarHHVSource
    totalHydrogenMoles : Nat
    flowMeasurement : SI.Measurement SI.Amount SI.unitScale
    moleUnit : SI.Measurement.unit flowMeasurement ≡ SI.mole
    sourceMagnitudeMatchesAmount :
      SI.Quantity.magnitude (SI.Measurement.value flowMeasurement)
      ≡ totalHydrogenMoles
    nonnegativeReading :
      SI.Quantity.negative (SI.Measurement.value flowMeasurement)
      ≡ false
    calibratedFlowIntegration : Set
    exactSameRunAndReferenceState : Set

open HydrogenFlowReceipt public

-- The gas-flow H2 energy is obtained by multiplication with a
-- source-controlled HHV, never by atomic-number or weight lookup alone.
meteredHydrogenEnergy :
  HydrogenFlowReceipt → SI.Quantity SI.Energy SI.unitScale
meteredHydrogenEnergy r =
  hydrogenBulkEnergy (totalHydrogenMoles r) (source r)

-- The same H2 mole inventory can be used in three roles, with Sabatier
-- requiring FOUR molecules of H2 for each methane molecule. This
-- exact mass partition is separate from kinetic reactor yield.
record HydrogenProcessAllocation : Set where
  field
    producedH2Moles : Nat
    directlyBurnedH2Moles : Nat
    methanatedCH4Moles : Nat
    storedH2Moles : Nat
    ventedH2Moles : Nat
    materialBalance :
      producedH2Moles ≡
        (directlyBurnedH2Moles + 4 * methanatedCH4Moles)
          + (storedH2Moles + ventedH2Moles)

open HydrogenProcessAllocation public

allocatedForReactor :
  HydrogenProcessAllocation → Nat
allocatedForReactor r = 4 * methanatedCH4Moles r

-- This is an exact allocation certificate, not a declaration of
-- completed Sabatier synthesis. Product assay and yield are separate.
record CarbonSynthesisReceipt : Set₁ where
  field
    allocation : HydrogenProcessAllocation
    capturedCarbonDioxideMoles : Nat
    carbonDioxideFedToReactorMoles : Nat
    producedMethaneMoles : Nat
    carbonDioxideWasSufficient :
      producedMethaneMoles ≤ carbonDioxideFedToReactorMoles
    methaneIsAllocation :
      producedMethaneMoles ≡ methanatedCH4Moles allocation
    carbonCapturedIsSufficient :
      carbonDioxideFedToReactorMoles ≤ capturedCarbonDioxideMoles
    hydrocarbonProductIdentityAssay : Set
    conversionYieldAndUncertainty : Set
    gasAndLiquidSeparationWorkReceipt : Set

open CarbonSynthesisReceipt public

-- Distinct from HHV, the standard-weight convention contains only an
-- approximation to molar masses and cannot create reaction enthalpies.
