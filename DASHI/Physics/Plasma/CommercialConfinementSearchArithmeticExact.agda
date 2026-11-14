module DASHI.Physics.Plasma.CommercialConfinementSearchArithmeticExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Plasma.GreenwaldDensityOperatingEnvelopeBidiExact as Density
import DASHI.Physics.Plasma.CommercialFusionPlantObjectiveExact as Plant

------------------------------------------------------------------------
-- COMMERCIAL-CONFINEMENT SEARCH ARITHMETIC CONTRACT
--
-- The executable Python probe mirrors only bookkeeping identities and ordering
-- semantics.  It is deliberately not a reactor predictor: transport, stability,
-- wall lifetime, coil stress and economic coefficients remain empirical leaves.
------------------------------------------------------------------------

record GreenwaldArithmeticReceipt : Set₁ where
  constructor greenwald-arithmetic-receipt
  field
    numberDensityDimension : SI.Dimension
    numberDensityDimensionIsCanonical :
      numberDensityDimension ≡ Density.NumberDensity
    greenwaldEquationReference : String
    plasmaCurrentUnitReference : String
    minorRadiusUnitReference : String
    outputUnitReference : String
    executableReplayReference : String

open GreenwaldArithmeticReceipt public

canonicalGreenwaldArithmeticReceipt : GreenwaldArithmeticReceipt
canonicalGreenwaldArithmeticReceipt =
  greenwald-arithmetic-receipt
    Density.NumberDensity
    refl
    "n_G[10^20 m^-3] = I_p[MA] / (pi a[m]^2)"
    "MA"
    "m"
    "m^-3"
    "scripts/commercial_confinement_probe.py::greenwald_density_m3"

record NetElectricAccountingReceipt : Set where
  constructor net-electric-accounting-receipt
  field
    accountingIdentityReference : String
    grossPowerDimension : SI.Dimension
    netPowerDimension : SI.Dimension
    grossPowerIsPower : grossPowerDimension ≡ SI.Power
    netPowerIsPower : netPowerDimension ≡ SI.Power
    executableReplayReference : String

open NetElectricAccountingReceipt public

canonicalNetElectricAccountingReceipt : NetElectricAccountingReceipt
canonicalNetElectricAccountingReceipt =
  net-electric-accounting-receipt
    "P_net = P_gross - sum(P_recirculating loads)"
    SI.Power
    SI.Power
    refl
    refl
    "scripts/commercial_confinement_probe.py::net_electric_mw"

data SearchSense : Set where
  minimize maximize : SearchSense

record DeclaredCommercialSearchAxis : Set where
  constructor declared-commercial-search-axis
  field
    axisName : String
    sense : SearchSense
    semanticReference : String

open DeclaredCommercialSearchAxis public

record ExecutableSearchProbeBoundary : Set where
  constructor executable-search-probe-boundary
  field
    localPythonMayCheckBookkeepingIdentities : Bool
    localPythonMayCheckBookkeepingIdentitiesIsTrue :
      localPythonMayCheckBookkeepingIdentities ≡ true

    arbitraryToyCoefficientsProveArchitectureSuperiority : Bool
    arbitraryToyCoefficientsProveArchitectureSuperiorityIsFalse :
      arbitraryToyCoefficientsProveArchitectureSuperiority ≡ false

    paretoAxisDirectionsMustBeDeclared : Bool
    paretoAxisDirectionsMustBeDeclaredIsTrue :
      paretoAxisDirectionsMustBeDeclared ≡ true

    scalarizedToyOptimumMayPromoteCommercialDesign : Bool
    scalarizedToyOptimumMayPromoteCommercialDesignIsFalse :
      scalarizedToyOptimumMayPromoteCommercialDesign ≡ false

    empiricalLeavesStillRequireSameRegimeAuthority : Bool
    empiricalLeavesStillRequireSameRegimeAuthorityIsTrue :
      empiricalLeavesStillRequireSameRegimeAuthority ≡ true

canonicalExecutableSearchProbeBoundary : ExecutableSearchProbeBoundary
canonicalExecutableSearchProbeBoundary =
  executable-search-probe-boundary
    true refl
    false refl
    true refl
    false refl
    true refl

pythonProbeTestReference : String
pythonProbeTestReference = "scripts/test_commercial_confinement_probe.py"
