module DASHI.Chemistry.HydrogenFuelCycleAtomicIdentityExact where

-- Attribution and boundary:
-- Atomic proton-number identity is owned by the existing
-- DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact,
-- with the historical formalisation attribution retained there.
-- Element target/atomic numbers are reused from the existing
-- DASHI.Promotion.ChemistryFiniteRuleTargets owner.
-- Standard atomic weight convention belongs to Prohaska et al.,
-- "Standard atomic weights of the elements 2021", DOI
-- 10.1515/pac-2019-0603, as explicitly attributed in existing DASHI
-- AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact.
-- This user-directed, ChatGPT-authored adapter does NOT discover the
-- periodic table, and does NOT turn standard weights into isotope masses.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic
import DASHI.Promotion.ChemistryFiniteRuleTargets as Targets
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact as Mass

-- Hydrogen, carbon, and oxygen are element identities by proton number.
-- Neutron counts here are purely identity fixtures, not empirical isotope
-- allocations or natural-abundance claims.
hIndex : Atomic.AtomicIndex
hIndex = Atomic.neutralAt 1 0

cIndex : Atomic.AtomicIndex
cIndex = Atomic.neutralAt 6 6

oIndex : Atomic.AtomicIndex
oIndex = Atomic.neutralAt 8 8

hAtomicNumberMatchesTarget :
  Atomic.protonNumber hIndex ≡ Targets.atomicNumber Targets.hydrogen
hAtomicNumberMatchesTarget = refl

cAtomicNumberMatchesTarget :
  Atomic.protonNumber cIndex ≡ Targets.atomicNumber Targets.carbon
cAtomicNumberMatchesTarget = refl

oAtomicNumberMatchesTarget :
  Atomic.protonNumber oIndex ≡ Targets.atomicNumber Targets.oxygen
oAtomicNumberMatchesTarget = refl

hNeutral : Atomic.Neutral hIndex
hNeutral = refl

cNeutral : Atomic.Neutral cIndex
cNeutral = refl

oNeutral : Atomic.Neutral oIndex
oNeutral = refl

-- Each molecular mass number is a sum of the EXISTING rounded abridged
-- standard atomic weight conventions in milli-u; this is neither an exact
-- isotope mass nor a source-paid thermochemical molecular enthalpy.
hMassMilliU : Nat
hMassMilliU = Mass.milliUnifiedAtomicMassUnits Mass.hydrogenMass

cMassMilliU : Nat
cMassMilliU = Mass.milliUnifiedAtomicMassUnits Mass.carbonMass

oMassMilliU : Nat
oMassMilliU = Mass.milliUnifiedAtomicMassUnits Mass.oxygenMass

waterConventionMassMilliU : Nat
waterConventionMassMilliU = 2 * hMassMilliU + oMassMilliU

methaneConventionMassMilliU : Nat
methaneConventionMassMilliU = cMassMilliU + 4 * hMassMilliU

carbonDioxideConventionMassMilliU : Nat
carbonDioxideConventionMassMilliU = cMassMilliU + 2 * oMassMilliU

waterMassConventionRegression :
  waterConventionMassMilliU ≡ 18015
waterMassConventionRegression = refl

methaneMassConventionRegression :
  methaneConventionMassMilliU ≡ 16043
methaneMassConventionRegression = refl

carbonDioxideMassConventionRegression :
  carbonDioxideConventionMassMilliU ≡ 44009
carbonDioxideMassConventionRegression = refl

-- Projecting atomic number does not prove the isotope distribution or that
-- any experimental mass/energy conversion factor has been calibrated.
record AtomicMolarBridgeReceipt : Set where
  field
    isotopeAndStandardWeightScope : Set
    moleculeObjectAndCompositionVerified : Set
    moleCountAndAvogadroConventionVerified : Set
    measuredGasFlowToAmountConversion : Set
    energyPerMoleSourceAndUncertainty : Set
