module DASHI.Physics.Closure.MonsterC3Native369ZetaCountingEnsembleExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AmmoniaMonster3BNative369FineCarrierExact as Native
import DASHI.Moonshine.Base369Monster3BMultiplicityTenByNineBidiExact as Ninety
import DASHI.Physics.Closure.MonsterC3UniformCountingEnsembleExact as Uniform
import DASHI.Physics.Laws.ThermodynamicStatisticalLaws as Thermo

------------------------------------------------------------------------
-- NATIVE-369 MICROSTATE COUNTING ENSEMBLE FOR THE ZETA SECTOR
--
-- Previous counting used anonymous Fin carriers.  The chemistry/Monster
-- cross-pollination now owns an exact model chart
--
--   Native369ZetaCoordinate
--     = Kernel6 x (Completed10 x T^2)
--     <-> X6 x Fin90
--
-- and the existing multiplicity arithmetic gives 729 * 90 = 65610.
-- We may therefore instantiate the mathematical counting ensemble directly on
-- the native-369 microstate carrier.  This still does not assert a physical
-- Hamiltonian, temperature, equiprobability, thermodynamic entropy or gravity.
------------------------------------------------------------------------

zetaStateCount : Nat
zetaStateCount = 65610

zetaCountAgreesWith729Times90 :
  Ninety.heisenbergTimesTenByNineDimension ≡ zetaStateCount
zetaCountAgreesWith729Times90 = Ninety.heisenbergTimesTenByNineIs65610

zetaWeightNumerator : Nat
zetaWeightNumerator = 1

zetaWeightDenominator : Nat
zetaWeightDenominator = 65610

zetaUniformWeight : Uniform.UniformProbability
zetaUniformWeight = Uniform.uniformProbability zetaWeightNumerator zetaWeightDenominator

zetaNormalization :
  zetaWeightNumerator * zetaStateCount ≡ zetaWeightDenominator
zetaNormalization = refl

data NativeZetaMacrostate : Set where
  completeNativeZetaCarrier : NativeZetaMacrostate

native369ZetaCountingEnsemble : Thermo.StatisticalEnsemble
native369ZetaCountingEnsemble = record
  { Microstate = Native.Native369ZetaCoordinate
  ; Macrostate = NativeZetaMacrostate
  ; Probability = Uniform.UniformProbability
  ; Energy = ⊤
  ; Parameter = ⊤
  ; PartitionValue = Nat
  ; Observable = ⊤
  ; Expectation = ⊤
  ; macrostate = λ _ → completeNativeZetaCarrier
  ; probability = λ _ _ → zetaUniformWeight
  ; microEnergy = λ _ → tt
  ; partitionFunction = λ _ → zetaStateCount
  ; expectation = λ _ _ → tt
  ; Normalised = λ _ → zetaNormalization
  ; EnsembleAdmissible = λ _ → ⊤
  }

record NativeZetaEnsembleBoundary : Set where
  constructor nativeZetaEnsembleBoundary
  field
    native369MicrostateCarrierPaid : Bool
    native369MicrostateCarrierPaidIsTrue : native369MicrostateCarrierPaid ≡ true
    zetaCardinality65610Paid : Bool
    zetaCardinality65610PaidIsTrue : zetaCardinality65610Paid ≡ true
    normalizedUniformCountingPaid : Bool
    normalizedUniformCountingPaidIsTrue : normalizedUniformCountingPaid ≡ true
    nativeUniformCountingIsPhysicalThermalEnsemble : Bool
    nativeUniformCountingIsPhysicalThermalEnsembleIsFalse :
      nativeUniformCountingIsPhysicalThermalEnsemble ≡ false
    unitEnergyPlaceholderIsPhysicalHamiltonian : Bool
    unitEnergyPlaceholderIsPhysicalHamiltonianIsFalse :
      unitEnergyPlaceholderIsPhysicalHamiltonian ≡ false
    physicalNH3StateAssignmentCreatesEquiprobability : Bool
    physicalNH3StateAssignmentCreatesEquiprobabilityIsFalse :
      physicalNH3StateAssignmentCreatesEquiprobability ≡ false
    countingMeasureCreatesEntropyGravity : Bool
    countingMeasureCreatesEntropyGravityIsFalse :
      countingMeasureCreatesEntropyGravity ≡ false
    interpretation : String

open NativeZetaEnsembleBoundary public

canonicalNativeZetaEnsembleBoundary : NativeZetaEnsembleBoundary
canonicalNativeZetaEnsembleBoundary =
  nativeZetaEnsembleBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "The Monster zeta-sector counting measure is now carried by the exact native-369 fine coordinate rather than an anonymous Fin carrier. This is a mathematical finite counting ensemble only; physical probabilities, Hamiltonian/density matrix and entropy-gravity interpretation remain separate payments."
