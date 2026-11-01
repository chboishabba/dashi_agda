module DASHI.Physics.QuantumVacuum.HarmonicOscillatorDoubledEnergyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- DENOMINATOR-FREE EXACT OSCILLATOR SPINE
--
-- Instead of making rational normalisation part of the primitive proof, use
-- the equivalent doubled-energy coordinate
--
--   2 E_n = (2 n + 1) hbar omega.
--
-- In normalized units hbar = 1 this is the exact Nat polynomial
--
--   doubledEnergy omega n = (2 n + 1) * omega.
--
-- The ground value is therefore omega and every excitation adds 2*omega.
-- A later rational interpretation divides this coordinate by two.
------------------------------------------------------------------------

doubledOccupation : Nat → Nat
doubledOccupation n = 2 * n

oddLevel : Nat → Nat
oddLevel n = doubledOccupation n + 1

doubledEnergy : Nat → Nat → Nat
doubledEnergy omega n = oddLevel n * omega

doubledZeroPointEnergy : Nat → Nat
doubledZeroPointEnergy omega = omega

doubledExcitationEnergy : Nat → Nat → Nat
doubledExcitationEnergy omega n = doubledOccupation n * omega

groundDoubledEnergy :
  (omega : Nat) →
  doubledEnergy omega 0 ≡ doubledZeroPointEnergy omega
groundDoubledEnergy omega = refl

groundDoubledExcitationIsZero :
  (omega : Nat) →
  doubledExcitationEnergy omega 0 ≡ 0
groundDoubledExcitationIsZero omega = refl

------------------------------------------------------------------------
-- Exact decomposition:
--
--   2 E_n = 2 DeltaE_n + 2 E_0
--
-- in the denominator-free coordinate.
------------------------------------------------------------------------

record DoubledSpectrumDecompositionReceipt (omega n : Nat) : Set where
  field
    decomposition :
      doubledEnergy omega n ≡
      doubledExcitationEnergy omega n + doubledZeroPointEnergy omega

open DoubledSpectrumDecompositionReceipt public

------------------------------------------------------------------------
-- Ground-minimality receipt over the concrete Nat instance.
--
-- The arithmetic producer is kept as a named receipt because downstream code
-- needs the order theorem, while the polynomial formulas themselves remain
-- definitional/computational.  This separates ordinary Nat-order library
-- plumbing from the physical zero-point ownership.
------------------------------------------------------------------------

record ConcreteGroundMinimalityReceipt (omega : Nat) : Set where
  field
    positiveFrequency : 0 < omega
    groundMinimal :
      (n : Nat) →
      doubledZeroPointEnergy omega ≤ doubledEnergy omega n

open ConcreteGroundMinimalityReceipt public

record ConcreteOscillatorHypervoxel : Set where
  field
    frequency : Nat
    frequencyPositive : 0 < frequency
    occupation : Nat
    groundReceipt : ConcreteGroundMinimalityReceipt frequency
    reading : String

open ConcreteOscillatorHypervoxel public

------------------------------------------------------------------------
-- A strictly positive doubled ground assignment still has zero excitation at
-- n = 0.  These are different coordinates and must not be conflated.
------------------------------------------------------------------------

record ZeroPointExcitationSeparation (omega : Nat) : Set where
  field
    frequencyPositive : 0 < omega
    groundDoubledEnergyPositive : 0 < doubledZeroPointEnergy omega
    groundExcitationZero : doubledExcitationEnergy omega 0 ≡ 0

open ZeroPointExcitationSeparation public

zeroPointExcitationSeparation :
  (omega : Nat) →
  0 < omega →
  ZeroPointExcitationSeparation omega
zeroPointExcitationSeparation omega positive =
  record
    { frequencyPositive = positive
    ; groundDoubledEnergyPositive = positive
    ; groundExcitationZero = refl
    }

------------------------------------------------------------------------
-- Typed interpretation boundary.
--
-- This finite Nat coordinate owns 2E, not E.  A consumer that wants the usual
-- E_n = hbar*omega*(n + 1/2) must supply an interpretation that divides by 2
-- in a scalar carrier.  That bridge is deliberately explicit.
------------------------------------------------------------------------

record HalfScaleInterpretation : Set₁ where
  field
    Scalar : Set
    interpretDoubledEnergy : Nat → Scalar
    half : Scalar
    hbar : Scalar
    frequencyScalar : Nat → Scalar
    occupationScalar : Nat → Scalar
    _+_ _*_ : Scalar → Scalar → Scalar

    oscillatorLaw :
      (omega n : Nat) →
      interpretDoubledEnergy (doubledEnergy omega n) ≡
      (hbar * frequencyScalar omega) * (occupationScalar n + half)

    groundLaw :
      (omega : Nat) →
      interpretDoubledEnergy (doubledZeroPointEnergy omega) ≡
      (hbar * frequencyScalar omega) * half

open HalfScaleInterpretation public

finiteDoubledCarrierIsRawQFTVacuumEnergy : Bool
finiteDoubledCarrierIsRawQFTVacuumEnergy = false

finiteDoubledCarrierIsExtractableReservoir : Bool
finiteDoubledCarrierIsExtractableReservoir = false

finiteDoubledCarrierIsRawQFTVacuumEnergyIsFalse :
  finiteDoubledCarrierIsRawQFTVacuumEnergy ≡ false
finiteDoubledCarrierIsRawQFTVacuumEnergyIsFalse = refl

finiteDoubledCarrierIsExtractableReservoirIsFalse :
  finiteDoubledCarrierIsExtractableReservoir ≡ false
finiteDoubledCarrierIsExtractableReservoirIsFalse = refl
