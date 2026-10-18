module DASHI.ComputerScience.TekumTernaryStoredProgramExecutionExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.FixedNineBitFramed27WordStorageExact as Storage
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime

------------------------------------------------------------------------
-- Concrete machine fixture: Tekum regime codes are stored as bounded naturals,
-- may be represented through the existing framed ternary-27 storage fibre, and
-- execute through the same radix-neutral machine after decoding.

regimeIndex : Regime.RegimeCode → Nat
regimeIndex Regime.rm7 = 0
regimeIndex Regime.rm6 = 1
regimeIndex Regime.rm5 = 2
regimeIndex Regime.rm4 = 3
regimeIndex Regime.rm3 = 4
regimeIndex Regime.rm2 = 5
regimeIndex Regime.rm1 = 6
regimeIndex Regime.r0  = 7
regimeIndex Regime.rp1 = 8
regimeIndex Regime.rp2 = 9
regimeIndex Regime.rp3 = 10
regimeIndex Regime.rp4 = 11
regimeIndex Regime.rp5 = 12
regimeIndex Regime.rp6 = 13
regimeIndex Regime.rp7 = 14

regimeMemory : Regime.RegimeCode → List Nat
regimeMemory r = regimeIndex r ∷ []

ternaryStoredRegime :
  Regime.RegimeCode → List Storage.Ternary27Word3
ternaryStoredRegime r =
  Storage.encodeTernary27Memory (regimeMemory r)

decodedTernaryRegimeMemory :
  Regime.RegimeCode → List Nat
decodedTernaryRegimeMemory r =
  Storage.decodeTernary27Memory (ternaryStoredRegime r)

regimeStorageRoundTrip :
  (r : Regime.RegimeCode) →
  decodedTernaryRegimeMemory r ≡ regimeMemory r
regimeStorageRoundTrip Regime.rm7 = refl
regimeStorageRoundTrip Regime.rm6 = refl
regimeStorageRoundTrip Regime.rm5 = refl
regimeStorageRoundTrip Regime.rm4 = refl
regimeStorageRoundTrip Regime.rm3 = refl
regimeStorageRoundTrip Regime.rm2 = refl
regimeStorageRoundTrip Regime.rm1 = refl
regimeStorageRoundTrip Regime.r0 = refl
regimeStorageRoundTrip Regime.rp1 = refl
regimeStorageRoundTrip Regime.rp2 = refl
regimeStorageRoundTrip Regime.rp3 = refl
regimeStorageRoundTrip Regime.rp4 = refl
regimeStorageRoundTrip Regime.rp5 = refl
regimeStorageRoundTrip Regime.rp6 = refl
regimeStorageRoundTrip Regime.rp7 = refl

regimeEchoProgram : Machine.Program
regimeEchoProgram =
  Machine.loadMemory Machine.r0 0
  ∷ Machine.outputRegister Machine.r0
  ∷ Machine.halt
  ∷ []

nativeRegimeInitialState : Regime.RegimeCode → Machine.MachineState
nativeRegimeInitialState r =
  Machine.machineState
    0 regimeEchoProgram (regimeMemory r)
    (Machine.registerFile 0 0 0) [] false 0

ternaryRegimeInitialState : Regime.RegimeCode → Machine.MachineState
ternaryRegimeInitialState r =
  Machine.machineState
    0 regimeEchoProgram (decodedTernaryRegimeMemory r)
    (Machine.registerFile 0 0 0) [] false 0

ternaryInitialStateIsNative :
  (r : Regime.RegimeCode) →
  ternaryRegimeInitialState r ≡ nativeRegimeInitialState r
ternaryInitialStateIsNative r
  rewrite regimeStorageRoundTrip r = refl

nativeRegimeFinalState : Regime.RegimeCode → Machine.MachineState
nativeRegimeFinalState r =
  Machine.runFuel 3 (nativeRegimeInitialState r)

ternaryRegimeFinalState : Regime.RegimeCode → Machine.MachineState
ternaryRegimeFinalState r =
  Machine.runFuel 3 (ternaryRegimeInitialState r)

ternaryExecutionMatchesNative :
  (r : Regime.RegimeCode) →
  ternaryRegimeFinalState r ≡ nativeRegimeFinalState r
ternaryExecutionMatchesNative r
  rewrite ternaryInitialStateIsNative r = refl

positiveOuterRegimeEchoesFourteen :
  Machine.output (ternaryRegimeFinalState Regime.rp7) ≡ 14 ∷ []
positiveOuterRegimeEchoesFourteen = refl

record TekumStoredProgramBoundary : Set where
  constructor tekumStoredProgramBoundary
  field
    regimeCodecRunsThroughExistingTernaryStorage : Bool
    ternaryStorageDecodesToSameMachineMemory : Bool
    decodedMachineExecutionIsIdentical : Bool
    physicalTernaryALUTimingClaimed : Bool

canonicalTekumStoredProgramBoundary : TekumStoredProgramBoundary
canonicalTekumStoredProgramBoundary =
  tekumStoredProgramBoundary true true true false
