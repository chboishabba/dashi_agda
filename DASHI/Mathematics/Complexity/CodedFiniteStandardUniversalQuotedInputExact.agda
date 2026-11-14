module DASHI.Mathematics.Complexity.CodedFiniteStandardUniversalQuotedInputExact where

------------------------------------------------------------------------
-- ONE SELF-DELIMITING INPUT FOR A FIXED UNIVERSAL INTERPRETER
--
--   machineCode(p) || unary(zeroSymbol) || unary(oneSymbol) || quote(q(p))
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardSelfDelimitingCodeExact as MachineCode
import DASHI.Mathematics.Complexity.CodedFiniteStandardRawInterpreterExact as Raw
import DASHI.Mathematics.Complexity.FiniteSelfSpecializingProgramSelfDelimitingCodeExact as ProgramCode

mapBoolNat : Nat → Nat → List Bool → List Nat
mapBoolNat zeroSymbol oneSymbol [] = []
mapBoolNat zeroSymbol oneSymbol (false ∷ rest) =
  zeroSymbol ∷ mapBoolNat zeroSymbol oneSymbol rest
mapBoolNat zeroSymbol oneSymbol (true ∷ rest) =
  oneSymbol ∷ mapBoolNat zeroSymbol oneSymbol rest

record RawQuotedBodyInput : Set where
  constructor raw-quoted-body-input
  field
    machine : MachineCode.RawMachine
    zeroSymbol : Nat
    oneSymbol : Nat
    program : ProgramCode.RawProgram

open RawQuotedBodyInput public

encodeUniversalQuotedInput :
  (body : Coded.CodedFiniteStandardTM) →
  Fin.Fin (Coded.symbolCount body) →
  Fin.Fin (Coded.symbolCount body) →
  List Bool
encodeUniversalQuotedInput body zeroSymbol oneSymbol =
  MachineCode.append
    (MachineCode.selfDelimitingMachineCode body)
    (MachineCode.append
      (MachineCode.encodeNat (Fin.toℕ zeroSymbol))
      (MachineCode.append
        (MachineCode.encodeNat (Fin.toℕ oneSymbol))
        (ProgramCode.fixedPointQuote body)))

decodeUniversalQuotedInput : List Bool → Maybe RawQuotedBodyInput
decodeUniversalQuotedInput bits with MachineCode.decodeMachine bits
... | nothing = nothing
... | just (machine , afterMachine) with MachineCode.decodeNat afterMachine
...   | nothing = nothing
...   | just (zeroSymbol , afterZero) with MachineCode.decodeNat afterZero
...     | nothing = nothing
...     | just (oneSymbol , afterOne)
      with ProgramCode.decodeProgramFuel ProgramCode.five afterOne
...       | nothing = nothing
...       | just (program , []) =
          just (raw-quoted-body-input machine zeroSymbol oneSymbol program)
...       | just (program , _ ∷ _) = nothing

universalQuotedInputRoundTrip :
  (body : Coded.CodedFiniteStandardTM)
  (zeroSymbol oneSymbol : Fin.Fin (Coded.symbolCount body)) →
  decodeUniversalQuotedInput
    (encodeUniversalQuotedInput body zeroSymbol oneSymbol)
  ≡
  just
    (raw-quoted-body-input
      (MachineCode.rawMachineView body)
      (Fin.toℕ zeroSymbol)
      (Fin.toℕ oneSymbol)
      (ProgramCode.fixedPointRawView body))
universalQuotedInputRoundTrip body zeroSymbol oneSymbol
  rewrite
    MachineCode.decodeMachineAppend
      (MachineCode.rawMachineView body)
      (MachineCode.append
        (MachineCode.encodeNat (Fin.toℕ zeroSymbol))
        (MachineCode.append
          (MachineCode.encodeNat (Fin.toℕ oneSymbol))
          (ProgramCode.fixedPointQuote body)))
    | MachineCode.decodeNatAppend
        (Fin.toℕ zeroSymbol)
        (MachineCode.append
          (MachineCode.encodeNat (Fin.toℕ oneSymbol))
          (ProgramCode.fixedPointQuote body))
    | MachineCode.decodeNatAppend
        (Fin.toℕ oneSymbol)
        (ProgramCode.fixedPointQuote body)
    | ProgramCode.fixedPointQuoteParsesExact body = refl

ifBool : Bool → Nat → Nat → Nat
ifBool false zero one = zero
ifBool true zero one = one

rawStartOnQuote :
  MachineCode.RawMachine → Nat → Nat → List Bool → Raw.RawConfiguration
rawStartOnQuote machine zeroSymbol oneSymbol [] =
  Raw.raw-configuration
    []
    (MachineCode.initial machine)
    (MachineCode.blank machine)
    []
rawStartOnQuote machine zeroSymbol oneSymbol (bit ∷ rest) =
  Raw.raw-configuration
    []
    (MachineCode.initial machine)
    (ifBool bit zeroSymbol oneSymbol)
    (mapBoolNat zeroSymbol oneSymbol rest)

runCanonicalUniversalQuotedInput :
  (steps : Nat)
  (body : Coded.CodedFiniteStandardTM)
  (zeroSymbol oneSymbol : Fin.Fin (Coded.symbolCount body)) →
  Maybe Raw.RawConfiguration
runCanonicalUniversalQuotedInput steps body zeroSymbol oneSymbol =
  Raw.iterateRaw
    steps
    (MachineCode.rawMachineView body)
    (rawStartOnQuote
      (MachineCode.rawMachineView body)
      (Fin.toℕ zeroSymbol)
      (Fin.toℕ oneSymbol)
      (ProgramCode.fixedPointQuote body))

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- One canonical finite input round-trips to the exact raw body, Boolean-symbol
-- ABI and whole q tree.  No raw-program re-encoder or hidden meta-level program
-- argument is required by the fixed universal-machine route.
------------------------------------------------------------------------
