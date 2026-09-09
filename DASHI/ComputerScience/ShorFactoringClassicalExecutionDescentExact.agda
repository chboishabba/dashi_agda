module DASHI.ComputerScience.ShorFactoringClassicalExecutionDescentExact where

open import DASHI.Core.Prelude

import DASHI.Crypto.FiniteFactorArithmetic as Factor
import DASHI.Crypto.ShorFactoring as Shor
import DASHI.Crypto.ShorConcreteExamples as Examples
import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.ModularExponentiationRegisterMachineExact as PowMachine
import DASHI.ComputerScience.ShorFactoringToClassicalBinaryTernaryMachineExact as FactorMachine

------------------------------------------------------------------------
-- SAME-OBJECT CLASSICAL DESCENT FROM THE EXISTING SHOR SPLIT
--
-- Certified Shor split
--   -> half-power x = a^(r/2) mod N
--   -> branch x-1 (for the two canonical fixtures)
--   -> Euclid gcd(N,x-1)
--   -> the same certified factor exposed by classicalShorFactor.
--
-- The half-power and gcd are both now produced by the same radix-neutral
-- ordinary machine family. Binary and framed-27 fibres remain representations
-- of those ordinary states, not alternate arithmetic semantics.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- N = 15.
------------------------------------------------------------------------

split15HalfPower : Nat
split15HalfPower = Factor.halfPower Factor.shorSplit15

machine15HalfPower : Nat
machine15HalfPower = Machine.reg0 (Machine.registers PowMachine.pow2Half15)

machine15HalfPowerIsSplitHalfPower : machine15HalfPower ≡ split15HalfPower
machine15HalfPowerIsSplitHalfPower = PowMachine.pow2Half15MatchesCertifiedHalfPower

machine15Branch : Nat
machine15Branch = machine15HalfPower ∸ 1

machine15BranchIsThree : machine15Branch ≡ 3
machine15BranchIsThree = refl

machine15Factor : Nat
machine15Factor = Machine.reg0 (Machine.registers FactorMachine.shor15BinaryFinal)

machine15FactorIsThree : machine15Factor ≡ 3
machine15FactorIsThree = refl

machine15FactorMatchesShor :
  machine15Factor ≡ proj₁ (Shor.classicalShorFactor Examples.shor15Problem)
machine15FactorMatchesShor = FactorMachine.shor15MachineMatchesCertifiedShorFactor

ternary15FactorMatchesBinary :
  Machine.reg0 (Machine.registers FactorMachine.shor15TernaryFinal)
  ≡ machine15Factor
ternary15FactorMatchesBinary = refl

------------------------------------------------------------------------
-- N = 21.
------------------------------------------------------------------------

split21HalfPower : Nat
split21HalfPower = Factor.halfPower Factor.shorSplit21

machine21HalfPower : Nat
machine21HalfPower = Machine.reg0 (Machine.registers PowMachine.pow2Half21)

machine21HalfPowerIsSplitHalfPower : machine21HalfPower ≡ split21HalfPower
machine21HalfPowerIsSplitHalfPower = PowMachine.pow2Half21MatchesCertifiedHalfPower

machine21Branch : Nat
machine21Branch = machine21HalfPower ∸ 1

machine21BranchIsSeven : machine21Branch ≡ 7
machine21BranchIsSeven = refl

machine21Factor : Nat
machine21Factor = Machine.reg0 (Machine.registers FactorMachine.shor21BinaryFinal)

machine21FactorIsSeven : machine21Factor ≡ 7
machine21FactorIsSeven = refl

machine21FactorMatchesShor :
  machine21Factor ≡ proj₁ (Shor.classicalShorFactor Examples.shor21Problem)
machine21FactorMatchesShor = FactorMachine.shor21MachineMatchesCertifiedShorFactor

ternary21FactorMatchesBinary :
  Machine.reg0 (Machine.registers FactorMachine.shor21TernaryFinal)
  ≡ machine21Factor
ternary21FactorMatchesBinary = refl

------------------------------------------------------------------------
-- One receipt states exactly which arrows have become executable.
------------------------------------------------------------------------

record ShorFactoringClassicalExecutionDescentReceipt : Set where
  constructor shorFactoringClassicalExecutionDescentReceipt
  field
    certifiedSplitIsExistingAuthority : Bool
    halfPowerProducedByOrdinaryMachine : Bool
    halfPowerMatchesExistingPowMod : Bool
    branchValueFeedsEuclid : Bool
    gcdProducedByOrdinaryMachine : Bool
    gcdFactorMatchesCertifiedShorFactor : Bool
    binaryRegisterRealizationExact : Bool
    ternary27RegisterRealizationExact : Bool
    quantumAndClassicalExecutionPathsIdentified : Bool
    representationCellCountPromotedToPhysicalCost : Bool
    genericAllModuliCorrectnessClosed : Bool

canonicalShorFactoringClassicalExecutionDescentReceipt :
  ShorFactoringClassicalExecutionDescentReceipt
canonicalShorFactoringClassicalExecutionDescentReceipt =
  shorFactoringClassicalExecutionDescentReceipt
    true true true true true true true true false false false
