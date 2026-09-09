module DASHI.ComputerScience.ShorOrderClassicalQuantumMachineComparisonExact where

open import DASHI.Core.Prelude

import DASHI.Crypto.ShorFactoring as Shor
import DASHI.Crypto.ShorConcreteExamples as Examples
import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.ClassicalOrderFindingRegisterMachineExact as Classical

------------------------------------------------------------------------
-- SAME ORDER CONSUMER, DIFFERENT EXECUTION FIBRES
--
-- For any certified quantum Shor run of the existing 15/21 factoring problems,
-- the quantum recovered order equals the order field.  The ordinary classical
-- scan independently computes that same field.  Equality is therefore at the
-- arithmetic consumer only; no theorem identifies the execution paths or cost
-- coordinates.
------------------------------------------------------------------------

quantum15OrderMatchesClassical :
  (R : Shor.QuantumShorFactoringRun Examples.shor15Problem) →
  Shor.quantumRecoveredOrder Examples.shor15Problem R
  ≡ Machine.reg2 (Machine.registers Classical.order15Final)
quantum15OrderMatchesClassical R
  rewrite Shor.quantumRecoveredOrderIsSplitOrder Examples.shor15Problem R = refl

quantum21OrderMatchesClassical :
  (R : Shor.QuantumShorFactoringRun Examples.shor21Problem) →
  Shor.quantumRecoveredOrder Examples.shor21Problem R
  ≡ Machine.reg2 (Machine.registers Classical.order21Final)
quantum21OrderMatchesClassical R
  rewrite Shor.quantumRecoveredOrderIsSplitOrder Examples.shor21Problem R = refl

record ShorOrderCrossParadigmBoundary : Set where
  constructor shorOrderCrossParadigmBoundary
  field
    commonOrderConsumerExact : Bool
    classicalOrderMachineExecutable : Bool
    quantumSuccessfulRecoveryTheoremReused : Bool
    sameOrderImpliesSameExecutionPath : Bool
    classicalTransitionCountEqualsQuantumGateCount : Bool
    classicalRegisterCellsEqualQuantumBasisDimension : Bool

canonicalShorOrderCrossParadigmBoundary : ShorOrderCrossParadigmBoundary
canonicalShorOrderCrossParadigmBoundary =
  shorOrderCrossParadigmBoundary true true true false false false
