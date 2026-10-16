module DASHI.Mathematics.Complexity.PNotEqualsNPBehavioralSpecializerFrontierValidation where

------------------------------------------------------------------------
-- CURRENT BEHAVIOURAL SELF-SPECIALIZATION FRONTIER ROLLUP
--
-- This is a dependency/receipt surface, not a new fixed-point axiom.
-- It keeps the surviving constructive route reachable from the P9 max-cut:
--
--   actual coded machine
--     -> self-delimiting quote
--     -> executable raw parse/dispatch/tape semantics
--     -> typed-standard fidelity on every actual exact run
--     -> literal parser/scanner/equality compiler primitives
--     -> abstract specialization/diagonal fixed-point theorem
--     -> explicit timing Pareto (phase expansion vs compact XOR counter)
--     -> still-unpaid full literal specializer/interpreter assembly
--     -> still-unpaid final same-object resource fixed point.
--
-- Attribution boundary: the XOR/IIT sibling motivates one implementation
-- option only. No IIT theorem or phi quantity is imported here as complexity
-- or lower-bound authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

open import DASHI.Mathematics.Complexity.CodedFiniteStandardSelfDelimitingCodeExact
  using (selfDelimitingMachineCode; selfDelimitingRoundTrip)

open import DASHI.Mathematics.Complexity.CodedFiniteStandardRawInterpreterExact
  using (runSelfDelimitedCode; runActualCodeReducesToRawView)

open import DASHI.Mathematics.Complexity.CodedFiniteStandardRawInterpreterFidelityExact
  using
    ( rawNextExact
    ; rawIterateFollowsStandardRun
    ; selfDelimitedInterpreterFollowsStandardRun
    )

open import DASHI.Mathematics.Complexity.CodedFiniteUnaryDelimiterScannerExact
  using (scannerCode; scannerMachine; doneStateHasNoResidentRule)

open import DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityDeterminismExact
  using (dispatchUnique; equalityCode)

open import DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityClosureExact
  using (fieldEqualityMachine; equalSinkQuiescent; unequalSinkQuiescent)

open import DASHI.Mathematics.Complexity.PNotEqualsNPKleeneSpecializationFixedPointExact
  using (fixedPointProgram; fixedPointProgramCorrect; fixedPointProgramSizeBound)

open import DASHI.Mathematics.Complexity.PNotEqualsNPPhaseCounterParetoExact
  using
    ( compactCounterSingleDecrementBound
    ; phaseExpandedStateCountExact
    ; phaseExpandedRuleCountExact
    ; canonicalPhaseCounterParetoBoundary
    )

------------------------------------------------------------------------
-- Explicit fail-closed frontier record.
------------------------------------------------------------------------

record BehavioralSpecializerFrontierBoundary : Set where
  constructor behavioral-specializer-frontier-boundary
  field
    selfDelimitingQuotePaid : Bool
    rawInterpreterPaid : Bool
    typedRawToStandardFidelityPaid : Bool
    delimiterScannerCodedPaid : Bool
    unaryEqualityCodedPaid : Bool
    abstractBehavioralFixedPointPaid : Bool
    timingResourceParetoPaid : Bool
    unaryEqualityRunCorrectnessStillRequired : Bool
    literalCodedSpecializerAssemblyStillRequired : Bool
    quotedCodeMustActuallyBeConsumed : Bool
    finalSameObjectResourceFixedPointStillRequired : Bool
    rawCodeEqualityRequired : Bool
    iitPhiIsComplexityLowerBound : Bool

open BehavioralSpecializerFrontierBoundary public

canonicalBehavioralSpecializerFrontierBoundary :
  BehavioralSpecializerFrontierBoundary
canonicalBehavioralSpecializerFrontierBoundary =
  behavioral-specializer-frontier-boundary
    true true true true true true true
    true true true true
    false false
