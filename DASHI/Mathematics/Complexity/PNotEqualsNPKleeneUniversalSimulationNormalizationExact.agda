module DASHI.Mathematics.Complexity.PNotEqualsNPKleeneUniversalSimulationNormalizationExact where

------------------------------------------------------------------------
-- QUOTED BODY RUN -> FIXED UNIVERSAL RAW-SIMULATION INSTANCE
--
-- For one coded body p and whole fixed-point quote q(p), the ordinary typed
-- execution of p on q(p) is reproduced step-for-step by the self-delimiting raw
-- interpreter on code(p).  This is the semantic normalization needed before
-- replacing p-dependent Cook construction by Cook of one fixed universal TM.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Maybe using (just)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardSelfDelimitingCodeExact as MachineCode
import DASHI.Mathematics.Complexity.CodedFiniteStandardRawInterpreterExact as Raw
import DASHI.Mathematics.Complexity.CodedFiniteStandardRawInterpreterFidelityExact as Fidelity
import DASHI.Mathematics.Complexity.CodedStandardCanonicalInputExact as CanonicalInput
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.PNotEqualsNPKleeneQuotedBodyCookDescriptionExact as Quoted

quotedBodyStandardStart :
  (body : Coded.CodedFiniteStandardTM) →
  Fin.Fin (Coded.symbolCount body) →
  Fin.Fin (Coded.symbolCount body) →
  DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact.StandardConfiguration
    (Fidelity.codedStandard body)
quotedBodyStandardStart body zeroSymbol oneSymbol =
  CanonicalInput.canonicalStandardStart
    (Quoted.fixedPointQuoteInput body zeroSymbol oneSymbol)

quotedBodyRawStart :
  (body : Coded.CodedFiniteStandardTM) →
  Fin.Fin (Coded.symbolCount body) →
  Fin.Fin (Coded.symbolCount body) →
  Raw.RawConfiguration
quotedBodyRawStart body zeroSymbol oneSymbol =
  Fidelity.rawConfigurationOf
    (quotedBodyStandardStart body zeroSymbol oneSymbol)

universalSemanticInstanceExact :
  (body : Coded.CodedFiniteStandardTM)
  (zeroSymbol oneSymbol : Fin.Fin (Coded.symbolCount body))
  ∀ {steps : Nat}
    {finish :
      DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact.StandardConfiguration
        (Fidelity.codedStandard body)} →
  Run.StandardExactRun
    (Fidelity.codedStandard body)
    steps
    (quotedBodyStandardStart body zeroSymbol oneSymbol)
    finish →
  Raw.runSelfDelimitedCode
    steps
    (MachineCode.selfDelimitingMachineCode body)
    (quotedBodyRawStart body zeroSymbol oneSymbol)
  ≡ just (Fidelity.rawConfigurationOf finish)
universalSemanticInstanceExact body zeroSymbol oneSymbol run =
  Fidelity.selfDelimitedInterpreterFollowsStandardRun body run

------------------------------------------------------------------------
-- MAX-CUT CONSEQUENCE
--
-- The same T-step p-on-quote(q) computation can be normalized to a fixed raw
-- interpreter semantics whose varying data are only self-delimiting code(p) and
-- the quoted input tape.  A literal standard-TM implementation U of this one
-- interpreter would let Cook--Levin describe U(code(p),quote(q),T), eliminating
-- p-dependent Cook transition tables while preserving acceptance step-for-step.
------------------------------------------------------------------------
