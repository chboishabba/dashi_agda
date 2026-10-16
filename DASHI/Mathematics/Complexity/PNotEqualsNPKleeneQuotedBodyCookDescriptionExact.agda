module DASHI.Mathematics.Complexity.PNotEqualsNPKleeneQuotedBodyCookDescriptionExact where

------------------------------------------------------------------------
-- SAME-OBJECT COOK DESCRIPTION FOR THE BEHAVIOURAL KLEENE FIXED POINT
--
-- The finite Kleene theorem gives
--
--   run1(q,x) = runPrimitive2(p,q,x).
--
-- Therefore a literal binary realization may execute the fixed body machine p
-- on tape data containing quote(q).  Cook--Levin must describe THAT SAME
-- `(p, quote(q), T)` computation.  No compiled q-machine or raw code equality is
-- required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.Nat using (Nat)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.GuardedCookStreamingBitExact as Stream
import DASHI.Mathematics.Complexity.FiniteSelfSpecializingProgramSelfDelimitingCodeExact as ProgramQuote

bodyConcreteMachine :
  Coded.CodedFiniteStandardTM →
  DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact.ConcreteTapeMachine
bodyConcreteMachine code =
  Presented.finitePresentedStandardToConcrete
    (Coded.decodeCodedStandardTM code)

fixedPointQuoteBits :
  Coded.CodedFiniteStandardTM → List Bool
fixedPointQuoteBits = ProgramQuote.fixedPointQuote

fixedPointQuoteInput :
  (body : Coded.CodedFiniteStandardTM) →
  Fin.Fin (Coded.symbolCount body) →
  Fin.Fin (Coded.symbolCount body) →
  Input.InputWord (bodyConcreteMachine body)
fixedPointQuoteInput body zeroSymbol oneSymbol =
  Query.mapBoolSymbols
    zeroSymbol oneSymbol
    (fixedPointQuoteBits body)

kleeneBodyCookDescription :
  (body : Coded.CodedFiniteStandardTM) →
  Selector.NonemptyRuleTable (bodyConcreteMachine body) →
  Fin.Fin (Coded.symbolCount body) →
  Fin.Fin (Coded.symbolCount body) →
  Nat →
  Description.GuardedCookFormulaDescription
kleeneBodyCookDescription
    body nonemptyRules zeroSymbol oneSymbol steps = record
  { Description.code = body
  ; Description.nonemptyRules = nonemptyRules
  ; Description.input =
      fixedPointQuoteInput body zeroSymbol oneSymbol
  ; Description.steps = steps
  }

kleeneBodyDescriptionCodeExact :
  (body : Coded.CodedFiniteStandardTM)
  (nonemptyRules : Selector.NonemptyRuleTable (bodyConcreteMachine body))
  (zeroSymbol oneSymbol : Fin.Fin (Coded.symbolCount body))
  (steps : Nat) →
  Description.code
    (kleeneBodyCookDescription
      body nonemptyRules zeroSymbol oneSymbol steps)
  ≡ body
kleeneBodyDescriptionCodeExact body nonemptyRules zeroSymbol oneSymbol steps = refl

kleeneBodyDescriptionInputExact :
  (body : Coded.CodedFiniteStandardTM)
  (nonemptyRules : Selector.NonemptyRuleTable (bodyConcreteMachine body))
  (zeroSymbol oneSymbol : Fin.Fin (Coded.symbolCount body))
  (steps : Nat) →
  Description.input
    (kleeneBodyCookDescription
      body nonemptyRules zeroSymbol oneSymbol steps)
  ≡ fixedPointQuoteInput body zeroSymbol oneSymbol
kleeneBodyDescriptionInputExact body nonemptyRules zeroSymbol oneSymbol steps = refl

kleeneBodyQuoteParsesExact :
  (body : Coded.CodedFiniteStandardTM) →
  ProgramQuote.decodeProgramFuel
    ProgramQuote.five
    (fixedPointQuoteBits body)
  ≡
  just
    (ProgramQuote.fixedPointRawView body , [])
kleeneBodyQuoteParsesExact = ProgramQuote.fixedPointQuoteParsesExact
  where
    open import Agda.Builtin.List using ([])
    open import Agda.Builtin.Maybe using (just)

kleeneBodyStreamedBit :
  (body : Coded.CodedFiniteStandardTM)
  (nonemptyRules : Selector.NonemptyRuleTable (bodyConcreteMachine body))
  (zeroSymbol oneSymbol : Fin.Fin (Coded.symbolCount body))
  (steps index : Nat) →
  Maybe Bool
kleeneBodyStreamedBit body nonemptyRules zeroSymbol oneSymbol steps index =
  Stream.streamedQueryBit
    (Description.atIndex
      (kleeneBodyCookDescription
        body nonemptyRules zeroSymbol oneSymbol steps)
      index)

kleeneBodyStreamedBitExact :
  (body : Coded.CodedFiniteStandardTM)
  (nonemptyRules : Selector.NonemptyRuleTable (bodyConcreteMachine body))
  (zeroSymbol oneSymbol : Fin.Fin (Coded.symbolCount body))
  (steps index : Nat) →
  kleeneBodyStreamedBit
    body nonemptyRules zeroSymbol oneSymbol steps index
  ≡
  Semantics.queryAnswer
    (Description.atIndex
      (kleeneBodyCookDescription
        body nonemptyRules zeroSymbol oneSymbol steps)
      index)
kleeneBodyStreamedBitExact body nonemptyRules zeroSymbol oneSymbol steps index =
  Stream.streamedQueryBitExact
    (Description.atIndex
      (kleeneBodyCookDescription
        body nonemptyRules zeroSymbol oneSymbol steps)
      index)

------------------------------------------------------------------------
-- MAX-CUT CONSEQUENCE
--
-- The correct behavioural self-object is now explicit: body machine p on the
-- literal self-delimiting quote of q(p).  The quote parser recovers the entire
-- five-node fixed-point syntax, including p, while Cook streaming describes the
-- same body p and same quote input.  Remaining work is to realize the binary body
-- machine that performs this parsing/streaming, simulates the SAT candidate over
-- the virtual Cook input, and negates its result within a closing resource T.
------------------------------------------------------------------------
