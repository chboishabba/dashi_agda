module DASHI.Mathematics.Complexity.CodedFiniteStandardStaticQuoteLookupExact where

------------------------------------------------------------------------
-- ACTUAL CODED MACHINE QUOTATION -> LITERAL UNARY-INDEX LOOKUP TM
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (just)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardStaticQuotationExact as Quote
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.CodedFiniteBitStreamLookupExact as Lookup
import DASHI.Mathematics.Complexity.CodedFiniteBitStreamLookupTransitionExact as Transition
import DASHI.Mathematics.Complexity.CodedFiniteStandardExactPhaseLiftExact as Phase
import DASHI.Mathematics.Complexity.CodedFiniteUnaryCursorExact as Cursor
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

staticQuoteBit :
  (code : Coded.CodedFiniteStandardTM) →
  Fin.Fin (Quote.codedStaticProgramWidth code) →
  Bool
staticQuoteBit code =
  CNF.lookupBit (Quote.codedStaticProgramBits code)

staticQuoteLookupCode :
  Coded.CodedFiniteStandardTM →
  Coded.CodedFiniteStandardTM
staticQuoteLookupCode code =
  Lookup.lookupCode
    (Quote.codedStaticProgramWidth code)
    (staticQuoteBit code)

staticQuoteStopTransitionExact :
  (code : Coded.CodedFiniteStandardTM)
  (index : Fin.Fin (Quote.codedStaticProgramWidth code)) →
  Standard.transition
    (Presented.finitePresentedStandardMachine
      (Coded.decodeCodedStandardTM (staticQuoteLookupCode code)))
    (Lookup.cursorInBase
      (Quote.codedStaticProgramWidth code)
      (Phase.raisePhase index))
    Cursor.stopSymbol
  ≡
  just
    (Standard.standard-transition
      (Lookup.bitSink
        (Quote.codedStaticProgramWidth code)
        (staticQuoteBit code index))
      Cursor.stopSymbol
      Local.stayPut)
staticQuoteStopTransitionExact code index =
  Transition.validStopTransition
    (staticQuoteBit code)
    index

staticQuoteTrueIsAccepting :
  (code : Coded.CodedFiniteStandardTM) →
  Lookup.trueSink (Quote.codedStaticProgramWidth code)
  ≡
  Coded.acceptingState (staticQuoteLookupCode code)
staticQuoteTrueIsAccepting code =
  Transition.trueSinkIsAccepting
    (Quote.codedStaticProgramWidth code)
    (staticQuoteBit code)

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The surviving behavioural route now has literal finite syntax for random
-- access to the quoted primitive machine's actual static program bits. Runtime
-- performs no Agda-level code lookup. This does not bake the full own-Cook
-- stream and therefore does not invoke the table-baked self-code no-go.
------------------------------------------------------------------------
