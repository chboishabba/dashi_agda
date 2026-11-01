module DASHI.Mathematics.Complexity.ConcreteTapeWindowCodecCNFWeldExact where

------------------------------------------------------------------------
-- GENERIC FIXED-WIDTH WINDOW CODEC -> CANONICAL TRUTH-TABLE CNF
--
-- This is deliberately not a rival Cell/Bits encoding.  It consumes any
-- supplied fixed-width codec whose decode-after-encode law is proved, then
-- composes:
--
--   semantic legal window
--     <-> reflected Boolean local predicate
--     <-> canonical truth-table CNF satisfaction.
--
-- The user's separate canonical Cell/Bits commits can therefore instantiate
-- this theorem directly once they are present on the remote branch.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapeLegalWindowReflectionExact as Reflect
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

record FixedWidthWindowCodec
    (machine : Local.ConcreteTapeMachine)
    (width : Nat) : Set₁ where
  field
    encode :
      Local.SixCellWindow machine →
      CNF.Bits width

    decode :
      CNF.Bits width →
      Local.SixCellWindow machine

    decodeEncode :
      (window : Local.SixCellWindow machine) →
      decode (encode window) ≡ window

open FixedWidthWindowCodec public

encodedWindowPredicate :
  ∀ {machine width} →
  FixedWidthWindowCodec machine width →
  Local.TapeRule
    (Local.State machine)
    (Local.Symbol machine) →
  CNF.Bits width →
  Bool
encodedWindowPredicate {machine} codec rule bits =
  Reflect.reflectedLegalWindowBool
    machine rule (decode codec bits)

encodedWindowCNF :
  ∀ {machine width} →
  FixedWidthWindowCodec machine width →
  Local.TapeRule
    (Local.State machine)
    (Local.Symbol machine) →
  CNF.CNF width
encodedWindowCNF codec rule =
  CNF.truthTableCNF
    (encodedWindowPredicate codec rule)

semanticLegalImpliesEncodedCNF :
  ∀ {machine width rule window}
    (codec : FixedWidthWindowCodec machine width) →
  Pattern.LegalWindowForRule machine rule window →
  CNF.evaluateCNF
    (encodedWindowCNF codec rule)
    (encode codec window)
  ≡ true
semanticLegalImpliesEncodedCNF
    {rule = rule} {window = window}
    codec legal
    with decodeEncode codec window
... | refl =
  CNF.truthTableCNFComplete
    (encodedWindowPredicate codec rule)
    (encode codec window)
    (Reflect.semanticLegalImpliesReflectedBooleanTrue legal)

encodedCNFImpliesSemanticLegal :
  ∀ {machine width rule window}
    (codec : FixedWidthWindowCodec machine width) →
  CNF.evaluateCNF
    (encodedWindowCNF codec rule)
    (encode codec window)
  ≡ true →
  Pattern.LegalWindowForRule machine rule window
encodedCNFImpliesSemanticLegal
    {rule = rule} {window = window}
    codec cnfTrue
    with decodeEncode codec window
... | refl =
  Reflect.booleanTrueImpliesSemanticLegal
    (CNF.truthTableCNFSound
      (encodedWindowPredicate codec rule)
      (encode codec window)
      cnfTrue)

record EncodedWindowCNFSemanticEquivalence
    {machine : Local.ConcreteTapeMachine}
    {width : Nat}
    (codec : FixedWidthWindowCodec machine width)
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (window : Local.SixCellWindow machine) : Set where
  field
    semanticToCNF :
      Pattern.LegalWindowForRule machine rule window →
      CNF.evaluateCNF
        (encodedWindowCNF codec rule)
        (encode codec window)
      ≡ true

    cnfToSemantic :
      CNF.evaluateCNF
        (encodedWindowCNF codec rule)
        (encode codec window)
      ≡ true →
      Pattern.LegalWindowForRule machine rule window

canonicalEncodedWindowCNFSemanticEquivalence :
  ∀ {machine width}
    (codec : FixedWidthWindowCodec machine width)
    (rule : Local.TapeRule
      (Local.State machine)
      (Local.Symbol machine))
    (window : Local.SixCellWindow machine) →
  EncodedWindowCNFSemanticEquivalence codec rule window
canonicalEncodedWindowCNFSemanticEquivalence codec rule window = record
  { semanticToCNF =
      semanticLegalImpliesEncodedCNF codec
  ; cnfToSemantic =
      encodedCNFImpliesSemanticLegal codec
  }

record ConcreteTapeWindowCodecCNFWeldBoundary : Set where
  constructor concrete-tape-window-codec-cnf-weld-boundary
  field
    reflectedBooleanPredicateReused : Bool
    truthTableCNFCompilerReused : Bool
    genericFixedWidthCodecSurfacePaid : Bool
    codecCNFSemanticEquivalencePaid : Bool
    canonicalConcreteWindowCodecPaid : Bool
    canonicalPlacedCNFWeldPaid : Bool
    runToSATPaid : Bool
    satToRunPaid : Bool
    genericCookLevinPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeWindowCodecCNFWeldBoundary :
  ConcreteTapeWindowCodecCNFWeldBoundary
canonicalConcreteTapeWindowCodecCNFWeldBoundary =
  concrete-tape-window-codec-cnf-weld-boundary
    true true true true false false false false false false
