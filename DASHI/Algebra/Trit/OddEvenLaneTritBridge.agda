module DASHI.Algebra.Trit.OddEvenLaneTritBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Algebra.Trit as T
import DASHI.Core.ParityLaneOperatorCore as P

------------------------------------------------------------------------
-- Odd/even lane to trit bridge.
--
-- This module is a candidate-only bridge from the parity-lane vocabulary
-- into the local Trit carrier.  It keeps the routing surface explicit:
-- odd lanes collapse to the residual lane, even lanes separate the operator
-- lane, and unresolved lanes stay neutral at the boundary.

data OddEvenLaneClass : Set where
  oddLane :
    OddEvenLaneClass

  evenLane :
    OddEvenLaneClass

  unresolvedLane :
    OddEvenLaneClass

data TritRoutingCode : Set where
  collapsedResidualLane :
    TritRoutingCode

  separatedOperatorLane :
    TritRoutingCode

  neutralBoundaryLane :
    TritRoutingCode

oddEvenLaneClassLabel : OddEvenLaneClass → String
oddEvenLaneClassLabel oddLane =
  "odd"
oddEvenLaneClassLabel evenLane =
  "even"
oddEvenLaneClassLabel unresolvedLane =
  "unresolved"

tritRoutingCodeLabel : TritRoutingCode → String
tritRoutingCodeLabel collapsedResidualLane =
  "collapsed-residual"
tritRoutingCodeLabel separatedOperatorLane =
  "separated-operator"
tritRoutingCodeLabel neutralBoundaryLane =
  "neutral-boundary"

candidateOnlyBitFromLaneClass : OddEvenLaneClass → Bool
candidateOnlyBitFromLaneClass _ =
  true

authorityFalseBitFromLaneClass : OddEvenLaneClass → Bool
authorityFalseBitFromLaneClass _ =
  false

laneClassToTrit : OddEvenLaneClass → T.Trit
laneClassToTrit oddLane =
  T.neg
laneClassToTrit evenLane =
  T.pos
laneClassToTrit unresolvedLane =
  T.zer

laneClassToRoutingCode : OddEvenLaneClass → TritRoutingCode
laneClassToRoutingCode oddLane =
  collapsedResidualLane
laneClassToRoutingCode evenLane =
  separatedOperatorLane
laneClassToRoutingCode unresolvedLane =
  neutralBoundaryLane

laneClassFromTrit : T.Trit → OddEvenLaneClass
laneClassFromTrit T.neg =
  oddLane
laneClassFromTrit T.zer =
  unresolvedLane
laneClassFromTrit T.pos =
  evenLane

laneClassFromRoutingCode : TritRoutingCode → OddEvenLaneClass
laneClassFromRoutingCode collapsedResidualLane =
  oddLane
laneClassFromRoutingCode separatedOperatorLane =
  evenLane
laneClassFromRoutingCode neutralBoundaryLane =
  unresolvedLane

record OddEvenLaneTritReceipt : Set where
  constructor mkOddEvenLaneTritReceipt
  field
    laneClass :
      OddEvenLaneClass

    laneClassTag :
      String

    laneTrit :
      T.Trit

    laneRoutingCode :
      TritRoutingCode

    routingCodeTag :
      String

    candidateOnlyBit :
      Bool

    authorityFalseBit :
      Bool

open OddEvenLaneTritReceipt public

record OddEvenLaneTritReceiptWitness
  (receipt : OddEvenLaneTritReceipt) :
  Set where
  constructor mkOddEvenLaneTritReceiptWitness
  field
    candidateOnlyBitIsTrue :
      candidateOnlyBit receipt ≡ true

    authorityFalseBitIsFalse :
      authorityFalseBit receipt ≡ false

    tritMatchesClass :
      laneTrit receipt ≡ laneClassToTrit (laneClass receipt)

    routingCodeMatchesClass :
      laneRoutingCode receipt ≡ laneClassToRoutingCode (laneClass receipt)

    classTagMatches :
      laneClassTag receipt ≡ oddEvenLaneClassLabel (laneClass receipt)

    routingTagMatches :
      routingCodeTag receipt ≡ tritRoutingCodeLabel (laneRoutingCode receipt)

open OddEvenLaneTritReceiptWitness public

oddLaneTritReceipt : OddEvenLaneTritReceipt
oddLaneTritReceipt =
  mkOddEvenLaneTritReceipt
    oddLane
    "odd"
    T.neg
    collapsedResidualLane
    "collapsed-residual"
    true
    false

evenLaneTritReceipt : OddEvenLaneTritReceipt
evenLaneTritReceipt =
  mkOddEvenLaneTritReceipt
    evenLane
    "even"
    T.pos
    separatedOperatorLane
    "separated-operator"
    true
    false

unresolvedLaneTritReceipt : OddEvenLaneTritReceipt
unresolvedLaneTritReceipt =
  mkOddEvenLaneTritReceipt
    unresolvedLane
    "unresolved"
    T.zer
    neutralBoundaryLane
    "neutral-boundary"
    true
    false

oddLaneTritReceiptWitness : OddEvenLaneTritReceiptWitness oddLaneTritReceipt
oddLaneTritReceiptWitness =
  mkOddEvenLaneTritReceiptWitness refl refl refl refl refl refl

evenLaneTritReceiptWitness :
  OddEvenLaneTritReceiptWitness evenLaneTritReceipt
evenLaneTritReceiptWitness =
  mkOddEvenLaneTritReceiptWitness refl refl refl refl refl refl

unresolvedLaneTritReceiptWitness :
  OddEvenLaneTritReceiptWitness unresolvedLaneTritReceipt
unresolvedLaneTritReceiptWitness =
  mkOddEvenLaneTritReceiptWitness refl refl refl refl refl refl

canonicalOddEvenLaneTritReceipts :
  List OddEvenLaneTritReceipt
canonicalOddEvenLaneTritReceipts =
  oddLaneTritReceipt
  ∷ evenLaneTritReceipt
  ∷ unresolvedLaneTritReceipt
  ∷ []

------------------------------------------------------------------------
-- Class-level lemmas.

oddClassifiesAsCollapsedResidualLane :
  laneClassToRoutingCode oddLane ≡ collapsedResidualLane
oddClassifiesAsCollapsedResidualLane =
  refl

evenClassifiesAsSeparatedOperatorLane :
  laneClassToRoutingCode evenLane ≡ separatedOperatorLane
evenClassifiesAsSeparatedOperatorLane =
  refl

unresolvedClassifiesAsNeutralBoundary :
  laneClassToRoutingCode unresolvedLane ≡ neutralBoundaryLane
unresolvedClassifiesAsNeutralBoundary =
  refl

oddClassifiesAsNegTrit :
  laneClassToTrit oddLane ≡ T.neg
oddClassifiesAsNegTrit =
  refl

evenClassifiesAsPosTrit :
  laneClassToTrit evenLane ≡ T.pos
evenClassifiesAsPosTrit =
  refl

unresolvedClassifiesAsZeroTrit :
  laneClassToTrit unresolvedLane ≡ T.zer
unresolvedClassifiesAsZeroTrit =
  refl

oddLaneCandidateOnlyBitIsTrue :
  candidateOnlyBit oddLaneTritReceipt ≡ true
oddLaneCandidateOnlyBitIsTrue =
  refl

evenLaneCandidateOnlyBitIsTrue :
  candidateOnlyBit evenLaneTritReceipt ≡ true
evenLaneCandidateOnlyBitIsTrue =
  refl

unresolvedLaneCandidateOnlyBitIsTrue :
  candidateOnlyBit unresolvedLaneTritReceipt ≡ true
unresolvedLaneCandidateOnlyBitIsTrue =
  refl

oddLaneAuthorityFalseBitIsFalse :
  authorityFalseBit oddLaneTritReceipt ≡ false
oddLaneAuthorityFalseBitIsFalse =
  refl

evenLaneAuthorityFalseBitIsFalse :
  authorityFalseBit evenLaneTritReceipt ≡ false
evenLaneAuthorityFalseBitIsFalse =
  refl

unresolvedLaneAuthorityFalseBitIsFalse :
  authorityFalseBit unresolvedLaneTritReceipt ≡ false
unresolvedLaneAuthorityFalseBitIsFalse =
  refl

oddLaneIsCollapsedResidualAtStringSurface :
  laneClassTag oddLaneTritReceipt ≡ "odd"
oddLaneIsCollapsedResidualAtStringSurface =
  refl

evenLaneIsSeparatedOperatorAtStringSurface :
  laneClassTag evenLaneTritReceipt ≡ "even"
evenLaneIsSeparatedOperatorAtStringSurface =
  refl

unresolvedLaneIsNeutralBoundaryAtStringSurface :
  laneClassTag unresolvedLaneTritReceipt ≡ "unresolved"
unresolvedLaneIsNeutralBoundaryAtStringSurface =
  refl

------------------------------------------------------------------------
-- Canonical round-trip helpers.

laneClassToTritRoundTrip :
  ∀ lane →
  laneClassFromTrit (laneClassToTrit lane) ≡ lane
laneClassToTritRoundTrip oddLane =
  refl
laneClassToTritRoundTrip evenLane =
  refl
laneClassToTritRoundTrip unresolvedLane =
  refl

laneClassToRoutingRoundTrip :
  ∀ lane →
  laneClassFromRoutingCode (laneClassToRoutingCode lane) ≡ lane
laneClassToRoutingRoundTrip oddLane =
  refl
laneClassToRoutingRoundTrip evenLane =
  refl
laneClassToRoutingRoundTrip unresolvedLane =
  refl

------------------------------------------------------------------------
-- Bridge receipts for the class-to-trit projection.

classToTritReceipt :
  (lane : OddEvenLaneClass) →
  OddEvenLaneTritReceipt
classToTritReceipt lane =
  mkOddEvenLaneTritReceipt
    lane
    (oddEvenLaneClassLabel lane)
    (laneClassToTrit lane)
    (laneClassToRoutingCode lane)
    (tritRoutingCodeLabel (laneClassToRoutingCode lane))
    (candidateOnlyBitFromLaneClass lane)
    (authorityFalseBitFromLaneClass lane)

classToTritReceiptCandidateOnly :
  ∀ lane →
  candidateOnlyBit (classToTritReceipt lane) ≡ true
classToTritReceiptCandidateOnly lane =
  refl

classToTritReceiptAuthorityFalse :
  ∀ lane →
  authorityFalseBit (classToTritReceipt lane) ≡ false
classToTritReceiptAuthorityFalse lane =
  refl

classToTritReceiptWitness :
  ∀ lane →
  OddEvenLaneTritReceiptWitness (classToTritReceipt lane)
classToTritReceiptWitness oddLane =
  mkOddEvenLaneTritReceiptWitness refl refl refl refl refl refl
classToTritReceiptWitness evenLane =
  mkOddEvenLaneTritReceiptWitness refl refl refl refl refl refl
classToTritReceiptWitness unresolvedLane =
  mkOddEvenLaneTritReceiptWitness refl refl refl refl refl refl

------------------------------------------------------------------------
-- Expected-core compatibility surface.
--
-- The import of DASHI.Core.ParityLaneOperatorCore is kept here so the bridge
-- can be wired to the shared parity-lane vocabulary when that core is present.
-- This local bridge remains self-describing even if the core is not yet used
-- directly by downstream callers.

expectedParityLaneOperatorCoreImport : String
expectedParityLaneOperatorCoreImport =
  "DASHI.Core.ParityLaneOperatorCore"
