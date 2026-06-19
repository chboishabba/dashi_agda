module DASHI.Core.ParityLaneOperatorCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.OddGrassmannLaneCore as Odd
import DASHI.Core.EvenLaneOperatorCore as Even

------------------------------------------------------------------------
-- Parity lane bridge.
--
-- This module centralizes the odd / even / unresolved parity split.  Odd
-- lanes collapse to a single collapsed regime, even lanes separate probe and
-- measure by receipt, and unresolved lanes stay candidate-only with no local
-- authority.

data LaneClass : Set where
  oddCollapsedLane :
    LaneClass

  evenSeparatedLane :
    LaneClass

  unresolvedLane :
    LaneClass

data OperatorRegime : Set where
  collapsedRegime :
    OperatorRegime

  separatedRegime :
    OperatorRegime

  candidateOnlyRegime :
    OperatorRegime

laneClassLabel :
  LaneClass →
  String
laneClassLabel oddCollapsedLane =
  "odd-collapsed lane"
laneClassLabel evenSeparatedLane =
  "even-separated lane"
laneClassLabel unresolvedLane =
  "unresolved lane"

operatorRegime :
  LaneClass →
  OperatorRegime
operatorRegime oddCollapsedLane =
  collapsedRegime
operatorRegime evenSeparatedLane =
  separatedRegime
operatorRegime unresolvedLane =
  candidateOnlyRegime

record ParityLaneReceipt : Set where
  constructor mkParityLaneReceipt
  field
    receiptLabel :
      String

    receiptClass :
      LaneClass

    receiptRegime :
      OperatorRegime

    probeReceipt :
      String

    measureReceipt :
      String

    candidateOnly :
      Bool

    authority :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    authorityIsFalse :
      authority ≡ false

open ParityLaneReceipt public

authorityFlag :
  ParityLaneReceipt →
  Bool
authorityFlag =
  authority

------------------------------------------------------------------------
-- Canonical receipts.

canonicalOddParityLaneReceipt :
  ParityLaneReceipt
canonicalOddParityLaneReceipt =
  mkParityLaneReceipt
    "odd-collapsed lane"
    oddCollapsedLane
    collapsedRegime
    "probe-measure collapse by receipt"
    "probe-measure collapse by receipt"
    true
    false
    refl
    refl

canonicalEvenParityLaneReceipt :
  ParityLaneReceipt
canonicalEvenParityLaneReceipt =
  mkParityLaneReceipt
    "even-separated lane"
    evenSeparatedLane
    separatedRegime
    "probe-measure separation by receipt"
    "probe-measure separation by receipt"
    true
    false
    refl
    refl

canonicalUnresolvedParityLaneReceipt :
  ParityLaneReceipt
canonicalUnresolvedParityLaneReceipt =
  mkParityLaneReceipt
    "unresolved lane"
    unresolvedLane
    candidateOnlyRegime
    "candidate-only probe receipt"
    "candidate-only probe receipt"
    true
    false
    refl
    refl

------------------------------------------------------------------------
-- Receipt projections.

canonicalOddReceiptLabelIsCanonical :
  receiptLabel canonicalOddParityLaneReceipt
  ≡
  "odd-collapsed lane"
canonicalOddReceiptLabelIsCanonical =
  refl

canonicalOddReceiptClassIsCollapsed :
  receiptClass canonicalOddParityLaneReceipt
  ≡
  oddCollapsedLane
canonicalOddReceiptClassIsCollapsed =
  refl

canonicalOddReceiptRegimeIsCollapsed :
  receiptRegime canonicalOddParityLaneReceipt
  ≡
  collapsedRegime
canonicalOddReceiptRegimeIsCollapsed =
  refl

canonicalOddProbeReceiptCollapses :
  probeReceipt canonicalOddParityLaneReceipt
  ≡
  "probe-measure collapse by receipt"
canonicalOddProbeReceiptCollapses =
  refl

canonicalOddMeasureReceiptCollapses :
  measureReceipt canonicalOddParityLaneReceipt
  ≡
  "probe-measure collapse by receipt"
canonicalOddMeasureReceiptCollapses =
  refl

canonicalOddCandidateOnlyIsTrue :
  candidateOnly canonicalOddParityLaneReceipt
  ≡
  true
canonicalOddCandidateOnlyIsTrue =
  refl

canonicalOddAuthorityIsFalse :
  authority canonicalOddParityLaneReceipt
  ≡
  false
canonicalOddAuthorityIsFalse =
  refl

oddMapsToCollapsed :
  receiptClass canonicalOddParityLaneReceipt
  ≡
  oddCollapsedLane
oddMapsToCollapsed =
  canonicalOddReceiptClassIsCollapsed

oddMapsToProbeMeasureCollapse :
  probeReceipt canonicalOddParityLaneReceipt
  ≡
  measureReceipt canonicalOddParityLaneReceipt
oddMapsToProbeMeasureCollapse =
  refl

canonicalEvenReceiptLabelIsCanonical :
  receiptLabel canonicalEvenParityLaneReceipt
  ≡
  "even-separated lane"
canonicalEvenReceiptLabelIsCanonical =
  refl

canonicalEvenReceiptClassIsSeparated :
  receiptClass canonicalEvenParityLaneReceipt
  ≡
  evenSeparatedLane
canonicalEvenReceiptClassIsSeparated =
  refl

canonicalEvenReceiptRegimeIsSeparated :
  receiptRegime canonicalEvenParityLaneReceipt
  ≡
  separatedRegime
canonicalEvenReceiptRegimeIsSeparated =
  refl

canonicalEvenProbeReceiptSeparates :
  probeReceipt canonicalEvenParityLaneReceipt
  ≡
  "probe-measure separation by receipt"
canonicalEvenProbeReceiptSeparates =
  refl

canonicalEvenMeasureReceiptSeparates :
  measureReceipt canonicalEvenParityLaneReceipt
  ≡
  "probe-measure separation by receipt"
canonicalEvenMeasureReceiptSeparates =
  refl

canonicalEvenCandidateOnlyIsTrue :
  candidateOnly canonicalEvenParityLaneReceipt
  ≡
  true
canonicalEvenCandidateOnlyIsTrue =
  refl

canonicalEvenAuthorityIsFalse :
  authority canonicalEvenParityLaneReceipt
  ≡
  false
canonicalEvenAuthorityIsFalse =
  refl

evenMapsToSeparated :
  receiptClass canonicalEvenParityLaneReceipt
  ≡
  evenSeparatedLane
evenMapsToSeparated =
  canonicalEvenReceiptClassIsSeparated

evenMapsToProbeMeasureSeparation :
  probeReceipt canonicalEvenParityLaneReceipt
  ≡
  measureReceipt canonicalEvenParityLaneReceipt
evenMapsToProbeMeasureSeparation =
  refl

canonicalUnresolvedReceiptLabelIsCanonical :
  receiptLabel canonicalUnresolvedParityLaneReceipt
  ≡
  "unresolved lane"
canonicalUnresolvedReceiptLabelIsCanonical =
  refl

canonicalUnresolvedReceiptClassIsUnresolved :
  receiptClass canonicalUnresolvedParityLaneReceipt
  ≡
  unresolvedLane
canonicalUnresolvedReceiptClassIsUnresolved =
  refl

canonicalUnresolvedReceiptRegimeIsCandidateOnly :
  receiptRegime canonicalUnresolvedParityLaneReceipt
  ≡
  candidateOnlyRegime
canonicalUnresolvedReceiptRegimeIsCandidateOnly =
  refl

canonicalUnresolvedCandidateOnlyIsTrue :
  candidateOnly canonicalUnresolvedParityLaneReceipt
  ≡
  true
canonicalUnresolvedCandidateOnlyIsTrue =
  refl

canonicalUnresolvedAuthorityIsFalse :
  authority canonicalUnresolvedParityLaneReceipt
  ≡
  false
canonicalUnresolvedAuthorityIsFalse =
  refl

unresolvedStaysCandidateOnly :
  candidateOnly canonicalUnresolvedParityLaneReceipt
  ≡
  true
unresolvedStaysCandidateOnly =
  canonicalUnresolvedCandidateOnlyIsTrue

unresolvedHasNoAuthority :
  authority canonicalUnresolvedParityLaneReceipt
  ≡
  false
unresolvedHasNoAuthority =
  canonicalUnresolvedAuthorityIsFalse
