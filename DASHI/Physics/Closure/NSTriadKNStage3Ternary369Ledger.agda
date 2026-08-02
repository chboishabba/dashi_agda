module DASHI.Physics.Closure.NSTriadKNStage3Ternary369Ledger where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Balanced/unbalanced ternary and 3-6-9 receipts for the Stage-3
-- shell and adjoint frontier".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a repository-original typed status layer.
-- Uses: DASHI.Algebra.Trit for signed analytic disposition, Base369.TriTruth
-- for role-specific unbalanced maturity, and Base369 HexTruth/NonaryTruth as
-- finite codes for six- and nine-state Stage-3 receipts.
-- Relationship: the encodings below are explicit set-level round trips.  They
-- do not identify the global cyclic C6 or C9 operations with product
-- operations, preserving the existing Base12369 role boundary.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Algebra.Trit as Balanced
import Base369 as Base
import DASHI.Physics.Closure.NSTriadKNThreeNumericShellLedgerStatus as Rows
import DASHI.Physics.Closure.NSTriadKNComplex3RelocationInstantiation as Relocation
import DASHI.Physics.Closure.NSTriadKNSymmetrisedFirstAdjointNullAudit as NullAudit
import DASHI.Physics.Closure.NSTriadKNFirstAdjointSobolevTailLedger as Tail

------------------------------------------------------------------------
-- Role-specific ternary axes.
--
-- Balanced.Trit:
--   neg = adverse/obstructed
--   zer = neutral, finite-overlap, or unresolved
--   pos = favourable strict decay/cancellation
--
-- Base.TriTruth, used here as an ordered maturity role:
--   tri-low  = missing/uninstantiated
--   tri-mid  = represented or exactly audited
--   tri-high = theorem- and transport-closed
------------------------------------------------------------------------

maturityRank : Base.TriTruth → Nat
maturityRank Base.tri-low = 0
maturityRank Base.tri-mid = 1
maturityRank Base.tri-high = 2

record Stage3SixCoordinate : Set where
  constructor six-coordinate
  field
    analyticDisposition : Balanced.Trit
    theoremClosed : Bool

open Stage3SixCoordinate public

encodeSix : Stage3SixCoordinate → Base.HexTruth
encodeSix (six-coordinate Balanced.neg false) = Base.hex-0
encodeSix (six-coordinate Balanced.neg true) = Base.hex-1
encodeSix (six-coordinate Balanced.zer false) = Base.hex-2
encodeSix (six-coordinate Balanced.zer true) = Base.hex-3
encodeSix (six-coordinate Balanced.pos false) = Base.hex-4
encodeSix (six-coordinate Balanced.pos true) = Base.hex-5

decodeSix : Base.HexTruth → Stage3SixCoordinate
decodeSix Base.hex-0 = six-coordinate Balanced.neg false
decodeSix Base.hex-1 = six-coordinate Balanced.neg true
decodeSix Base.hex-2 = six-coordinate Balanced.zer false
decodeSix Base.hex-3 = six-coordinate Balanced.zer true
decodeSix Base.hex-4 = six-coordinate Balanced.pos false
decodeSix Base.hex-5 = six-coordinate Balanced.pos true

sixDecodeEncode : (x : Stage3SixCoordinate) → decodeSix (encodeSix x) ≡ x
sixDecodeEncode (six-coordinate Balanced.neg false) = refl
sixDecodeEncode (six-coordinate Balanced.neg true) = refl
sixDecodeEncode (six-coordinate Balanced.zer false) = refl
sixDecodeEncode (six-coordinate Balanced.zer true) = refl
sixDecodeEncode (six-coordinate Balanced.pos false) = refl
sixDecodeEncode (six-coordinate Balanced.pos true) = refl

sixEncodeDecode : (x : Base.HexTruth) → encodeSix (decodeSix x) ≡ x
sixEncodeDecode Base.hex-0 = refl
sixEncodeDecode Base.hex-1 = refl
sixEncodeDecode Base.hex-2 = refl
sixEncodeDecode Base.hex-3 = refl
sixEncodeDecode Base.hex-4 = refl
sixEncodeDecode Base.hex-5 = refl

record Stage3NonaryCoordinate : Set where
  constructor nonary-coordinate
  field
    rowDisposition : Balanced.Trit
    proofMaturity : Base.TriTruth

open Stage3NonaryCoordinate public

encodeNonary : Stage3NonaryCoordinate → Base.NonaryTruth
encodeNonary (nonary-coordinate Balanced.neg Base.tri-low) = Base.non-0
encodeNonary (nonary-coordinate Balanced.neg Base.tri-mid) = Base.non-1
encodeNonary (nonary-coordinate Balanced.neg Base.tri-high) = Base.non-2
encodeNonary (nonary-coordinate Balanced.zer Base.tri-low) = Base.non-3
encodeNonary (nonary-coordinate Balanced.zer Base.tri-mid) = Base.non-4
encodeNonary (nonary-coordinate Balanced.zer Base.tri-high) = Base.non-5
encodeNonary (nonary-coordinate Balanced.pos Base.tri-low) = Base.non-6
encodeNonary (nonary-coordinate Balanced.pos Base.tri-mid) = Base.non-7
encodeNonary (nonary-coordinate Balanced.pos Base.tri-high) = Base.non-8

decodeNonary : Base.NonaryTruth → Stage3NonaryCoordinate
decodeNonary Base.non-0 = nonary-coordinate Balanced.neg Base.tri-low
decodeNonary Base.non-1 = nonary-coordinate Balanced.neg Base.tri-mid
decodeNonary Base.non-2 = nonary-coordinate Balanced.neg Base.tri-high
decodeNonary Base.non-3 = nonary-coordinate Balanced.zer Base.tri-low
decodeNonary Base.non-4 = nonary-coordinate Balanced.zer Base.tri-mid
decodeNonary Base.non-5 = nonary-coordinate Balanced.zer Base.tri-high
decodeNonary Base.non-6 = nonary-coordinate Balanced.pos Base.tri-low
decodeNonary Base.non-7 = nonary-coordinate Balanced.pos Base.tri-mid
decodeNonary Base.non-8 = nonary-coordinate Balanced.pos Base.tri-high

nonaryDecodeEncode :
  (x : Stage3NonaryCoordinate) → decodeNonary (encodeNonary x) ≡ x
nonaryDecodeEncode (nonary-coordinate Balanced.neg Base.tri-low) = refl
nonaryDecodeEncode (nonary-coordinate Balanced.neg Base.tri-mid) = refl
nonaryDecodeEncode (nonary-coordinate Balanced.neg Base.tri-high) = refl
nonaryDecodeEncode (nonary-coordinate Balanced.zer Base.tri-low) = refl
nonaryDecodeEncode (nonary-coordinate Balanced.zer Base.tri-mid) = refl
nonaryDecodeEncode (nonary-coordinate Balanced.zer Base.tri-high) = refl
nonaryDecodeEncode (nonary-coordinate Balanced.pos Base.tri-low) = refl
nonaryDecodeEncode (nonary-coordinate Balanced.pos Base.tri-mid) = refl
nonaryDecodeEncode (nonary-coordinate Balanced.pos Base.tri-high) = refl

nonaryEncodeDecode :
  (x : Base.NonaryTruth) → encodeNonary (decodeNonary x) ≡ x
nonaryEncodeDecode Base.non-0 = refl
nonaryEncodeDecode Base.non-1 = refl
nonaryEncodeDecode Base.non-2 = refl
nonaryEncodeDecode Base.non-3 = refl
nonaryEncodeDecode Base.non-4 = refl
nonaryEncodeDecode Base.non-5 = refl
nonaryEncodeDecode Base.non-6 = refl
nonaryEncodeDecode Base.non-7 = refl
nonaryEncodeDecode Base.non-8 = refl

------------------------------------------------------------------------
-- The 24 shell rows receive a signed disposition and a maturity coordinate.
------------------------------------------------------------------------

statusDisposition : Rows.LedgerRowStatus → Balanced.Trit
statusDisposition Rows.numericExponentClosed = Balanced.pos
statusDisposition Rows.finiteOverlapOnly = Balanced.zer
statusDisposition Rows.analyticOpen = Balanced.zer

statusMaturity : Rows.LedgerRowStatus → Base.TriTruth
statusMaturity Rows.numericExponentClosed = Base.tri-mid
statusMaturity Rows.finiteOverlapOnly = Base.tri-mid
statusMaturity Rows.analyticOpen = Base.tri-low

rowNonaryCoordinate : Rows.LedgerLeg → Rows.LedgerClass → Stage3NonaryCoordinate
rowNonaryCoordinate leg class =
  nonary-coordinate
    (statusDisposition (Rows.rowStatus leg class))
    (statusMaturity (Rows.rowStatus leg class))

rowNonaryCode : Rows.LedgerLeg → Rows.LedgerClass → Base.NonaryTruth
rowNonaryCode leg class = encodeNonary (rowNonaryCoordinate leg class)

outputRelocationCoordinate : Stage3NonaryCoordinate
outputRelocationCoordinate = nonary-coordinate Balanced.pos Base.tri-high

firstPrimitiveCoordinate : Stage3NonaryCoordinate
firstPrimitiveCoordinate = nonary-coordinate Balanced.neg Base.tri-mid

firstAssembledTailCoordinate : Stage3NonaryCoordinate
firstAssembledTailCoordinate = nonary-coordinate Balanced.pos Base.tri-mid

secondStructuralCoordinate : Stage3NonaryCoordinate
secondStructuralCoordinate = nonary-coordinate Balanced.pos Base.tri-mid

outputRelocationSix : Stage3SixCoordinate
outputRelocationSix = six-coordinate Balanced.pos true

firstPrimitiveSix : Stage3SixCoordinate
firstPrimitiveSix = six-coordinate Balanced.neg false

firstAssembledTailSix : Stage3SixCoordinate
firstAssembledTailSix = six-coordinate Balanced.pos false

secondStructuralSix : Stage3SixCoordinate
secondStructuralSix = six-coordinate Balanced.pos false

record Stage3Ternary369Receipt : Set where
  constructor receipt
  field
    outputRelocationIsFavourableClosed :
      encodeNonary outputRelocationCoordinate ≡ Base.non-8
    primitiveFirstAdjointIsAdverseAudited :
      encodeNonary firstPrimitiveCoordinate ≡ Base.non-1
    assembledFirstTailIsFavourableAudited :
      encodeNonary firstAssembledTailCoordinate ≡ Base.non-7
    secondAdjointIsFavourableAudited :
      encodeNonary secondStructuralCoordinate ≡ Base.non-7

    outputSixIsFavourableClosed :
      encodeSix outputRelocationSix ≡ Base.hex-5
    firstPrimitiveSixIsAdverseOpen :
      encodeSix firstPrimitiveSix ≡ Base.hex-0
    firstTailSixIsFavourableOpen :
      encodeSix firstAssembledTailSix ≡ Base.hex-4
    secondSixIsFavourableOpen :
      encodeSix secondStructuralSix ≡ Base.hex-4

    concreteRelocationReallyClosed :
      Relocation.concreteComplexCarrierOutputRelocationClosed ≡ true
    primitiveSymmetrisedGainReallyRejected :
      NullAudit.symmetrisationSuppliesUniversalFirstAdjointLowGain ≡ false
    tailArithmeticReallyClosed :
      Tail.firstAdjointSobolevTailExponentArithmeticClosed ≡ true
    tailFunctionalTheoremReallyOpen :
      Tail.firstAdjointCutoffUniformFunctionalEstimateClosed ≡ false

    allRowsReallyEnumerated : Rows.allTwentyFourRowsEnumerated ≡ true
    allRowsReallyNotClosed : Rows.allTwentyFourNumericConstraintsClosed ≡ false

open Stage3Ternary369Receipt public

stage3Ternary369Receipt : Stage3Ternary369Receipt
stage3Ternary369Receipt =
  receipt refl refl refl refl refl refl refl refl
    Relocation.concreteComplexCarrierOutputRelocationClosedIsTrue
    NullAudit.symmetrisationSuppliesUniversalFirstAdjointLowGainIsFalse
    Tail.firstAdjointSobolevTailExponentArithmeticClosedIsTrue
    Tail.firstAdjointCutoffUniformFunctionalEstimateClosedIsFalse
    Rows.allTwentyFourRowsEnumeratedIsTrue
    Rows.allTwentyFourNumericConstraintsClosedIsFalse

hexProductOperationGloballyPromoted : Bool
hexProductOperationGloballyPromoted = false

hexProductOperationGloballyPromotedIsFalse :
  hexProductOperationGloballyPromoted ≡ false
hexProductOperationGloballyPromotedIsFalse = refl

nonaryProductOperationGloballyPromoted : Bool
nonaryProductOperationGloballyPromoted = false

nonaryProductOperationGloballyPromotedIsFalse :
  nonaryProductOperationGloballyPromoted ≡ false
nonaryProductOperationGloballyPromotedIsFalse = refl

stage3Ternary369LayerRepresented : Bool
stage3Ternary369LayerRepresented = true

stage3Ternary369LayerRepresentedIsTrue :
  stage3Ternary369LayerRepresented ≡ true
stage3Ternary369LayerRepresentedIsTrue = refl
