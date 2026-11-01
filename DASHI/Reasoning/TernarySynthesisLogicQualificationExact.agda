module DASHI.Reasoning.TernarySynthesisLogicQualificationExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Keep three logical resolutions orthogonal instead of replacing one by
-- another:
--
--   * the ternary 27-cell carries the local comparison+synthesis coordinate;
--   * the tetralemma support square records position/counterposition support;
--   * the existing sixfold carrier records bounded inexpressible,
--     underdetermined and scope-exceeded states.
--
-- A higher-order logical qualification retains the 27-cell carrier and adds
-- those observation/meta-status coordinates. In particular `bothSupported`
-- and `neitherEstablished` do not have to be collapsed into one ternary zero.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.SixfoldLogic as Six
import DASHI.Foundations.DialecticCubieTetralemmaExact as Tetra
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Synthesis

record TetralemmaQualifiedSynthesis : Set where
  constructor tetralemmaQualifiedSynthesis
  field
    synthesisCarrier : Synthesis.SynthesisChoice27
    supportSquare : Tetra.SupportCounterSquare
    tetralemmaPosition : Tetra.TetralemmaPosition
    tetralemmaPositionExact :
      tetralemmaPosition ≡ Tetra.classifySupportSquare supportSquare

open TetralemmaQualifiedSynthesis public

qualifyTetralemma :
  Synthesis.SynthesisChoice27 →
  Tetra.SupportCounterSquare →
  TetralemmaQualifiedSynthesis
qualifyTetralemma synthesis square =
  tetralemmaQualifiedSynthesis
    synthesis
    square
    (Tetra.classifySupportSquare square)
    refl

qualificationPreservesSynthesis :
  (synthesis : Synthesis.SynthesisChoice27) →
  (square : Tetra.SupportCounterSquare) →
  synthesisCarrier (qualifyTetralemma synthesis square) ≡ synthesis
qualificationPreservesSynthesis synthesis square = refl

positionOnlyQualification :
  Synthesis.SynthesisChoice27 → TetralemmaQualifiedSynthesis
positionOnlyQualification synthesis =
  qualifyTetralemma synthesis
    (Tetra.supportCounterSquare Tetra.supported Tetra.unsupported)

counterpositionOnlyQualification :
  Synthesis.SynthesisChoice27 → TetralemmaQualifiedSynthesis
counterpositionOnlyQualification synthesis =
  qualifyTetralemma synthesis
    (Tetra.supportCounterSquare Tetra.unsupported Tetra.supported)

bothSupportedQualification :
  Synthesis.SynthesisChoice27 → TetralemmaQualifiedSynthesis
bothSupportedQualification synthesis =
  qualifyTetralemma synthesis
    (Tetra.supportCounterSquare Tetra.supported Tetra.supported)

neitherEstablishedQualification :
  Synthesis.SynthesisChoice27 → TetralemmaQualifiedSynthesis
neitherEstablishedQualification synthesis =
  qualifyTetralemma synthesis
    (Tetra.supportCounterSquare Tetra.unsupported Tetra.unsupported)

bothPositionIsBothSupported :
  (synthesis : Synthesis.SynthesisChoice27) →
  tetralemmaPosition (bothSupportedQualification synthesis)
  ≡ Tetra.bothSupported
bothPositionIsBothSupported synthesis = refl

neitherPositionIsNeitherEstablished :
  (synthesis : Synthesis.SynthesisChoice27) →
  tetralemmaPosition (neitherEstablishedQualification synthesis)
  ≡ Tetra.neitherEstablished
neitherPositionIsNeitherEstablished synthesis = refl

------------------------------------------------------------------------
-- Sixfold meta-status is another retained coordinate, not a rewrite of the
-- ternary carrier or of the tetralemma support square.
------------------------------------------------------------------------

record SixfoldQualifiedSynthesis : Set where
  constructor sixfoldQualifiedSynthesis
  field
    tetralemmaQualified : TetralemmaQualifiedSynthesis
    sixfoldStatus : Six.Stage6

open SixfoldQualifiedSynthesis public

qualifySixfold :
  TetralemmaQualifiedSynthesis →
  Six.Stage6 →
  SixfoldQualifiedSynthesis
qualifySixfold synthesis status =
  sixfoldQualifiedSynthesis synthesis status

sixfoldQualificationPreservesTetralemmaCarrier :
  (synthesis : TetralemmaQualifiedSynthesis) →
  (status : Six.Stage6) →
  tetralemmaQualified (qualifySixfold synthesis status) ≡ synthesis
sixfoldQualificationPreservesTetralemmaCarrier synthesis status = refl

underdeterminedQualification :
  TetralemmaQualifiedSynthesis → SixfoldQualifiedSynthesis
underdeterminedQualification synthesis =
  qualifySixfold synthesis Six.underdetermined

scopeExceededQualification :
  TetralemmaQualifiedSynthesis → SixfoldQualifiedSynthesis
scopeExceededQualification synthesis =
  qualifySixfold synthesis Six.scopeExceeded

underdeterminedStatusRetained :
  (synthesis : TetralemmaQualifiedSynthesis) →
  sixfoldStatus (underdeterminedQualification synthesis)
  ≡ Six.underdetermined
underdeterminedStatusRetained synthesis = refl

scopeExceededStatusRetained :
  (synthesis : TetralemmaQualifiedSynthesis) →
  sixfoldStatus (scopeExceededQualification synthesis)
  ≡ Six.scopeExceeded
scopeExceededStatusRetained synthesis = refl

record SynthesisLogicQualificationBoundary : Set where
  field
    tetralemmaRetainsPriorCarrier : Bool
    tetralemmaRetainsPriorCarrierIsTrue :
      tetralemmaRetainsPriorCarrier ≡ true

    sixfoldRetainsTetralemmaCarrier : Bool
    sixfoldRetainsTetralemmaCarrierIsTrue :
      sixfoldRetainsTetralemmaCarrier ≡ true

    bothCollapsedToNeutralTrit : Bool
    bothCollapsedToNeutralTritIsFalse :
      bothCollapsedToNeutralTrit ≡ false

    neitherCollapsedToNeutralTrit : Bool
    neitherCollapsedToNeutralTritIsFalse :
      neitherCollapsedToNeutralTrit ≡ false

    scopeExceededPromotedToContradiction : Bool
    scopeExceededPromotedToContradictionIsFalse :
      scopeExceededPromotedToContradiction ≡ false

canonicalSynthesisLogicQualificationBoundary :
  SynthesisLogicQualificationBoundary
canonicalSynthesisLogicQualificationBoundary =
  record
    { tetralemmaRetainsPriorCarrier = true
    ; tetralemmaRetainsPriorCarrierIsTrue = refl
    ; sixfoldRetainsTetralemmaCarrier = true
    ; sixfoldRetainsTetralemmaCarrierIsTrue = refl
    ; bothCollapsedToNeutralTrit = false
    ; bothCollapsedToNeutralTritIsFalse = refl
    ; neitherCollapsedToNeutralTrit = false
    ; neitherCollapsedToNeutralTritIsFalse = refl
    ; scopeExceededPromotedToContradiction = false
    ; scopeExceededPromotedToContradictionIsFalse = refl
    }
