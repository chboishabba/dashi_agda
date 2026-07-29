module DASHI.Analysis.BishopFastCauchyCommonCompletionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import DASHI.Analysis.FastCauchyReals as Fast
import DASHI.Analysis.BishopConstructedRealBackendExact as Bishop
import DASHI.Analysis.FastCauchyConstructedRealBackendExact as FastBackend
import DASHI.Analysis.ConstructiveRealCategoricityExact as Categoricity
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Bishop and FastCauchy as presentations of one rational Cauchy completion.
--
-- Herman Geuvers and Milad Niqui,
-- "Constructive Reals in Coq: Axioms and Categoricity",
-- Types for Proofs and Programs, LNCS 2277 (2002), 79--95.
-- DOI: 10.1007/3-540-45842-5_6.
-- Theorem 4.1: Cauchy sequences over an Archimedean constructive ordered field
-- form a real-number structure.  Theorem 5.7: all such structures are
-- isomorphic through rational approximation and limits.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- Dalhousie University, April 2022, arXiv:2205.08354, no DOI.
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- 582c6afcdf805d06730c8c0aa970f4a6e033b611.
------------------------------------------------------------------------

record RationalCauchyCompletionPresentation
    (Real Rational Sequence : Set) : Set₁ where
  field
    representative : Real → Sequence
    term : Sequence → Nat → Rational
    RegularOrCauchy : Sequence → Set
    representativeRegular : ∀ value → RegularOrCauchy (representative value)

    Equality : Real → Real → Set
    EquivalentRepresentatives : Sequence → Sequence → Set
    equalityIffEquivalentRepresentatives : ∀ left right → Set

    realize : (sequence : Sequence) → RegularOrCauchy sequence → Real
    realizeRepresentativeRoundTrip : ∀ value →
      Equality (realize (representative value) (representativeRegular value)) value
    representativeRealizeRoundTrip : ∀ sequence regular →
      EquivalentRepresentatives
        (representative (realize sequence regular))
        sequence

    epsilonCauchySemantics : Set
    reciprocalNaturalSemanticsEquivalentAfterArchimedeanProof : Set

open RationalCauchyCompletionPresentation public

record BishopFastCauchyCommonCompletion
    (A : Fast.RationalMetricAuthority)
    (operations : Fast.FastCauchyOperations A)
    (bishopPackaging : Bishop.BishopAlgebraOrderPackaging)
    (fastPackaging : FastBackend.FastCauchyBackendPackaging A operations) : Set₂ where
  field
    Rational : Set
    BishopSequence FastSequence : Set

    bishopPresentation :
      RationalCauchyCompletionPresentation
        BishopReal.ℝ Rational BishopSequence
    fastPresentation :
      RationalCauchyCompletionPresentation
        (Fast.FastCauchyReal A) Rational FastSequence

    bishopRationalsAgreeWithImportedRepresentation : Set
    fastRationalsAgreeWithMetricAuthority :
      Rational ≡ Fast.Q A

    bishopRegularityAndFastCauchyReindex :
      BishopSequence → FastSequence
    fastCauchyAndBishopRegularityReindex :
      FastSequence → BishopSequence

    forwardReindexPreservesRationalTerms : ∀ sequence index → Set
    backwardReindexPreservesRationalTerms : ∀ sequence index → Set
    regularityImpliesDyadicFastCauchy : ∀ sequence → Set
    dyadicFastCauchyImpliesRegularity : ∀ sequence → Set

    forwardBridge :
      Categoricity.CommonRationalApproximationBridge
        (Bishop.bishopSetoidOrderedCompleteReal bishopPackaging)
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations fastPackaging)
    backwardBridge :
      Categoricity.CommonRationalApproximationBridge
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations fastPackaging)
        (Bishop.bishopSetoidOrderedCompleteReal bishopPackaging)

    bridgeRationalCarriersAgree :
      Categoricity.Q forwardBridge ≡ Categoricity.Q backwardBridge
    forwardBridgeGeneratedByReindexingAndFastLimit : Set
    backwardBridgeGeneratedByReindexingAndBishopLimit : Set
    bothAreCauchyCompletionsOfSameRationals : Set

open BishopFastCauchyCommonCompletion public

commonCompletionPresentation :
  ∀ {A operations bishopPackaging fastPackaging} →
  BishopFastCauchyCommonCompletion
    A operations bishopPackaging fastPackaging →
  Categoricity.CommonCauchyCompletionPresentation
    (Bishop.bishopSetoidOrderedCompleteReal bishopPackaging)
    (FastBackend.fastCauchySetoidOrderedCompleteReal operations fastPackaging)
commonCompletionPresentation dataSet = record
  { forward = forwardBridge dataSet
  ; backward = backwardBridge dataSet
  ; sameRationalCarrier = bridgeRationalCarriersAgree dataSet
  ; leftIsCauchyCompletionOfRationals =
      bothAreCauchyCompletionsOfSameRationals dataSet
  ; rightIsCauchyCompletionOfRationals =
      bothAreCauchyCompletionsOfSameRationals dataSet
  ; epsilonCauchyDefinitionSelected =
      epsilonCauchySemantics (bishopPresentation dataSet)
  ; reciprocalNaturalDefinitionEquivalentAfterArchimedeanProof =
      reciprocalNaturalSemanticsEquivalentAfterArchimedeanProof
        (fastPresentation dataSet)
  }

commonRationalCompletionDefinitionLevel : ProofLevel
commonRationalCompletionDefinitionLevel = machineChecked

bishopFastCauchyReindexingAndRepresentationInputsLevel : ProofLevel
bishopFastCauchyReindexingAndRepresentationInputsLevel = conditional
