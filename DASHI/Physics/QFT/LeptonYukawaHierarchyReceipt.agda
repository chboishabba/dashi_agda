module DASHI.Physics.QFT.LeptonYukawaHierarchyReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.LeptonYukawaFromLevelOverlapReceipt as Overlap

------------------------------------------------------------------------
-- Lepton Yukawa hierarchy aggregate receipt.
--
-- This receipt only aggregates the modular level-overlap ratios already
-- recorded by the level-overlap receipt:
--
--   generation 1: 1/2
--   generation 2: 0, meaning no overlap ratio
--   generation 3: 1/3 and 1/4 candidate branches
--
-- The aggregate is structural/candidate bookkeeping.  It does not promote a
-- physical lepton Yukawa operator, physical lepton masses, or any exact
-- Standard-Model/DHR match.

data LeptonYukawaHierarchyStatus : Set where
  modularOverlapHierarchyCandidateRecorded :
    LeptonYukawaHierarchyStatus

data LeptonYukawaHierarchyBlocker : Set where
  modularOverlapRatiosAreStructuralOnly :
    LeptonYukawaHierarchyBlocker

  generationTwoHasNoOverlapRatio :
    LeptonYukawaHierarchyBlocker

  generationThreeHasTwoCandidateRatios :
    LeptonYukawaHierarchyBlocker

  missingPhysicalLeptonYukawaOperator :
    LeptonYukawaHierarchyBlocker

  missingPhysicalLeptonMassRenormalisation :
    LeptonYukawaHierarchyBlocker

  exactStandardModelNotConstructed :
    LeptonYukawaHierarchyBlocker

canonicalLeptonYukawaHierarchyBlockers :
  List LeptonYukawaHierarchyBlocker
canonicalLeptonYukawaHierarchyBlockers =
  modularOverlapRatiosAreStructuralOnly
  ∷ generationTwoHasNoOverlapRatio
  ∷ generationThreeHasTwoCandidateRatios
  ∷ missingPhysicalLeptonYukawaOperator
  ∷ missingPhysicalLeptonMassRenormalisation
  ∷ exactStandardModelNotConstructed
  ∷ []

data LeptonYukawaHierarchyPromotion : Set where

leptonYukawaHierarchyPromotionImpossibleHere :
  LeptonYukawaHierarchyPromotion →
  ⊥
leptonYukawaHierarchyPromotionImpossibleHere ()

hierarchyBoundaryLabel : String
hierarchyBoundaryLabel =
  "Lepton Yukawa hierarchy aggregate records modular overlap ratios only: gen1=1/2, gen2=0, gen3=1/3 and 1/4; no physical Yukawa promotion"

record GenerationOverlapRatio : Set where
  field
    generationIndex :
      Nat

    ratio :
      Overlap.ExactRatio

    structuralCandidate :
      Bool

    structuralCandidateIsTrue :
      structuralCandidate ≡ true

    physicalYukawaPromoted :
      Bool

    physicalYukawaPromotedIsFalse :
      physicalYukawaPromoted ≡ false

    statement :
      String

open GenerationOverlapRatio public

generationOneHierarchyRatio :
  GenerationOverlapRatio
generationOneHierarchyRatio =
  record
    { generationIndex =
        1
    ; ratio =
        Overlap.genOneOneHalfRatio
    ; structuralCandidate =
        true
    ; structuralCandidateIsTrue =
        refl
    ; physicalYukawaPromoted =
        false
    ; physicalYukawaPromotedIsFalse =
        refl
    ; statement =
        "generation 1 modular overlap ratio candidate: 1/2"
    }

generationTwoHierarchyZero :
  GenerationOverlapRatio
generationTwoHierarchyZero =
  record
    { generationIndex =
        2
    ; ratio =
        Overlap.discElevenNoRatio
    ; structuralCandidate =
        true
    ; structuralCandidateIsTrue =
        refl
    ; physicalYukawaPromoted =
        false
    ; physicalYukawaPromotedIsFalse =
        refl
    ; statement =
        "generation 2 modular overlap ratio candidate: 0, recording no overlap ratio"
    }

generationThreeHierarchyOneThird :
  GenerationOverlapRatio
generationThreeHierarchyOneThird =
  record
    { generationIndex =
        3
    ; ratio =
        Overlap.genThreeOneThirdRatio
    ; structuralCandidate =
        true
    ; structuralCandidateIsTrue =
        refl
    ; physicalYukawaPromoted =
        false
    ; physicalYukawaPromotedIsFalse =
        refl
    ; statement =
        "generation 3 modular overlap ratio candidate: 1/3"
    }

generationThreeHierarchyOneQuarter :
  GenerationOverlapRatio
generationThreeHierarchyOneQuarter =
  record
    { generationIndex =
        3
    ; ratio =
        Overlap.genThreeOneQuarterRatio
    ; structuralCandidate =
        true
    ; structuralCandidateIsTrue =
        refl
    ; physicalYukawaPromoted =
        false
    ; physicalYukawaPromotedIsFalse =
        refl
    ; statement =
        "generation 3 modular overlap ratio candidate: 1/4"
    }

canonicalLeptonYukawaHierarchyRatios :
  List GenerationOverlapRatio
canonicalLeptonYukawaHierarchyRatios =
  generationOneHierarchyRatio
  ∷ generationTwoHierarchyZero
  ∷ generationThreeHierarchyOneThird
  ∷ generationThreeHierarchyOneQuarter
  ∷ []

record LeptonYukawaHierarchyReceipt : Setω where
  field
    sourceOverlapReceipt :
      Overlap.LeptonYukawaFromLevelOverlapReceipt

    sourceOverlapReceiptIsCanonical :
      sourceOverlapReceipt
      ≡
      Overlap.canonicalLeptonYukawaFromLevelOverlapReceipt

    status :
      LeptonYukawaHierarchyStatus

    statusIsModularOverlapHierarchyCandidateRecorded :
      status ≡ modularOverlapHierarchyCandidateRecorded

    hierarchyRatios :
      List GenerationOverlapRatio

    hierarchyRatiosAreCanonical :
      hierarchyRatios ≡ canonicalLeptonYukawaHierarchyRatios

    generationOneRatio :
      Overlap.ExactRatio

    generationOneRatioIsOneHalf :
      generationOneRatio ≡ Overlap.genOneOneHalfRatio

    generationOneReducedNumeratorIsOne :
      Overlap.reducedNumerator generationOneRatio ≡ 1

    generationOneReducedDenominatorIsTwo :
      Overlap.reducedDenominator generationOneRatio ≡ 2

    generationTwoRatio :
      Overlap.ExactRatio

    generationTwoRatioIsZero :
      generationTwoRatio ≡ Overlap.discElevenNoRatio

    generationTwoReducedNumeratorIsZero :
      Overlap.reducedNumerator generationTwoRatio ≡ 0

    generationThreeOneThird :
      Overlap.ExactRatio

    generationThreeOneThirdIsCanonical :
      generationThreeOneThird ≡ Overlap.genThreeOneThirdRatio

    generationThreeOneQuarter :
      Overlap.ExactRatio

    generationThreeOneQuarterIsCanonical :
      generationThreeOneQuarter ≡ Overlap.genThreeOneQuarterRatio

    structuralCandidateAggregate :
      Bool

    structuralCandidateAggregateIsTrue :
      structuralCandidateAggregate ≡ true

    physicalLeptonYukawaPromoted :
      Bool

    physicalLeptonYukawaPromotedIsFalse :
      physicalLeptonYukawaPromoted ≡ false

    physicalLeptonMassHierarchyPromoted :
      Bool

    physicalLeptonMassHierarchyPromotedIsFalse :
      physicalLeptonMassHierarchyPromoted ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    promotionFlags :
      List LeptonYukawaHierarchyPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    blockers :
      List LeptonYukawaHierarchyBlocker

    blockersAreCanonical :
      blockers ≡ canonicalLeptonYukawaHierarchyBlockers

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ hierarchyBoundaryLabel

    auditTrail :
      List String

open LeptonYukawaHierarchyReceipt public

canonicalLeptonYukawaHierarchyReceipt :
  LeptonYukawaHierarchyReceipt
canonicalLeptonYukawaHierarchyReceipt =
  record
    { sourceOverlapReceipt =
        Overlap.canonicalLeptonYukawaFromLevelOverlapReceipt
    ; sourceOverlapReceiptIsCanonical =
        refl
    ; status =
        modularOverlapHierarchyCandidateRecorded
    ; statusIsModularOverlapHierarchyCandidateRecorded =
        refl
    ; hierarchyRatios =
        canonicalLeptonYukawaHierarchyRatios
    ; hierarchyRatiosAreCanonical =
        refl
    ; generationOneRatio =
        Overlap.genOneOneHalfRatio
    ; generationOneRatioIsOneHalf =
        refl
    ; generationOneReducedNumeratorIsOne =
        refl
    ; generationOneReducedDenominatorIsTwo =
        refl
    ; generationTwoRatio =
        Overlap.discElevenNoRatio
    ; generationTwoRatioIsZero =
        refl
    ; generationTwoReducedNumeratorIsZero =
        refl
    ; generationThreeOneThird =
        Overlap.genThreeOneThirdRatio
    ; generationThreeOneThirdIsCanonical =
        refl
    ; generationThreeOneQuarter =
        Overlap.genThreeOneQuarterRatio
    ; generationThreeOneQuarterIsCanonical =
        refl
    ; structuralCandidateAggregate =
        true
    ; structuralCandidateAggregateIsTrue =
        refl
    ; physicalLeptonYukawaPromoted =
        false
    ; physicalLeptonYukawaPromotedIsFalse =
        refl
    ; physicalLeptonMassHierarchyPromoted =
        false
    ; physicalLeptonMassHierarchyPromotedIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; blockers =
        canonicalLeptonYukawaHierarchyBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        hierarchyBoundaryLabel
    ; receiptBoundaryIsCanonical =
        refl
    ; auditTrail =
        "Aggregated generation 1 modular overlap ratio candidate: 1/2"
        ∷ "Aggregated generation 2 modular overlap ratio candidate: 0 because D=-11 has no overlap ratio"
        ∷ "Aggregated generation 3 modular overlap ratio candidates: 1/3 and 1/4"
        ∷ "The aggregate is structural/candidate bookkeeping only"
        ∷ "No physical lepton Yukawa operator, lepton mass hierarchy, or exact SM promotion is introduced"
        ∷ []
    }

leptonYukawaHierarchyKeepsPhysicalYukawaFalse :
  physicalLeptonYukawaPromoted canonicalLeptonYukawaHierarchyReceipt
  ≡
  false
leptonYukawaHierarchyKeepsPhysicalYukawaFalse =
  refl

leptonYukawaHierarchyKeepsMassHierarchyFalse :
  physicalLeptonMassHierarchyPromoted canonicalLeptonYukawaHierarchyReceipt
  ≡
  false
leptonYukawaHierarchyKeepsMassHierarchyFalse =
  refl

leptonYukawaHierarchyKeepsExactSMFalse :
  exactStandardModelPromotion canonicalLeptonYukawaHierarchyReceipt
  ≡
  false
leptonYukawaHierarchyKeepsExactSMFalse =
  refl
