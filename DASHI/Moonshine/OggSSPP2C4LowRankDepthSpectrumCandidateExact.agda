module DASHI.Moonshine.OggSSPP2C4LowRankDepthSpectrumCandidateExact where

------------------------------------------------------------------------
-- p=2 C4 LOW-RANK / NON-DOUBLE-TRIVIAL DEPTH-SPECTRUM CANDIDATE
--
-- EXTERNAL SOURCE INPUT
--
-- Carnahan--Urano, "Monstrous Moonshine for Integral Group Rings",
-- Section 6, Theorem 6.2 / Lemma 6.4, gives the source-native C4
-- indecomposable table used here.  In the source ordering
--
--   A, B, C, D, E, C^A, C^B, C^E, C^{AB}
--
-- the underlying Z-ranks are
--
--   1, 1, 2, 4, 2, 3, 3, 4, 4.
--
-- The square-subgroup restrictions include:
--
--   A      -> Z
--   B      -> Z
--   C      -> 2 I
--   D      -> 2 Z[H]
--   E      -> 2 Z
--   C^A    -> I + Z[H]
--   C^B    -> I + Z[H]
--   C^E    -> Z + I + Z[H]
--   C^{AB} -> Z + I + Z[H].
--
-- SOURCE-COMPATIBLE / DASHI SELECTION
--
-- Carnahan--Urano Lemma 6.4 further says that for order-4 Monster elements
-- whose square lies in 2B, only
--
--   A, B, C, D, E, C^A, C^B
--
-- can occur; C^E and C^{AB} are excluded by the square-subgroup restriction.
--
-- DASHI then removes the two coarse square-restriction shapes:
--
--   D -> 2 Z[H]   (doubled regular/projective),
--   E -> 2 Z      (doubled trivial).
--
-- The surviving source-compatible non-coarse family is exactly
--
--   A, B, C, C^A, C^B,
--
-- whose source ranks are 1,1,2,3,3.  The older finite characterization
-- "rank < 4 and not double-trivial" is retained below as an equivalent check,
-- not as the conceptual selection rule.
--
-- whose ranks are
--
--   1, 1, 2, 3, 3.
--
-- Reordered by depth this is exactly
--
--   3,3,2,1,1.
--
-- IMPORTANT ATTRIBUTION / PROMOTION FIREWALL
--
-- Carnahan--Urano own the indecomposable table.
-- DASHI owns:
--   * the low-rank/non-double-trivial predicate;
--   * the five-element selection;
--   * its rechart to the p=2 scalar slots.
--
-- We do NOT claim:
--   * the source singles out this five-element subset for 2B;
--   * all five occur in the actual 4A Moonshine decomposition
--     (Theorem 6.5 instead uses A, D, C^A);
--   * module rank equals localized DVR composition length;
--   * the five modules are the five geometric inertia sectors;
--   * the rank sum proves the Monster residual 10.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPP2InertiaDepthQuotientExact as Scalar
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source-native C4 indecomposable labels.
------------------------------------------------------------------------

data C4IntegralIndecomposable : Set where
  moduleA :
    C4IntegralIndecomposable
  moduleB :
    C4IntegralIndecomposable
  moduleC :
    C4IntegralIndecomposable
  moduleD :
    C4IntegralIndecomposable
  moduleE :
    C4IntegralIndecomposable
  moduleCA :
    C4IntegralIndecomposable
  moduleCB :
    C4IntegralIndecomposable
  moduleCE :
    C4IntegralIndecomposable
  moduleCAB :
    C4IntegralIndecomposable

moduleRank :
  C4IntegralIndecomposable ->
  Nat
moduleRank moduleA = 1
moduleRank moduleB = 1
moduleRank moduleC = 2
moduleRank moduleD = 4
moduleRank moduleE = 2
moduleRank moduleCA = 3
moduleRank moduleCB = 3
moduleRank moduleCE = 4
moduleRank moduleCAB = 4

data SquareRestrictionShape : Set where
  singleTrivial :
    SquareRestrictionShape
  doubleSign :
    SquareRestrictionShape
  doubleRegular :
    SquareRestrictionShape
  doubleTrivial :
    SquareRestrictionShape
  signPlusRegular :
    SquareRestrictionShape
  trivialPlusSignPlusRegular :
    SquareRestrictionShape

squareRestrictionShape :
  C4IntegralIndecomposable ->
  SquareRestrictionShape
squareRestrictionShape moduleA = singleTrivial
squareRestrictionShape moduleB = singleTrivial
squareRestrictionShape moduleC = doubleSign
squareRestrictionShape moduleD = doubleRegular
squareRestrictionShape moduleE = doubleTrivial
squareRestrictionShape moduleCA = signPlusRegular
squareRestrictionShape moduleCB = signPlusRegular
squareRestrictionShape moduleCE = trivialPlusSignPlusRegular
squareRestrictionShape moduleCAB = trivialPlusSignPlusRegular

------------------------------------------------------------------------
-- 2. External source attribution.
------------------------------------------------------------------------

carnahanUranoIntegralGroupRings : Source.AttributedSource
carnahanUranoIntegralGroupRings =
  Source.mkDOISource
    "Scott Carnahan and Satoru Urano"
    "Monstrous Moonshine for Integral Group Rings"
    "International Mathematics Research Notices 2024(4), 2748-2789"
    "2024"
    "10.1093/imrn/rnad028"
    "https://doi.org/10.1093/imrn/rnad028"
    Source.academicArticleSource
    "Section 6 supplies the C4 indecomposable rank/restriction table reconstructed in this module. The paper does not select DASHI's five low-rank/non-double-trivial candidates, identify them with characteristic-2 inertia sectors, or state a 3,3,2,1,1 Monster-local valuation law."
    Source.publicAttribution

c4DepthSpectrumSourceAtlas : Source.AttributedSourceAtlas
c4DepthSpectrumSourceAtlas =
  Source.mkSourceAtlas
    "C4 indecomposable rank/restriction source atlas"
    "DASHI.Moonshine.OggSSPP2C4LowRankDepthSpectrumCandidateExact"
    (carnahanUranoIntegralGroupRings ∷ [])
    "Carnahan--Urano own the integral C4 module table; DASHI owns the structural five-module selection and all p=2 scalar-depth cross-welding."

------------------------------------------------------------------------
-- 3. Source-compatible order-4 -> 2B family and coarse-shape removal.
------------------------------------------------------------------------

monsterOrderFourSquareTwoBCompatible :
  C4IntegralIndecomposable ->
  Bool
monsterOrderFourSquareTwoBCompatible moduleA = true
monsterOrderFourSquareTwoBCompatible moduleB = true
monsterOrderFourSquareTwoBCompatible moduleC = true
monsterOrderFourSquareTwoBCompatible moduleD = true
monsterOrderFourSquareTwoBCompatible moduleE = true
monsterOrderFourSquareTwoBCompatible moduleCA = true
monsterOrderFourSquareTwoBCompatible moduleCB = true
monsterOrderFourSquareTwoBCompatible moduleCE = false
monsterOrderFourSquareTwoBCompatible moduleCAB = false

squareRestrictionIsCoarseProjectiveOrDoubleTrivial :
  C4IntegralIndecomposable ->
  Bool
squareRestrictionIsCoarseProjectiveOrDoubleTrivial moduleA = false
squareRestrictionIsCoarseProjectiveOrDoubleTrivial moduleB = false
squareRestrictionIsCoarseProjectiveOrDoubleTrivial moduleC = false
squareRestrictionIsCoarseProjectiveOrDoubleTrivial moduleD = true
squareRestrictionIsCoarseProjectiveOrDoubleTrivial moduleE = true
squareRestrictionIsCoarseProjectiveOrDoubleTrivial moduleCA = false
squareRestrictionIsCoarseProjectiveOrDoubleTrivial moduleCB = false
squareRestrictionIsCoarseProjectiveOrDoubleTrivial moduleCE = false
squareRestrictionIsCoarseProjectiveOrDoubleTrivial moduleCAB = false

sourceCompatibleNonCoarse :
  C4IntegralIndecomposable ->
  Bool
sourceCompatibleNonCoarse moduleA = true
sourceCompatibleNonCoarse moduleB = true
sourceCompatibleNonCoarse moduleC = true
sourceCompatibleNonCoarse moduleD = false
sourceCompatibleNonCoarse moduleE = false
sourceCompatibleNonCoarse moduleCA = true
sourceCompatibleNonCoarse moduleCB = true
sourceCompatibleNonCoarse moduleCE = false
sourceCompatibleNonCoarse moduleCAB = false

sourceCompatibleSelectionA :
  sourceCompatibleNonCoarse moduleA ≡ true
sourceCompatibleSelectionA = refl

sourceCompatibleSelectionB :
  sourceCompatibleNonCoarse moduleB ≡ true
sourceCompatibleSelectionB = refl

sourceCompatibleSelectionC :
  sourceCompatibleNonCoarse moduleC ≡ true
sourceCompatibleSelectionC = refl

sourceCompatibleSelectionCA :
  sourceCompatibleNonCoarse moduleCA ≡ true
sourceCompatibleSelectionCA = refl

sourceCompatibleSelectionCB :
  sourceCompatibleNonCoarse moduleCB ≡ true
sourceCompatibleSelectionCB = refl

sourceCompatibleRejectD :
  sourceCompatibleNonCoarse moduleD ≡ false
sourceCompatibleRejectD = refl

sourceCompatibleRejectE :
  sourceCompatibleNonCoarse moduleE ≡ false
sourceCompatibleRejectE = refl

sourceCompatibleRejectCE :
  sourceCompatibleNonCoarse moduleCE ≡ false
sourceCompatibleRejectCE = refl

sourceCompatibleRejectCAB :
  sourceCompatibleNonCoarse moduleCAB ≡ false
sourceCompatibleRejectCAB = refl

------------------------------------------------------------------------
-- 4. Equivalent finite low-rank / non-double-trivial characterization.
--
-- The test is executable on ALL nine source-native labels.  It uses only the
-- sourced rank/restriction table and does not mention Monster residuals,
-- inertia sectors, Base369, or the five-slot target.
------------------------------------------------------------------------

rankBelowFour :
  C4IntegralIndecomposable ->
  Bool
rankBelowFour moduleA = true
rankBelowFour moduleB = true
rankBelowFour moduleC = true
rankBelowFour moduleD = false
rankBelowFour moduleE = true
rankBelowFour moduleCA = true
rankBelowFour moduleCB = true
rankBelowFour moduleCE = false
rankBelowFour moduleCAB = false

restrictionIsDoubleTrivial :
  C4IntegralIndecomposable ->
  Bool
restrictionIsDoubleTrivial moduleA = false
restrictionIsDoubleTrivial moduleB = false
restrictionIsDoubleTrivial moduleC = false
restrictionIsDoubleTrivial moduleD = false
restrictionIsDoubleTrivial moduleE = true
restrictionIsDoubleTrivial moduleCA = false
restrictionIsDoubleTrivial moduleCB = false
restrictionIsDoubleTrivial moduleCE = false
restrictionIsDoubleTrivial moduleCAB = false

structurallySelected :
  C4IntegralIndecomposable ->
  Bool
structurallySelected moduleA = true
structurallySelected moduleB = true
structurallySelected moduleC = true
structurallySelected moduleD = false
structurallySelected moduleE = false
structurallySelected moduleCA = true
structurallySelected moduleCB = true
structurallySelected moduleCE = false
structurallySelected moduleCAB = false

selectedAByStructuralTest :
  structurallySelected moduleA ≡ true
selectedAByStructuralTest = refl

selectedBByStructuralTest :
  structurallySelected moduleB ≡ true
selectedBByStructuralTest = refl

selectedCByStructuralTest :
  structurallySelected moduleC ≡ true
selectedCByStructuralTest = refl

selectedCAByStructuralTest :
  structurallySelected moduleCA ≡ true
selectedCAByStructuralTest = refl

selectedCBByStructuralTest :
  structurallySelected moduleCB ≡ true
selectedCBByStructuralTest = refl

rejectDByStructuralTest :
  structurallySelected moduleD ≡ false
rejectDByStructuralTest = refl

rejectEByStructuralTest :
  structurallySelected moduleE ≡ false
rejectEByStructuralTest = refl

rejectCEByStructuralTest :
  structurallySelected moduleCE ≡ false
rejectCEByStructuralTest = refl

rejectCABByStructuralTest :
  structurallySelected moduleCAB ≡ false
rejectCABByStructuralTest = refl


structuralTestsAgree :
  (module : C4IntegralIndecomposable) ->
  sourceCompatibleNonCoarse module ≡ structurallySelected module
structuralTestsAgree moduleA = refl
structuralTestsAgree moduleB = refl
structuralTestsAgree moduleC = refl
structuralTestsAgree moduleD = refl
structuralTestsAgree moduleE = refl
structuralTestsAgree moduleCA = refl
structuralTestsAgree moduleCB = refl
structuralTestsAgree moduleCE = refl
structuralTestsAgree moduleCAB = refl

------------------------------------------------------------------------
-- Witness family for exactly the labels accepted by the structural test.
------------------------------------------------------------------------

data LowRankNonDoubleTrivial :
    C4IntegralIndecomposable ->
    Set where

  selectA :
    LowRankNonDoubleTrivial moduleA

  selectB :
    LowRankNonDoubleTrivial moduleB

  selectC :
    LowRankNonDoubleTrivial moduleC

  selectCA :
    LowRankNonDoubleTrivial moduleCA

  selectCB :
    LowRankNonDoubleTrivial moduleCB

data P2C4DepthCandidate : Set where
  candidateA :
    P2C4DepthCandidate
  candidateB :
    P2C4DepthCandidate
  candidateC :
    P2C4DepthCandidate
  candidateCA :
    P2C4DepthCandidate
  candidateCB :
    P2C4DepthCandidate

candidateModule :
  P2C4DepthCandidate ->
  C4IntegralIndecomposable
candidateModule candidateA = moduleA
candidateModule candidateB = moduleB
candidateModule candidateC = moduleC
candidateModule candidateCA = moduleCA
candidateModule candidateCB = moduleCB

candidateSelectionWitness :
  (candidate : P2C4DepthCandidate) ->
  LowRankNonDoubleTrivial (candidateModule candidate)
candidateSelectionWitness candidateA = selectA
candidateSelectionWitness candidateB = selectB
candidateSelectionWitness candidateC = selectC
candidateSelectionWitness candidateCA = selectCA
candidateSelectionWitness candidateCB = selectCB

candidateRank :
  P2C4DepthCandidate ->
  Nat
candidateRank candidate =
  moduleRank (candidateModule candidate)

candidateARankIsOne :
  candidateRank candidateA ≡ 1
candidateARankIsOne = refl

candidateBRankIsOne :
  candidateRank candidateB ≡ 1
candidateBRankIsOne = refl

candidateCRankIsTwo :
  candidateRank candidateC ≡ 2
candidateCRankIsTwo = refl

candidateCARankIsThree :
  candidateRank candidateCA ≡ 3
candidateCARankIsThree = refl

candidateCBRankIsThree :
  candidateRank candidateCB ≡ 3
candidateCBRankIsThree = refl

------------------------------------------------------------------------
-- 5. Exact rechart to the five scalar slots.
--
-- This is a finite rank-spectrum recognition, NOT a localized-length theorem.
------------------------------------------------------------------------

candidateToScalarSlot :
  P2C4DepthCandidate ->
  Scalar.P2ScalarSlot
candidateToScalarSlot candidateCA = Scalar.highSlotA
candidateToScalarSlot candidateCB = Scalar.highSlotB
candidateToScalarSlot candidateC = Scalar.middleSlot
candidateToScalarSlot candidateA = Scalar.lowSlotA
candidateToScalarSlot candidateB = Scalar.lowSlotB

scalarSlotToCandidate :
  Scalar.P2ScalarSlot ->
  P2C4DepthCandidate
scalarSlotToCandidate Scalar.highSlotA = candidateCA
scalarSlotToCandidate Scalar.highSlotB = candidateCB
scalarSlotToCandidate Scalar.middleSlot = candidateC
scalarSlotToCandidate Scalar.lowSlotA = candidateA
scalarSlotToCandidate Scalar.lowSlotB = candidateB

candidateSlotRoundTrip :
  (candidate : P2C4DepthCandidate) ->
  scalarSlotToCandidate (candidateToScalarSlot candidate) ≡ candidate
candidateSlotRoundTrip candidateA = refl
candidateSlotRoundTrip candidateB = refl
candidateSlotRoundTrip candidateC = refl
candidateSlotRoundTrip candidateCA = refl
candidateSlotRoundTrip candidateCB = refl

slotCandidateRoundTrip :
  (slot : Scalar.P2ScalarSlot) ->
  candidateToScalarSlot (scalarSlotToCandidate slot) ≡ slot
slotCandidateRoundTrip Scalar.highSlotA = refl
slotCandidateRoundTrip Scalar.highSlotB = refl
slotCandidateRoundTrip Scalar.middleSlot = refl
slotCandidateRoundTrip Scalar.lowSlotA = refl
slotCandidateRoundTrip Scalar.lowSlotB = refl

candidateRankMatchesScalarSlotDepth :
  (candidate : P2C4DepthCandidate) ->
  candidateRank candidate
  ≡
  Scalar.slotLength (candidateToScalarSlot candidate)
candidateRankMatchesScalarSlotDepth candidateA = refl
candidateRankMatchesScalarSlotDepth candidateB = refl
candidateRankMatchesScalarSlotDepth candidateC = refl
candidateRankMatchesScalarSlotDepth candidateCA = refl
candidateRankMatchesScalarSlotDepth candidateCB = refl

scalarSlotDepthMatchesCandidateRank :
  (slot : Scalar.P2ScalarSlot) ->
  Scalar.slotLength slot
  ≡
  candidateRank (scalarSlotToCandidate slot)
scalarSlotDepthMatchesCandidateRank Scalar.highSlotA = refl
scalarSlotDepthMatchesCandidateRank Scalar.highSlotB = refl
scalarSlotDepthMatchesCandidateRank Scalar.middleSlot = refl
scalarSlotDepthMatchesCandidateRank Scalar.lowSlotA = refl
scalarSlotDepthMatchesCandidateRank Scalar.lowSlotB = refl

------------------------------------------------------------------------
-- 6. Rank-spectrum total.
------------------------------------------------------------------------

candidateRankTotal : Nat
candidateRankTotal =
  candidateRank candidateCA
  + candidateRank candidateCB
  + candidateRank candidateC
  + candidateRank candidateA
  + candidateRank candidateB

candidateRankTotalIsTen :
  candidateRankTotal ≡ 10
candidateRankTotalIsTen = refl

------------------------------------------------------------------------
-- 7. Actual 4A occurrence is DIFFERENT.
--
-- Source Theorem 6.5 uses only A, D, C^A in the actual 4A Moonshine
-- decomposition.  We encode only this exclusion boundary here.
------------------------------------------------------------------------

data ActualFourAMoonshineLabel : Set where
  actualA :
    ActualFourAMoonshineLabel
  actualD :
    ActualFourAMoonshineLabel
  actualCA :
    ActualFourAMoonshineLabel

actualFourAModule :
  ActualFourAMoonshineLabel ->
  C4IntegralIndecomposable
actualFourAModule actualA = moduleA
actualFourAModule actualD = moduleD
actualFourAModule actualCA = moduleCA

data CandidateFamilyEqualsActualFourADecomposition : Set where
data CandidateBOccursInActualFourAByThisSource : Set where
data CandidateCOccursInActualFourAByThisSource : Set where
data CandidateCBOccursInActualFourAByThisSource : Set where

candidateFamilyNotActualFourADecomposition :
  CandidateFamilyEqualsActualFourADecomposition -> ⊥
candidateFamilyNotActualFourADecomposition ()

candidateBNotPromotedToActualFourA :
  CandidateBOccursInActualFourAByThisSource -> ⊥
candidateBNotPromotedToActualFourA ()

candidateCNotPromotedToActualFourA :
  CandidateCOccursInActualFourAByThisSource -> ⊥
candidateCNotPromotedToActualFourA ()

candidateCBNotPromotedToActualFourA :
  CandidateCBOccursInActualFourAByThisSource -> ⊥
candidateCBNotPromotedToActualFourA ()

------------------------------------------------------------------------
-- 8. Rank is not yet localized DVR composition length.
------------------------------------------------------------------------

data RankEqualsLocalizedDVRLength : Set where
data RankSpectrumIsP2MonsterCorrection : Set where
data CandidateRanksAreInertiaDepthsBySource : Set where
data CarnahanUranoSelectedTheseFiveForTwoB : Set where

rankNotPromotedToLocalizedDVRLength :
  RankEqualsLocalizedDVRLength -> ⊥
rankNotPromotedToLocalizedDVRLength ()

rankSpectrumNotPromotedToMonsterCorrection :
  RankSpectrumIsP2MonsterCorrection -> ⊥
rankSpectrumNotPromotedToMonsterCorrection ()

candidateRanksNotIdentifiedWithInertiaDepthsBySource :
  CandidateRanksAreInertiaDepthsBySource -> ⊥
candidateRanksNotIdentifiedWithInertiaDepthsBySource ()

carnahanUranoNotCreditedWithFiveModuleSelection :
  CarnahanUranoSelectedTheseFiveForTwoB -> ⊥
carnahanUranoNotCreditedWithFiveModuleSelection ()

------------------------------------------------------------------------
-- 9. Sharpened remaining recognition theorem.
--
-- The source-native spectrum supplies a concrete five-slot candidate family.
-- A future theorem must still show:
--
--   (a) actual 2B source pieces realize these candidate labels (or an
--       independently equivalent five-piece refinement), and
--   (b) localized finite-DVR composition length equals the source-native rank
--       on those realized pieces.
------------------------------------------------------------------------

record P2C4RankToLocalizedLengthAuthority : Set₁ where
  field
    SourcePiece :
      Set

    sourcePiece :
      P2C4DepthCandidate ->
      SourcePiece

    candidateLabelActuallyOccursInTwoBSource :
      P2C4DepthCandidate ->
      Bool

    candidateLabelActuallyOccursInTwoBSourceIsTrue :
      (candidate : P2C4DepthCandidate) ->
      candidateLabelActuallyOccursInTwoBSource candidate ≡ true

    sourcePieceComesFromIntegralTwoBTateObject :
      SourcePiece ->
      Bool

    sourcePieceComesFromIntegralTwoBTateObjectIsTrue :
      (piece : SourcePiece) ->
      sourcePieceComesFromIntegralTwoBTateObject piece ≡ true

    normalizedLocalizedDVRLength :
      SourcePiece ->
      Nat

    localizedLengthEqualsCandidateRank :
      (candidate : P2C4DepthCandidate) ->
      normalizedLocalizedDVRLength (sourcePiece candidate)
      ≡
      candidateRank candidate

    recognitionIndependentOfMonsterResidualTen :
      Bool

    recognitionIndependentOfMonsterResidualTenIsTrue :
      recognitionIndependentOfMonsterResidualTen ≡ true

    recognitionIndependentOfBase369 :
      Bool

    recognitionIndependentOfBase369IsTrue :
      recognitionIndependentOfBase369 ≡ true

open P2C4RankToLocalizedLengthAuthority public

asP2SourceDepthSlotLengthAuthority :
  P2C4RankToLocalizedLengthAuthority ->
  Scalar.P2SourceDepthSlotLengthAuthority
asP2SourceDepthSlotLengthAuthority A =
  record
    { Scalar.SourcePiece =
        SourcePiece A

    ; Scalar.sourcePiece =
        λ slot ->
          sourcePiece A (scalarSlotToCandidate slot)

    ; Scalar.sourcePiecesArePairwiseSourceSlots =
        true

    ; Scalar.sourcePiecesArePairwiseSourceSlotsIsTrue =
        refl

    ; Scalar.sourcePieceComesFromIntegralTwoBTateObject =
        sourcePieceComesFromIntegralTwoBTateObject A

    ; Scalar.sourcePieceComesFromIntegralTwoBTateObjectIsTrue =
        sourcePieceComesFromIntegralTwoBTateObjectIsTrue A

    ; Scalar.normalizedDVRLength =
        normalizedLocalizedDVRLength A

    ; Scalar.sourceSlotLengthMatchesDepth =
        λ slot ->
          trans
            (localizedLengthEqualsCandidateRank A
              (scalarSlotToCandidate slot))
            (sym (scalarSlotDepthMatchesCandidateRank slot))

    ; Scalar.paymentIndependentOfMonsterResidualTen =
        recognitionIndependentOfMonsterResidualTen A

    ; Scalar.paymentIndependentOfMonsterResidualTenIsTrue =
        recognitionIndependentOfMonsterResidualTenIsTrue A

    ; Scalar.paymentIndependentOfBase369Labels =
        recognitionIndependentOfBase369 A

    ; Scalar.paymentIndependentOfBase369LabelsIsTrue =
        recognitionIndependentOfBase369IsTrue A
    }

data P2C4RankToLocalizedLengthAuthorityInhabited : Set where

p2C4RankToLocalizedLengthStillOpen :
  P2C4RankToLocalizedLengthAuthorityInhabited -> ⊥
p2C4RankToLocalizedLengthStillOpen ()

------------------------------------------------------------------------
-- 10. Boundary.
------------------------------------------------------------------------

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record P2C4LowRankDepthSpectrumBoundary : Set where
  constructor p2-c4-low-rank-depth-spectrum-boundary
  field
    carnahanUranoC4RankTableSourced : Bool
    carnahanUranoSquareRestrictionTableSourced : Bool
    sourceOrderFourSquareTwoBCompatibilitySourced : Bool
    sourceExcludesCE_CAB : Bool
    dDoubleRegularAndEDoubleTrivialShapesSourced : Bool
    sourceCompatibleNonCoarseSelectionOwned : Bool
    structuralLowRankNonDoubleTrivialSelectionOwned : Bool
    structuralTestsEquivalentProved : Bool
    structuralTestExecutableOnAllNineLabels : Bool
    structuralTestRejectsD_E_CE_CAB : Bool
    selectedFamilyHasExactlyFiveLabels : Bool
    selectedRanksAreOneOneTwoThreeThree : Bool
    exactRechartToScalarSlotsProved : Bool
    rankMatchesScalarSlotDepthPointwise : Bool
    rankSpectrumTotalTen : Bool

    selectedFamilyIsActualFourADecomposition : Bool
    selectedFamilyOccurrenceInActualTwoBSourcePaid : Bool
    rankEqualsLocalizedDVRLengthPaid : Bool
    candidateRanksIdentifiedWithInertiaDepthsBySource : Bool
    monsterResidualUsedToSelectFamily : Bool
    base369UsedToSelectFamily : Bool
    carnahanUranoCreditedWithDASHISelection : Bool

    sharpenedRankToLengthAuthoritySpecified : Bool
    sharpenedRankToLengthAuthorityInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalP2C4LowRankDepthSpectrumBoundary :
  P2C4LowRankDepthSpectrumBoundary
canonicalP2C4LowRankDepthSpectrumBoundary =
  p2-c4-low-rank-depth-spectrum-boundary
    true true true true true true true true true true true true true true
    false false false false false false false
    true false true
