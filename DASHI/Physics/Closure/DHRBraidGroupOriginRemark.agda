module DASHI.Physics.Closure.DHRBraidGroupOriginRemark where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

open import Base369 using (TriTruth; tri-mid)
import LogicTlurey as LT

------------------------------------------------------------------------
-- DHR braid-group origin remark.
--
-- This is an origin/narrative receipt only.  It records the standard B3
-- presentation as the first non-abelian braid-group locus behind the
-- Yang-Baxter/DHR hexagon vocabulary, contrasts it with the abelian B2 = Z
-- surface, and links the Klein-quartic / mapping-class / PSL(2,F7) finite
-- symmetry relation as a finite-symmetry remark.  It also records the
-- LogicTlurey resonance-resonance join as the local tri-mid origin marker.
--
-- No DHR theorem, CKM derivation, Yang-Mills result, or Clay promotion is
-- asserted here.

data DHRBraidGroupOriginRemarkStatus : Set where
  originRemark_notNewMathematics :
    DHRBraidGroupOriginRemarkStatus

data BraidGroupRank : Set where
  B2 :
    BraidGroupRank

  B3 :
    BraidGroupRank

data BraidGroupPresentation : Set where
  ArtinB3Presentation :
    BraidGroupPresentation

data BraidGroupOriginRole : Set where
  YangBaxterDHRHexagonOrigin :
    BraidGroupOriginRole

  B2AbelianNoMixingOrigin :
    BraidGroupOriginRole

  B3FirstNonAbelianOrigin :
    BraidGroupOriginRole

data FiniteSymmetryOriginRelation : Set where
  KleinQuarticMappingClassPSL2F7Relation :
    FiniteSymmetryOriginRelation

data LogicTlureyOriginRelation : Set where
  resonanceResonanceTriMidJoin :
    LogicTlureyOriginRelation

data PromotionToken : Set where

promotionImpossibleHere :
  PromotionToken →
  ⊥
promotionImpossibleHere ()

canonicalOriginRoles :
  List BraidGroupOriginRole
canonicalOriginRoles =
  YangBaxterDHRHexagonOrigin
  ∷ B2AbelianNoMixingOrigin
  ∷ B3FirstNonAbelianOrigin
  ∷ []

canonicalFiniteSymmetryRelations :
  List FiniteSymmetryOriginRelation
canonicalFiniteSymmetryRelations =
  KleinQuarticMappingClassPSL2F7Relation
  ∷ []

canonicalLogicTlureyRelations :
  List LogicTlureyOriginRelation
canonicalLogicTlureyRelations =
  resonanceResonanceTriMidJoin
  ∷ []

B3PresentationStatement :
  String
B3PresentationStatement =
  "B3 has Artin presentation <sigma1,sigma2 | sigma1 sigma2 sigma1 = sigma2 sigma1 sigma2>; this is the braid/Yang-Baxter relation used as DHR-hexagon origin vocabulary."

B2AbelianStatement :
  String
B2AbelianStatement =
  "B2 is isomorphic to Z and is abelian; this origin surface alone supplies no non-abelian CKM mixing mechanism."

B3FirstNonAbelianStatement :
  String
B3FirstNonAbelianStatement =
  "B3 is the first non-abelian braid group, so the first braid-group source where Yang-Baxter/DHR-hexagon non-commutation can be named."

KleinQuarticRelationStatement :
  String
KleinQuarticRelationStatement =
  "The Klein quartic, mapping-class symmetry, and PSL(2,F7) finite automorphism relation are recorded as a finite-symmetry origin relation only."

LogicTlureyJoinStatement :
  String
LogicTlureyJoinStatement =
  "LogicTlurey combineStage resonance resonance = tri-mid is read here as the Bruhat-Tits tree join/origin remark."

boundaryStatement :
  String
boundaryStatement =
  "Origin remark only: no DHR theorem, no CKM derivation, no Yang-Mills result, and no Clay promotion are asserted."

record DHRBraidGroupOriginRemark : Set where
  field
    status :
      DHRBraidGroupOriginRemarkStatus

    statusIsOriginRemark :
      status ≡ originRemark_notNewMathematics

    presentationRank :
      BraidGroupRank

    presentationRankIsB3 :
      presentationRank ≡ B3

    presentation :
      BraidGroupPresentation

    presentationIsArtinB3 :
      presentation ≡ ArtinB3Presentation

    presentationSummary :
      String

    presentationSummaryIsCanonical :
      presentationSummary ≡ B3PresentationStatement

    braidRelationIsYangBaxterOrigin :
      Bool

    braidRelationIsYangBaxterOriginIsTrue :
      braidRelationIsYangBaxterOrigin ≡ true

    braidRelationIsDHRHexagonOrigin :
      Bool

    braidRelationIsDHRHexagonOriginIsTrue :
      braidRelationIsDHRHexagonOrigin ≡ true

    B2Rank :
      BraidGroupRank

    B2RankIsB2 :
      B2Rank ≡ B2

    B2IsZAbelian :
      Bool

    B2IsZAbelianIsTrue :
      B2IsZAbelian ≡ true

    B2AbelianSummary :
      String

    B2AbelianSummaryIsCanonical :
      B2AbelianSummary ≡ B2AbelianStatement

    B2SuppliesCKMMixing :
      Bool

    B2SuppliesCKMMixingIsFalse :
      B2SuppliesCKMMixing ≡ false

    B3IsFirstNonAbelianBraidGroup :
      Bool

    B3IsFirstNonAbelianBraidGroupIsTrue :
      B3IsFirstNonAbelianBraidGroup ≡ true

    B3FirstNonAbelianSummary :
      String

    B3FirstNonAbelianSummaryIsCanonical :
      B3FirstNonAbelianSummary ≡ B3FirstNonAbelianStatement

    originRoles :
      List BraidGroupOriginRole

    originRolesAreCanonical :
      originRoles ≡ canonicalOriginRoles

    finiteSymmetryRelations :
      List FiniteSymmetryOriginRelation

    finiteSymmetryRelationsAreCanonical :
      finiteSymmetryRelations ≡ canonicalFiniteSymmetryRelations

    KleinQuarticPSL2F7Order :
      Nat

    KleinQuarticPSL2F7OrderIs168 :
      KleinQuarticPSL2F7Order ≡ 168

    KleinQuarticRelationSummary :
      String

    KleinQuarticRelationSummaryIsCanonical :
      KleinQuarticRelationSummary ≡ KleinQuarticRelationStatement

    LogicTlureyRelations :
      List LogicTlureyOriginRelation

    LogicTlureyRelationsAreCanonical :
      LogicTlureyRelations ≡ canonicalLogicTlureyRelations

    LogicTlureyJoinValue :
      TriTruth

    LogicTlureyJoinValueIsTriMid :
      LogicTlureyJoinValue ≡ tri-mid

    LogicTlureyResonanceJoinProof :
      LT.combineStage LT.resonance LT.resonance ≡ tri-mid

    LogicTlureyJoinSummary :
      String

    LogicTlureyJoinSummaryIsCanonical :
      LogicTlureyJoinSummary ≡ LogicTlureyJoinStatement

    DHRTheoremPromoted :
      Bool

    DHRTheoremPromotedIsFalse :
      DHRTheoremPromoted ≡ false

    CKMPromoted :
      Bool

    CKMPromotedIsFalse :
      CKMPromoted ≡ false

    YangMillsPromoted :
      Bool

    YangMillsPromotedIsFalse :
      YangMillsPromoted ≡ false

    ClayPromoted :
      Bool

    ClayPromotedIsFalse :
      ClayPromoted ≡ false

    promotionFlags :
      List PromotionToken

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ boundaryStatement

open DHRBraidGroupOriginRemark public

canonicalDHRBraidGroupOriginRemark :
  DHRBraidGroupOriginRemark
canonicalDHRBraidGroupOriginRemark =
  record
    { status =
        originRemark_notNewMathematics
    ; statusIsOriginRemark =
        refl
    ; presentationRank =
        B3
    ; presentationRankIsB3 =
        refl
    ; presentation =
        ArtinB3Presentation
    ; presentationIsArtinB3 =
        refl
    ; presentationSummary =
        B3PresentationStatement
    ; presentationSummaryIsCanonical =
        refl
    ; braidRelationIsYangBaxterOrigin =
        true
    ; braidRelationIsYangBaxterOriginIsTrue =
        refl
    ; braidRelationIsDHRHexagonOrigin =
        true
    ; braidRelationIsDHRHexagonOriginIsTrue =
        refl
    ; B2Rank =
        B2
    ; B2RankIsB2 =
        refl
    ; B2IsZAbelian =
        true
    ; B2IsZAbelianIsTrue =
        refl
    ; B2AbelianSummary =
        B2AbelianStatement
    ; B2AbelianSummaryIsCanonical =
        refl
    ; B2SuppliesCKMMixing =
        false
    ; B2SuppliesCKMMixingIsFalse =
        refl
    ; B3IsFirstNonAbelianBraidGroup =
        true
    ; B3IsFirstNonAbelianBraidGroupIsTrue =
        refl
    ; B3FirstNonAbelianSummary =
        B3FirstNonAbelianStatement
    ; B3FirstNonAbelianSummaryIsCanonical =
        refl
    ; originRoles =
        canonicalOriginRoles
    ; originRolesAreCanonical =
        refl
    ; finiteSymmetryRelations =
        canonicalFiniteSymmetryRelations
    ; finiteSymmetryRelationsAreCanonical =
        refl
    ; KleinQuarticPSL2F7Order =
        168
    ; KleinQuarticPSL2F7OrderIs168 =
        refl
    ; KleinQuarticRelationSummary =
        KleinQuarticRelationStatement
    ; KleinQuarticRelationSummaryIsCanonical =
        refl
    ; LogicTlureyRelations =
        canonicalLogicTlureyRelations
    ; LogicTlureyRelationsAreCanonical =
        refl
    ; LogicTlureyJoinValue =
        LT.combineStage LT.resonance LT.resonance
    ; LogicTlureyJoinValueIsTriMid =
        refl
    ; LogicTlureyResonanceJoinProof =
        LT.resonance-combine
    ; LogicTlureyJoinSummary =
        LogicTlureyJoinStatement
    ; LogicTlureyJoinSummaryIsCanonical =
        refl
    ; DHRTheoremPromoted =
        false
    ; DHRTheoremPromotedIsFalse =
        refl
    ; CKMPromoted =
        false
    ; CKMPromotedIsFalse =
        refl
    ; YangMillsPromoted =
        false
    ; YangMillsPromotedIsFalse =
        refl
    ; ClayPromoted =
        false
    ; ClayPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        boundaryStatement
    ; receiptBoundaryIsCanonical =
        refl
    }

originRemarkStatusIsNotNewMathematics :
  status canonicalDHRBraidGroupOriginRemark
  ≡
  originRemark_notNewMathematics
originRemarkStatusIsNotNewMathematics =
  refl

B3PresentationRecordedAsYangBaxterDHRHexagonOrigin :
  braidRelationIsDHRHexagonOrigin canonicalDHRBraidGroupOriginRemark
  ≡
  true
B3PresentationRecordedAsYangBaxterDHRHexagonOrigin =
  refl

B2AbelianGivesNoCKMMixingRecorded :
  B2SuppliesCKMMixing canonicalDHRBraidGroupOriginRemark
  ≡
  false
B2AbelianGivesNoCKMMixingRecorded =
  refl

B3FirstNonAbelianBraidGroupRecorded :
  B3IsFirstNonAbelianBraidGroup canonicalDHRBraidGroupOriginRemark
  ≡
  true
B3FirstNonAbelianBraidGroupRecorded =
  refl

LogicTlureyResonanceResonanceJoinIsTriMid :
  LT.combineStage LT.resonance LT.resonance
  ≡
  tri-mid
LogicTlureyResonanceResonanceJoinIsTriMid =
  LT.resonance-combine

originRemarkKeepsDHRCKMYMClayFalse :
  DHRTheoremPromoted canonicalDHRBraidGroupOriginRemark
  ≡
  false
originRemarkKeepsDHRCKMYMClayFalse =
  refl
