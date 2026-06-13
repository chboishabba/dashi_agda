module DASHI.Physics.Closure.YMActualPolymerActivityCandidateReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Paper3YMDependencyGraphReceipt as Graph
import DASHI.Physics.Closure.YMActualPolymerActivityDefinitionReceipt as Definition
import DASHI.Physics.Closure.YMBalabanRGScaleTransferFrontierReceipt as Balaban

------------------------------------------------------------------------
-- YM5 actual polymer-activity candidate receipt.
--
-- This file records the candidate surface for the actual polymer-activity
-- lane.  It is intentionally fail-closed: the YM5 bridge is named, the
-- dependency list is explicit, the open consequences are listed, and no
-- promotion to continuum or Clay status is constructed here.

data YMActualPolymerActivityCandidateStatus : Set where
  candidateRecordedNoPromotion :
    YMActualPolymerActivityCandidateStatus

data YMActualPolymerActivityCandidateDependency : Set where
  ym5DefinitionFrontierImported :
    YMActualPolymerActivityCandidateDependency

  paper3DependencyGraphStillOpen :
    YMActualPolymerActivityCandidateDependency

  balabanRGScaleTransferStillRequired :
    YMActualPolymerActivityCandidateDependency

  actualPolymerActivityBridgeExplicit :
    YMActualPolymerActivityCandidateDependency

  promotionBoundaryFailClosed :
    YMActualPolymerActivityCandidateDependency

canonicalYMActualPolymerActivityCandidateDependencies :
  List YMActualPolymerActivityCandidateDependency
canonicalYMActualPolymerActivityCandidateDependencies =
  ym5DefinitionFrontierImported
  ∷ paper3DependencyGraphStillOpen
  ∷ balabanRGScaleTransferStillRequired
  ∷ actualPolymerActivityBridgeExplicit
  ∷ promotionBoundaryFailClosed
  ∷ []

data YMActualPolymerActivityCandidateConsequence : Set where
  candidateSurfaceRecorded :
    YMActualPolymerActivityCandidateConsequence

  actualPolymerActivityRemainsMissing :
    YMActualPolymerActivityCandidateConsequence

  downstreamYM5BridgeStaysOpen :
    YMActualPolymerActivityCandidateConsequence

  continuumPromotionStaysClosed :
    YMActualPolymerActivityCandidateConsequence

  clayPromotionStaysClosed :
    YMActualPolymerActivityCandidateConsequence

canonicalYMActualPolymerActivityCandidateConsequences :
  List YMActualPolymerActivityCandidateConsequence
canonicalYMActualPolymerActivityCandidateConsequences =
  candidateSurfaceRecorded
  ∷ actualPolymerActivityRemainsMissing
  ∷ downstreamYM5BridgeStaysOpen
  ∷ continuumPromotionStaysClosed
  ∷ clayPromotionStaysClosed
  ∷ []

data YMActualPolymerActivityCandidateNonClaim : Set where
  noActualPolymerActivityTheorem :
    YMActualPolymerActivityCandidateNonClaim

  noBalabanRGClosure :
    YMActualPolymerActivityCandidateNonClaim

  noContinuumYangMillsConstruction :
    YMActualPolymerActivityCandidateNonClaim

  noClayYangMillsPromotion :
    YMActualPolymerActivityCandidateNonClaim

  noPromotionTokenIssued :
    YMActualPolymerActivityCandidateNonClaim

canonicalYMActualPolymerActivityCandidateNonClaims :
  List YMActualPolymerActivityCandidateNonClaim
canonicalYMActualPolymerActivityCandidateNonClaims =
  noActualPolymerActivityTheorem
  ∷ noBalabanRGClosure
  ∷ noContinuumYangMillsConstruction
  ∷ noClayYangMillsPromotion
  ∷ noPromotionTokenIssued
  ∷ []

data YMActualPolymerActivityCandidatePromotion : Set where

ymActualPolymerActivityCandidatePromotionImpossibleHere :
  YMActualPolymerActivityCandidatePromotion →
  ⊥
ymActualPolymerActivityCandidatePromotionImpossibleHere ()

candidateStatement : String
candidateStatement =
  "YM5 candidate receipt: the actual polymer-activity bridge is recorded as an open YM frontier, not a theorem; the same-prime definition receipt, the Paper 3 dependency graph, and the Balaban scale-transfer frontier remain explicit inputs, while continuum and Clay promotion stay closed."

candidatePromotionBoundary : String
candidatePromotionBoundary =
  "Fail-closed boundary: this receipt stops at recording the YM5 candidate surface and its missing bridge. It does not construct actual polymer activity, Balaban RG closure, continuum Yang-Mills promotion, or Clay promotion."

canonicalCandidateBoundaryNotes : List String
canonicalCandidateBoundaryNotes =
  "YM5 is a candidate surface, not a closure theorem"
  ∷ "The immediate missing bridge is no longer polymer-activity supply itself; it is downstream Balaban/continuum consumption"
  ∷ "Paper 3 remains open at the YM5 node, so the downstream graph is not promoted"
  ∷ "Balaban scale transfer remains required and is not collapsed here"
  ∷ "Continuum and Clay promotion stay explicitly false"
  ∷ []

record YMActualPolymerActivityCandidateReceipt : Setω where
  field
    status :
      YMActualPolymerActivityCandidateStatus

    statusIsCanonical :
      status ≡ candidateRecordedNoPromotion

    definitionReceipt :
      Definition.YMActualPolymerActivityDefinitionReceipt

    definitionReceiptRecordsActivityTrue :
      Definition.actualPolymerActivitySupplied definitionReceipt ≡ true

    paper3DependencyGraphReceipt :
      Graph.Paper3YMDependencyGraphReceipt

    paper3DependencyGraphKeepsYM5Open :
      Graph.ym5ActualPolymerActivitySupplied paper3DependencyGraphReceipt ≡ false

    balabanFrontierReceipt :
      Balaban.YMBalabanRGScaleTransferFrontierReceipt

    balabanFrontierStillRequiresBridge :
      Balaban.bridgeVerdict balabanFrontierReceipt ≡ Balaban.nonperturbativeBridgeRequired

    dependencies :
      List YMActualPolymerActivityCandidateDependency

    dependenciesAreCanonical :
      dependencies ≡ canonicalYMActualPolymerActivityCandidateDependencies

    consequences :
      List YMActualPolymerActivityCandidateConsequence

    consequencesAreCanonical :
      consequences ≡ canonicalYMActualPolymerActivityCandidateConsequences

    nonClaims :
      List YMActualPolymerActivityCandidateNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMActualPolymerActivityCandidateNonClaims

    candidateRecorded :
      Bool

    candidateRecordedIsTrue :
      candidateRecorded ≡ true

    immediateMissingBridge :
      Bool

    immediateMissingBridgeIsTrue :
      immediateMissingBridge ≡ true

    promotionImpossible :
      Bool

    promotionImpossibleIsTrue :
      promotionImpossible ≡ true

    continuumYangMillsPromoted :
      Bool

    continuumYangMillsPromotedIsFalse :
      continuumYangMillsPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ candidateStatement

    promotionBoundary :
      String

    promotionBoundaryIsCanonical :
      promotionBoundary ≡ candidatePromotionBoundary

    boundaryNotes :
      List String

    boundaryNotesAreCanonical :
      boundaryNotes ≡ canonicalCandidateBoundaryNotes

open YMActualPolymerActivityCandidateReceipt public

canonicalYMActualPolymerActivityCandidateReceipt :
  YMActualPolymerActivityCandidateReceipt
canonicalYMActualPolymerActivityCandidateReceipt =
  record
    { status =
        candidateRecordedNoPromotion
    ; statusIsCanonical =
        refl
    ; definitionReceipt =
        Definition.canonicalYMActualPolymerActivityDefinitionReceipt
    ; definitionReceiptRecordsActivityTrue =
        refl
    ; paper3DependencyGraphReceipt =
        Graph.canonicalPaper3YMDependencyGraphReceipt
    ; paper3DependencyGraphKeepsYM5Open =
        refl
    ; balabanFrontierReceipt =
        Balaban.canonicalYMBalabanRGScaleTransferFrontierReceipt
    ; balabanFrontierStillRequiresBridge =
        refl
    ; dependencies =
        canonicalYMActualPolymerActivityCandidateDependencies
    ; dependenciesAreCanonical =
        refl
    ; consequences =
        canonicalYMActualPolymerActivityCandidateConsequences
    ; consequencesAreCanonical =
        refl
    ; nonClaims =
        canonicalYMActualPolymerActivityCandidateNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; candidateRecorded =
        true
    ; candidateRecordedIsTrue =
        refl
    ; immediateMissingBridge =
        true
    ; immediateMissingBridgeIsTrue =
        refl
    ; promotionImpossible =
        true
    ; promotionImpossibleIsTrue =
        refl
    ; continuumYangMillsPromoted =
        false
    ; continuumYangMillsPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; statement =
        candidateStatement
    ; statementIsCanonical =
        refl
    ; promotionBoundary =
        candidatePromotionBoundary
    ; promotionBoundaryIsCanonical =
        refl
    ; boundaryNotes =
        canonicalCandidateBoundaryNotes
    ; boundaryNotesAreCanonical =
        refl
    }

canonicalYMActualPolymerActivityCandidatePromotionImpossible :
  YMActualPolymerActivityCandidatePromotion →
  ⊥
canonicalYMActualPolymerActivityCandidatePromotionImpossible =
  ymActualPolymerActivityCandidatePromotionImpossibleHere
