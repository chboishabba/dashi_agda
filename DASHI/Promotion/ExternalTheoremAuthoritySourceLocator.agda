module DASHI.Promotion.ExternalTheoremAuthoritySourceLocator where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Algebra.StageQuotient as StageQuotient
import DASHI.Algebra.StageQuotientIrreversibilityBoundary as StageQuotientBoundary
import DASHI.Physics.Closure.CRTMonsterFixedPointCompactificationBoundary as CRTMonster

------------------------------------------------------------------------
-- External theorem/proof-authority source locator.
--
-- This module records where two promotion gates must look for external
-- theorem/proof authority.  The rows are locator requests only: they import
-- the checked boundary surfaces by module name, but they do not accept those
-- surfaces as external proofs and do not promote Monster/Moonshine or
-- Carnot/thermodynamic claims.

data ExternalTheoremAuthorityLane : Set where
  monsterMoonshineLane :
    ExternalTheoremAuthorityLane

  carnotThermodynamicLane :
    ExternalTheoremAuthorityLane

data ExternalAuthorityRequestKind : Set where
  externalTheoremAuthorityRequest :
    ExternalAuthorityRequestKind

  externalProofAuthorityRequest :
    ExternalAuthorityRequestKind

data SourceLocatorBoundaryAnchor : Set where
  crtMonsterFixedPointCompactificationBoundaryAnchor :
    SourceLocatorBoundaryAnchor

  stageQuotientIrreversibilityBoundaryAnchor :
    SourceLocatorBoundaryAnchor

record ExternalTheoremAuthoritySourceLocatorRow : Set where
  field
    lane :
      ExternalTheoremAuthorityLane

    requestKind :
      ExternalAuthorityRequestKind

    boundaryAnchor :
      SourceLocatorBoundaryAnchor

    sourceModuleName :
      String

    importedBoundaryName :
      String

    boundaryValueName :
      String

    externalAuthorityRequired :
      String

    consumerGate :
      String

    locatedAsExternalRequest :
      Bool

    locatedAsExternalRequestIsTrue :
      locatedAsExternalRequest ≡ true

    acceptedAsProof :
      Bool

    acceptedAsProofIsFalse :
      acceptedAsProof ≡ false

    promotionPreserved :
      Bool

    promotionPreservedIsFalse :
      promotionPreserved ≡ false

    importedBoundaryPromotionFlag :
      Bool

    importedBoundaryPromotionFlagIsFalse :
      importedBoundaryPromotionFlag ≡ false

    locatorNotes :
      List String

open ExternalTheoremAuthoritySourceLocatorRow public

mkFailClosedLocatorRow :
  ExternalTheoremAuthorityLane →
  ExternalAuthorityRequestKind →
  SourceLocatorBoundaryAnchor →
  String →
  String →
  String →
  String →
  String →
  (importedBoundaryPromotionFlag' : Bool) →
  importedBoundaryPromotionFlag' ≡ false →
  List String →
  ExternalTheoremAuthoritySourceLocatorRow
mkFailClosedLocatorRow
  lane'
  requestKind'
  boundaryAnchor'
  sourceModuleName'
  importedBoundaryName'
  boundaryValueName'
  externalAuthorityRequired'
  consumerGate'
  importedBoundaryPromotionFlag'
  importedBoundaryPromotionFlagIsFalse'
  locatorNotes' =
  record
    { lane =
        lane'
    ; requestKind =
        requestKind'
    ; boundaryAnchor =
        boundaryAnchor'
    ; sourceModuleName =
        sourceModuleName'
    ; importedBoundaryName =
        importedBoundaryName'
    ; boundaryValueName =
        boundaryValueName'
    ; externalAuthorityRequired =
        externalAuthorityRequired'
    ; consumerGate =
        consumerGate'
    ; locatedAsExternalRequest =
        true
    ; locatedAsExternalRequestIsTrue =
        refl
    ; acceptedAsProof =
        false
    ; acceptedAsProofIsFalse =
        refl
    ; promotionPreserved =
        false
    ; promotionPreservedIsFalse =
        refl
    ; importedBoundaryPromotionFlag =
        importedBoundaryPromotionFlag'
    ; importedBoundaryPromotionFlagIsFalse =
        importedBoundaryPromotionFlagIsFalse'
    ; locatorNotes =
        locatorNotes'
    }

stageQuotientSeamLocatorReference : StageQuotient.StageQuotientSeam
stageQuotientSeamLocatorReference =
  StageQuotient.stageQuotientSeamSurface

stageQuotientIrreversibilityLocatorReference :
  StageQuotientBoundary.StageQuotientIrreversibilityBoundary
stageQuotientIrreversibilityLocatorReference =
  StageQuotientBoundary.canonicalStageQuotientIrreversibilityBoundary

crtMonsterBoundaryLocatorReference :
  CRTMonster.CRTMonsterFixedPointCompactificationBoundaryReceipt
crtMonsterBoundaryLocatorReference =
  CRTMonster.canonicalCRTMonsterFixedPointCompactificationBoundaryReceipt

monsterMoonshineExternalAuthorityLocatorRow :
  ExternalTheoremAuthoritySourceLocatorRow
monsterMoonshineExternalAuthorityLocatorRow =
  mkFailClosedLocatorRow
    monsterMoonshineLane
    externalTheoremAuthorityRequest
    crtMonsterFixedPointCompactificationBoundaryAnchor
    "DASHI.Physics.Closure.CRTMonsterFixedPointCompactificationBoundary"
    "CRTMonsterFixedPointCompactificationBoundaryReceipt"
    "canonicalCRTMonsterFixedPointCompactificationBoundaryReceipt"
    "External theorem/proof authority for Monster/Moonshine theorem promotion"
    "Monster/Moonshine theorem authority gate"
    (CRTMonster.monsterTheoremPromoted
      crtMonsterBoundaryLocatorReference)
    CRTMonster.canonicalCRTMonsterTheoremPromotionFalse
    ( "Located at the CRT/Monster fixed-point compactification boundary as a request for external theorem authority"
    ∷ "The checked CRT/196884/Monster receipt is not accepted here as a Monster/Moonshine proof"
    ∷ "Monster theorem, surreal isomorphism, and terminal promotion remain false at the imported boundary"
    ∷ []
    )

carnotThermodynamicExternalAuthorityLocatorRow :
  ExternalTheoremAuthoritySourceLocatorRow
carnotThermodynamicExternalAuthorityLocatorRow =
  mkFailClosedLocatorRow
    carnotThermodynamicLane
    externalProofAuthorityRequest
    stageQuotientIrreversibilityBoundaryAnchor
    "DASHI.Algebra.StageQuotientIrreversibilityBoundary"
    "StageQuotientIrreversibilityBoundary"
    "canonicalStageQuotientIrreversibilityBoundary"
    "External theorem/proof authority for Carnot or thermodynamic theorem promotion"
    "Carnot/thermodynamic authority gate"
    (StageQuotientBoundary.StageQuotientIrreversibilityBoundary.thermodynamicCarnotPromotion
      stageQuotientIrreversibilityLocatorReference)
    (StageQuotientBoundary.StageQuotientIrreversibilityBoundary.thermodynamicCarnotPromotionIsFalse
      stageQuotientIrreversibilityLocatorReference)
    ( "Located at the StageQuotient irreversibility boundary as a request for external proof authority"
    ∷ "The Stage -> TriTruth quotient seam is an imported finite boundary, not a thermodynamic proof"
    ∷ "No thermodynamic Carnot theorem or physical Carnot theorem is promoted from the imported boundary"
    ∷ []
    )

canonicalExternalTheoremAuthoritySourceLocatorRows :
  List ExternalTheoremAuthoritySourceLocatorRow
canonicalExternalTheoremAuthoritySourceLocatorRows =
  monsterMoonshineExternalAuthorityLocatorRow
  ∷ carnotThermodynamicExternalAuthorityLocatorRow
  ∷ []

sourceLocatorRowCount :
  List ExternalTheoremAuthoritySourceLocatorRow →
  Nat
sourceLocatorRowCount [] =
  zero
sourceLocatorRowCount (_ ∷ xs) =
  suc (sourceLocatorRowCount xs)

canonicalSourceLocatorRowCountIs2 :
  sourceLocatorRowCount canonicalExternalTheoremAuthoritySourceLocatorRows
  ≡
  2
canonicalSourceLocatorRowCountIs2 =
  refl

monsterMoonshineLocatorAcceptedAsProofFalse :
  acceptedAsProof monsterMoonshineExternalAuthorityLocatorRow ≡ false
monsterMoonshineLocatorAcceptedAsProofFalse =
  refl

monsterMoonshineLocatorPromotionPreservedFalse :
  promotionPreserved monsterMoonshineExternalAuthorityLocatorRow ≡ false
monsterMoonshineLocatorPromotionPreservedFalse =
  refl

carnotThermodynamicLocatorAcceptedAsProofFalse :
  acceptedAsProof carnotThermodynamicExternalAuthorityLocatorRow ≡ false
carnotThermodynamicLocatorAcceptedAsProofFalse =
  refl

carnotThermodynamicLocatorPromotionPreservedFalse :
  promotionPreserved carnotThermodynamicExternalAuthorityLocatorRow ≡ false
carnotThermodynamicLocatorPromotionPreservedFalse =
  refl
