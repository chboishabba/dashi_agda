module DASHI.Interop.InspectionRelativeNoTypedMeet where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawResidualLattice as Residual

NO_TYPED_MEET :
  Residual.ResidualLevel
NO_TYPED_MEET =
  Residual.noTypedMeet

------------------------------------------------------------------------
-- NO_TYPED_MEET inspection boundary.
--
-- This module is a receipt surface.  It records that a visible
-- NO_TYPED_MEET result is relative to the current inspection level and is not
-- an eternal/global impossibility theorem.  Deeper parsing, explicit bridge
-- admission, or a new role assignment may revise the comparison surface, but
-- none of those options promotes truth, support, admissibility, or authority.

data InspectionLevel : Set where
  currentStructuralInspection :
    InspectionLevel

  deeperParseInspection :
    InspectionLevel

  bridgeAwareInspection :
    InspectionLevel

  newRoleAssignmentInspection :
    InspectionLevel

data RevisionRoute : Set where
  deeperParseRoute :
    RevisionRoute

  explicitBridgeRoute :
    RevisionRoute

  newRoleAssignmentRoute :
    RevisionRoute

inspectionCanReviseNoTypedMeet :
  InspectionLevel →
  Bool
inspectionCanReviseNoTypedMeet currentStructuralInspection =
  false
inspectionCanReviseNoTypedMeet deeperParseInspection =
  true
inspectionCanReviseNoTypedMeet bridgeAwareInspection =
  true
inspectionCanReviseNoTypedMeet newRoleAssignmentInspection =
  true

record TransformAdmitted : Set where
  constructor transformAdmitted
  field
    transformLevel :
      InspectionLevel

    transformRoute :
      RevisionRoute

    transformAdmittedFlag :
      Bool

    transformAdmittedFlagIsTrue :
      transformAdmittedFlag ≡ true

    transformMayReviseNoTypedMeet :
      Bool

    transformMayReviseNoTypedMeetIsTrue :
      transformMayReviseNoTypedMeet ≡ true

    transformPromotesTruth :
      Bool

    transformPromotesTruthIsFalse :
      transformPromotesTruth ≡ false

    transformPromotesSupport :
      Bool

    transformPromotesSupportIsFalse :
      transformPromotesSupport ≡ false

    transformPromotesAdmissibility :
      Bool

    transformPromotesAdmissibilityIsFalse :
      transformPromotesAdmissibility ≡ false

record BridgeAdmitted : Set where
  constructor bridgeAdmitted
  field
    bridgeLevel :
      InspectionLevel

    bridgeRoute :
      RevisionRoute

    bridgeAdmittedFlag :
      Bool

    bridgeAdmittedFlagIsTrue :
      bridgeAdmittedFlag ≡ true

    bridgeMayReviseNoTypedMeet :
      Bool

    bridgeMayReviseNoTypedMeetIsTrue :
      bridgeMayReviseNoTypedMeet ≡ true

    bridgePromotesTruth :
      Bool

    bridgePromotesTruthIsFalse :
      bridgePromotesTruth ≡ false

    bridgePromotesSupport :
      Bool

    bridgePromotesSupportIsFalse :
      bridgePromotesSupport ≡ false

    bridgePromotesAdmissibility :
      Bool

    bridgePromotesAdmissibilityIsFalse :
      bridgePromotesAdmissibility ≡ false

record GlobalNoTypedMeetClaim : Set where
  constructor globalNoTypedMeetClaim
  field
    globalClaimLabel :
      String

    blockedFlag :
      Bool

    blockedFlagIsTrue :
      blockedFlag ≡ true

    globalImpossibilityPromoted :
      Bool

    globalImpossibilityPromotedIsFalse :
      globalImpossibilityPromoted ≡ false

    permanentIncommensurabilityPromoted :
      Bool

    permanentIncommensurabilityPromotedIsFalse :
      permanentIncommensurabilityPromoted ≡ false

    supportPromotedFromGlobalClaim :
      Bool

    supportPromotedFromGlobalClaimIsFalse :
      supportPromotedFromGlobalClaim ≡ false

    admissibilityPromotedFromGlobalClaim :
      Bool

    admissibilityPromotedFromGlobalClaimIsFalse :
      admissibilityPromotedFromGlobalClaim ≡ false

    truthPromotedFromGlobalClaim :
      Bool

    truthPromotedFromGlobalClaimIsFalse :
      truthPromotedFromGlobalClaim ≡ false

sameSignatureAtCurrentInspection :
  Residual.PredicatePNF →
  Residual.PredicatePNF →
  Bool
sameSignatureAtCurrentInspection left right =
  Residual.sameStructuralSignature
    (Residual.PredicatePNF.structuralSignature left)
    (Residual.PredicatePNF.structuralSignature right)

structuralMismatchAtCurrentInspection :
  Residual.PredicatePNF →
  Residual.PredicatePNF →
  Bool
structuralMismatchAtCurrentInspection left right with
  sameSignatureAtCurrentInspection left right
... | true =
  false
... | false =
  true

record NoTypedMeetAtInspection : Set where
  constructor noTypedMeetAtInspection
  field
    inspectionLevel :
      InspectionLevel

    leftReceipt :
      Residual.PNFEmissionReceipt

    rightReceipt :
      Residual.PNFEmissionReceipt

    leftAtom :
      Residual.PredicatePNF

    rightAtom :
      Residual.PredicatePNF

    leftAtomFromReceipt :
      leftAtom
      ≡
      Residual.PNFEmissionReceipt.emittedAtom leftReceipt

    rightAtomFromReceipt :
      rightAtom
      ≡
      Residual.PNFEmissionReceipt.emittedAtom rightReceipt

    currentSameStructuralSignature :
      Bool

    currentSameStructuralSignatureIsFalse :
      currentSameStructuralSignature ≡ false

    currentStructuralSignatureMismatch :
      Bool

    currentStructuralSignatureMismatchIsTrue :
      currentStructuralSignatureMismatch ≡ true

    residualAtInspection :
      Residual.ResidualLevel

    residualAtInspectionFromReceipts :
      residualAtInspection
      ≡
      Residual.receiptResidual leftReceipt rightReceipt

    residualAtInspectionIsNoTypedMeet :
      residualAtInspection ≡ NO_TYPED_MEET

    globalClaim :
      GlobalNoTypedMeetClaim

    globalClaimBlocked :
      GlobalNoTypedMeetClaim.blockedFlag globalClaim ≡ true

    deeperParseTransform :
      TransformAdmitted

    bridgeAdmission :
      BridgeAdmitted

    roleAssignmentTransform :
      TransformAdmitted

    revisableUnderDeeperParse :
      Bool

    revisableUnderDeeperParseIsTrue :
      revisableUnderDeeperParse ≡ true

    revisableUnderBridge :
      Bool

    revisableUnderBridgeIsTrue :
      revisableUnderBridge ≡ true

    revisableUnderNewRoleAssignment :
      Bool

    revisableUnderNewRoleAssignmentIsTrue :
      revisableUnderNewRoleAssignment ≡ true

    truthPromotion :
      Bool

    truthPromotionIsFalse :
      truthPromotion ≡ false

    supportPromotion :
      Bool

    supportPromotionIsFalse :
      supportPromotion ≡ false

    admissibilityPromotion :
      Bool

    admissibilityPromotionIsFalse :
      admissibilityPromotion ≡ false

------------------------------------------------------------------------
-- Canonical current-inspection example.

canonicalCurrentLeftPredicate :
  Residual.PredicatePNF
canonicalCurrentLeftPredicate =
  Residual.predicatePNF
    "canonical structural source"
    Residual.sig-agent-theme
    (Residual.opaqueArg "agent")
    (Residual.opaqueArg "theme")
    Residual.absent
    Residual.positive
    Residual.directEvidence
    "current-inspection-left"

canonicalCurrentRightPredicate :
  Residual.PredicatePNF
canonicalCurrentRightPredicate =
  Residual.predicatePNF
    "canonical structural source"
    Residual.sig-agent-goal
    (Residual.opaqueArg "agent")
    Residual.absent
    (Residual.opaqueArg "goal")
    Residual.positive
    Residual.directEvidence
    "current-inspection-right"

canonicalCurrentLeftReceipt :
  Residual.PNFEmissionReceipt
canonicalCurrentLeftReceipt =
  Residual.pnfEmissionReceipt
    "current-structural-parser"
    "current-structural-reducer"
    "agent theme surface"
    canonicalCurrentLeftPredicate

canonicalCurrentRightReceipt :
  Residual.PNFEmissionReceipt
canonicalCurrentRightReceipt =
  Residual.pnfEmissionReceipt
    "current-structural-parser"
    "current-structural-reducer"
    "agent goal surface"
    canonicalCurrentRightPredicate

canonicalCurrentSameStructuralSignatureIsFalse :
  sameSignatureAtCurrentInspection
    canonicalCurrentLeftPredicate
    canonicalCurrentRightPredicate
  ≡
  false
canonicalCurrentSameStructuralSignatureIsFalse =
  refl

canonicalCurrentStructuralMismatchIsTrue :
  structuralMismatchAtCurrentInspection
    canonicalCurrentLeftPredicate
    canonicalCurrentRightPredicate
  ≡
  true
canonicalCurrentStructuralMismatchIsTrue =
  refl

canonicalCurrentReceiptResidualIsNoTypedMeet :
  Residual.receiptResidual
    canonicalCurrentLeftReceipt
    canonicalCurrentRightReceipt
  ≡
  NO_TYPED_MEET
canonicalCurrentReceiptResidualIsNoTypedMeet =
  refl

canonicalRevisionRoutes :
  List RevisionRoute
canonicalRevisionRoutes =
  deeperParseRoute
  ∷ explicitBridgeRoute
  ∷ newRoleAssignmentRoute
  ∷ []

canonicalDeeperParseTransformAdmitted :
  TransformAdmitted
canonicalDeeperParseTransformAdmitted =
  transformAdmitted
    deeperParseInspection
    deeperParseRoute
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl

canonicalBridgeAdmitted :
  BridgeAdmitted
canonicalBridgeAdmitted =
  bridgeAdmitted
    bridgeAwareInspection
    explicitBridgeRoute
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl

canonicalRoleAssignmentTransformAdmitted :
  TransformAdmitted
canonicalRoleAssignmentTransformAdmitted =
  transformAdmitted
    newRoleAssignmentInspection
    newRoleAssignmentRoute
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl

canonicalGlobalNoTypedMeetClaim :
  GlobalNoTypedMeetClaim
canonicalGlobalNoTypedMeetClaim =
  globalNoTypedMeetClaim
    "NO_TYPED_MEET is eternal/global"
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

canonicalNoTypedMeetAtCurrentInspection :
  NoTypedMeetAtInspection
canonicalNoTypedMeetAtCurrentInspection =
  noTypedMeetAtInspection
    currentStructuralInspection
    canonicalCurrentLeftReceipt
    canonicalCurrentRightReceipt
    canonicalCurrentLeftPredicate
    canonicalCurrentRightPredicate
    refl
    refl
    (sameSignatureAtCurrentInspection
      canonicalCurrentLeftPredicate
      canonicalCurrentRightPredicate)
    refl
    (structuralMismatchAtCurrentInspection
      canonicalCurrentLeftPredicate
      canonicalCurrentRightPredicate)
    refl
    (Residual.receiptResidual
      canonicalCurrentLeftReceipt
      canonicalCurrentRightReceipt)
    refl
    refl
    canonicalGlobalNoTypedMeetClaim
    refl
    canonicalDeeperParseTransformAdmitted
    canonicalBridgeAdmitted
    canonicalRoleAssignmentTransformAdmitted
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- False promotion/globalization lemmas.  Each is intentionally by refl:
-- the receipt stores these gates as closed booleans, not as assumed
-- impossibility theorems.

noTypedMeetAtCurrentInspectionNoGlobalImpossibility :
  GlobalNoTypedMeetClaim.globalImpossibilityPromoted
    canonicalGlobalNoTypedMeetClaim
  ≡
  false
noTypedMeetAtCurrentInspectionNoGlobalImpossibility =
  refl

noTypedMeetAtCurrentInspectionNoPermanentIncommensurability :
  GlobalNoTypedMeetClaim.permanentIncommensurabilityPromoted
    canonicalGlobalNoTypedMeetClaim
  ≡
  false
noTypedMeetAtCurrentInspectionNoPermanentIncommensurability =
  refl

noTypedMeetAtCurrentInspectionNoSupportPromotion :
  NoTypedMeetAtInspection.supportPromotion
    canonicalNoTypedMeetAtCurrentInspection
  ≡
  false
noTypedMeetAtCurrentInspectionNoSupportPromotion =
  refl

noTypedMeetAtCurrentInspectionNoAdmissibilityPromotion :
  NoTypedMeetAtInspection.admissibilityPromotion
    canonicalNoTypedMeetAtCurrentInspection
  ≡
  false
noTypedMeetAtCurrentInspectionNoAdmissibilityPromotion =
  refl

noTypedMeetAtCurrentInspectionNoTruthPromotion :
  NoTypedMeetAtInspection.truthPromotion
    canonicalNoTypedMeetAtCurrentInspection
  ≡
  false
noTypedMeetAtCurrentInspectionNoTruthPromotion =
  refl

noTypedMeetAtCurrentInspectionMayReviseByDeeperParse :
  NoTypedMeetAtInspection.revisableUnderDeeperParse
    canonicalNoTypedMeetAtCurrentInspection
  ≡
  true
noTypedMeetAtCurrentInspectionMayReviseByDeeperParse =
  refl

noTypedMeetAtCurrentInspectionMayReviseByBridge :
  NoTypedMeetAtInspection.revisableUnderBridge
    canonicalNoTypedMeetAtCurrentInspection
  ≡
  true
noTypedMeetAtCurrentInspectionMayReviseByBridge =
  refl

noTypedMeetAtCurrentInspectionMayReviseByNewRoleAssignment :
  NoTypedMeetAtInspection.revisableUnderNewRoleAssignment
    canonicalNoTypedMeetAtCurrentInspection
  ≡
  true
noTypedMeetAtCurrentInspectionMayReviseByNewRoleAssignment =
  refl
