module DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Balaban/Odusanya Yang-Mills mass-gap receipt intake.
--
-- This module records two separate receipts: external Yang-Mills mass-gap
-- authority intake, and the DASHI-internal ST3 depth-recursion/Banach receipt.
-- The local receipt is finite-depth/finite-carrier only, while continuum,
-- Clay, journal, community, and terminal promotion remain explicitly false.

data BalabanRGMassGapStatus : Set where
  externalClaimUnderReviewNoDASHIPromotion :
    BalabanRGMassGapStatus

  finiteDepthPromotedContinuumOpen :
    BalabanRGMassGapStatus

  dashiInternalContinuumClosedClayReviewPending :
    BalabanRGMassGapStatus

  verifiedFiniteCarrierOnlyContinuumClayOpen :
    BalabanRGMassGapStatus

data ClayOfficialUnsolvedStatus : Set where
  clayOfficialUnsolvedStatus :
    ClayOfficialUnsolvedStatus

data OdusanyaClaimSeparateSubmission : Set where
  odusanyaClaimSeparateSubmission :
    OdusanyaClaimSeparateSubmission

data ZenodoDissolutionAlternative : Set where
  zenodoDissolutionAlternative :
    ZenodoDissolutionAlternative

data VerifiedMassGapAuthoritySourceStatus : Set where
  cambridgeOpenEngageWorkingPreprintUnderReview :
    VerifiedMassGapAuthoritySourceStatus

  zenodoDissolutionAlternativeFiniteDiscreteLatticeCampaign :
    VerifiedMassGapAuthoritySourceStatus

data YangMillsMassGapClaimStage : Set where
  latticeTransferMatrixGap :
    YangMillsMassGapClaimStage

  balabanMultiscaleRGInduction :
    YangMillsMassGapClaimStage

  osterwalderSchraderReconstruction :
    YangMillsMassGapClaimStage

  compactSimpleGroupExtension :
    YangMillsMassGapClaimStage

  machineVerificationIntake :
    YangMillsMassGapClaimStage

canonicalYangMillsMassGapClaimStages :
  List YangMillsMassGapClaimStage
canonicalYangMillsMassGapClaimStages =
  latticeTransferMatrixGap
  ∷ balabanMultiscaleRGInduction
  ∷ osterwalderSchraderReconstruction
  ∷ compactSimpleGroupExtension
  ∷ machineVerificationIntake
  ∷ []

data BalabanRGMassGapOpenObligation : Set where
  missingPeerReviewOrClayAcceptance :
    BalabanRGMassGapOpenObligation

  missingLocalKernelImport :
    BalabanRGMassGapOpenObligation

  missingDASHIWilsonPlaquetteBinding :
    BalabanRGMassGapOpenObligation

  missingOSReconstructionAuthority :
    BalabanRGMassGapOpenObligation

  missingCompactSimpleGroupCoverageAuthority :
    BalabanRGMassGapOpenObligation

canonicalBalabanRGMassGapOpenObligations :
  List BalabanRGMassGapOpenObligation
canonicalBalabanRGMassGapOpenObligations =
  missingPeerReviewOrClayAcceptance
  ∷ missingLocalKernelImport
  ∷ missingDASHIWilsonPlaquetteBinding
  ∷ missingOSReconstructionAuthority
  ∷ missingCompactSimpleGroupCoverageAuthority
  ∷ []

data BalabanRGMassGapPromotionAuthorityToken : Set where

data MassGapProofLineage : Set where
  OdusanyaBalabanRG :
    MassGapProofLineage

  AgawaHolonomyNonlocalRG :
    MassGapProofLineage

  DissolutionCampaign :
    MassGapProofLineage

  DASHIProObjectMassGap :
    MassGapProofLineage

canonicalMassGapProofLineages :
  List MassGapProofLineage
canonicalMassGapProofLineages =
  OdusanyaBalabanRG
  ∷ AgawaHolonomyNonlocalRG
  ∷ DissolutionCampaign
  ∷ DASHIProObjectMassGap
  ∷ []

data CandidateMassGapDisproof : Set where
  gribovObstruction :
    CandidateMassGapDisproof

  irSlavery :
    CandidateMassGapDisproof

  masslessGluonScaling :
    CandidateMassGapDisproof

canonicalCandidateMassGapDisproofs :
  List CandidateMassGapDisproof
canonicalCandidateMassGapDisproofs =
  gribovObstruction
  ∷ irSlavery
  ∷ masslessGluonScaling
  ∷ []

record FiniteDepthLatticeGapReceipt (depth : Nat) : Setω where
  field
    latticeDepth :
      Nat

    latticeDepth-v :
      latticeDepth
      ≡
      depth

    receiptKind :
      String

    receiptKind-v :
      receiptKind
      ≡
      "finite-depth-lattice-transfer-matrix-gap"

    gapCarrierShape :
      String

    gapCarrierShape-v :
      gapCarrierShape
      ≡
      "positive-gap-for-fixed-lattice-depth-before-continuum-limit"

    promotedAtThisDepth :
      Bool

    promotedAtThisDepthIsTrue :
      promotedAtThisDepth ≡ true

    notClayContinuumTheorem :
      Bool

    notClayContinuumTheoremIsTrue :
      notClayContinuumTheorem ≡ true

open FiniteDepthLatticeGapReceipt public

finiteDepthLatticeGapReceipt :
  (depth : Nat) →
  FiniteDepthLatticeGapReceipt depth
finiteDepthLatticeGapReceipt depth =
  record
    { latticeDepth =
        depth
    ; latticeDepth-v =
        refl
    ; receiptKind =
        "finite-depth-lattice-transfer-matrix-gap"
    ; receiptKind-v =
        refl
    ; gapCarrierShape =
        "positive-gap-for-fixed-lattice-depth-before-continuum-limit"
    ; gapCarrierShape-v =
        refl
    ; promotedAtThisDepth =
        true
    ; promotedAtThisDepthIsTrue =
        refl
    ; notClayContinuumTheorem =
        true
    ; notClayContinuumTheoremIsTrue =
        refl
    }

record FiniteDepthLatticeGapProObjectReceipt : Setω where
  field
    receiptAtEveryDepth :
      (depth : Nat) →
      FiniteDepthLatticeGapReceipt depth

    proObjectShape :
      String

    proObjectShape-v :
      proObjectShape
      ≡
      "depth-indexed-pro-object-family-of-finite-lattice-gap-receipts"

    depthIndexedPromoted :
      Bool

    depthIndexedPromotedIsTrue :
      depthIndexedPromoted ≡ true

    continuumLimitPromoted :
      Bool

    continuumLimitPromotedIsFalse :
      continuumLimitPromoted ≡ false

open FiniteDepthLatticeGapProObjectReceipt public

canonicalFiniteDepthLatticeGapProObjectReceipt :
  FiniteDepthLatticeGapProObjectReceipt
canonicalFiniteDepthLatticeGapProObjectReceipt =
  record
    { receiptAtEveryDepth =
        finiteDepthLatticeGapReceipt
    ; proObjectShape =
        "depth-indexed-pro-object-family-of-finite-lattice-gap-receipts"
    ; proObjectShape-v =
        refl
    ; depthIndexedPromoted =
        true
    ; depthIndexedPromotedIsTrue =
        refl
    ; continuumLimitPromoted =
        false
    ; continuumLimitPromotedIsFalse =
        refl
    }

record BalabanMasterBoundObligation : Setω where
  field
    obligationName :
      String

    obligationName-v :
      obligationName
      ≡
      "external-Balaban-master-bound-with-uniform-continuum-control"

    requiredForClayContinuumMassGap :
      Bool

    requiredForClayContinuumMassGapIsTrue :
      requiredForClayContinuumMassGap ≡ true

    suppliedInDASHI :
      Bool

    suppliedInDASHIIsFalse :
      suppliedInDASHI ≡ false

    odusanyaAcceptanceRequired :
      Bool

    odusanyaAcceptanceRequiredIsTrue :
      odusanyaAcceptanceRequired ≡ true

open BalabanMasterBoundObligation public

canonicalBalabanMasterBoundObligation :
  BalabanMasterBoundObligation
canonicalBalabanMasterBoundObligation =
  record
    { obligationName =
        "external-Balaban-master-bound-with-uniform-continuum-control"
    ; obligationName-v =
        refl
    ; requiredForClayContinuumMassGap =
        true
    ; requiredForClayContinuumMassGapIsTrue =
        refl
    ; suppliedInDASHI =
        false
    ; suppliedInDASHIIsFalse =
        refl
    ; odusanyaAcceptanceRequired =
        true
    ; odusanyaAcceptanceRequiredIsTrue =
        refl
    }

record ContinuumMassGapFromBalabanMasterBound : Setω where
  field
    clayStatus :
      ClayOfficialUnsolvedStatus

    odusanyaSubmission :
      OdusanyaClaimSeparateSubmission

    zenodoAlternative :
      ZenodoDissolutionAlternative

    masterBoundObligation :
      BalabanMasterBoundObligation

    continuumClaimShape :
      String

    continuumClaimShape-v :
      continuumClaimShape
      ≡
      "continuum-Clay-Yang-Mills-mass-gap-from-external-Balaban-master-bound"

    promotedAsClayTheorem :
      Bool

    promotedAsClayTheoremIsFalse :
      promotedAsClayTheorem ≡ false

    usableAsTerminalTheorem :
      Bool

    usableAsTerminalTheoremIsFalse :
      usableAsTerminalTheorem ≡ false

open ContinuumMassGapFromBalabanMasterBound public

continuumMassGapFromBalabanMasterBound :
  ContinuumMassGapFromBalabanMasterBound
continuumMassGapFromBalabanMasterBound =
  record
    { clayStatus =
        clayOfficialUnsolvedStatus
    ; odusanyaSubmission =
        odusanyaClaimSeparateSubmission
    ; zenodoAlternative =
        zenodoDissolutionAlternative
    ; masterBoundObligation =
        canonicalBalabanMasterBoundObligation
    ; continuumClaimShape =
        "continuum-Clay-Yang-Mills-mass-gap-from-external-Balaban-master-bound"
    ; continuumClaimShape-v =
        refl
    ; promotedAsClayTheorem =
        false
    ; promotedAsClayTheoremIsFalse =
        refl
    ; usableAsTerminalTheorem =
        false
    ; usableAsTerminalTheoremIsFalse =
        refl
    }

data MassGapQuantifierExchangePoint : Set where
  pointwiseDepthGap :
    MassGapQuantifierExchangePoint

  uniformContinuumGap :
    MassGapQuantifierExchangePoint

canonicalMassGapQuantifierExchangePoints :
  List MassGapQuantifierExchangePoint
canonicalMassGapQuantifierExchangePoints =
  pointwiseDepthGap
  ∷ uniformContinuumGap
  ∷ []

record MassGapQuantifierExchangeReceipt : Setω where
  field
    exchangePoints :
      List MassGapQuantifierExchangePoint

    exchangePointsAreCanonical :
      exchangePoints
      ≡
      canonicalMassGapQuantifierExchangePoints

    pointwiseDepthGapShape :
      String

    pointwiseDepthGapShape-v :
      pointwiseDepthGapShape
      ≡
      "pointwise-depth-gap-forall-d-Delta-d-positive"

    uniformContinuumGapShape :
      String

    uniformContinuumGapShape-v :
      uniformContinuumGapShape
      ≡
      "uniform-continuum-gap-exists-epsilon-forall-d-Delta-d-at-least-epsilon"

    pointwiseFiniteDepthPromoted :
      Bool

    pointwiseFiniteDepthPromotedIsTrue :
      pointwiseFiniteDepthPromoted ≡ true

    uniformContinuumPromoted :
      Bool

    uniformContinuumPromotedIsFalse :
      uniformContinuumPromoted ≡ false

    quantifierExchangeDischarged :
      Bool

    quantifierExchangeDischargedIsFalse :
      quantifierExchangeDischarged ≡ false

    exchangeBoundary :
      List String

open MassGapQuantifierExchangeReceipt public

canonicalMassGapQuantifierExchangeReceipt :
  MassGapQuantifierExchangeReceipt
canonicalMassGapQuantifierExchangeReceipt =
  record
    { exchangePoints =
        canonicalMassGapQuantifierExchangePoints
    ; exchangePointsAreCanonical =
        refl
    ; pointwiseDepthGapShape =
        "pointwise-depth-gap-forall-d-Delta-d-positive"
    ; pointwiseDepthGapShape-v =
        refl
    ; uniformContinuumGapShape =
        "uniform-continuum-gap-exists-epsilon-forall-d-Delta-d-at-least-epsilon"
    ; uniformContinuumGapShape-v =
        refl
    ; pointwiseFiniteDepthPromoted =
        true
    ; pointwiseFiniteDepthPromotedIsTrue =
        refl
    ; uniformContinuumPromoted =
        false
    ; uniformContinuumPromotedIsFalse =
        refl
    ; quantifierExchangeDischarged =
        false
    ; quantifierExchangeDischargedIsFalse =
        refl
    ; exchangeBoundary =
        "forall d, Delta_d > 0 is the finite-depth pointwise receipt shape"
        ∷ "exists epsilon, forall d, Delta_d >= epsilon is the uniform continuum receipt shape"
        ∷ "this surface records the quantifier exchange point and does not discharge it"
        ∷ []
    }

record MassGapDepthIndexedVsContinuumStatus : Setω where
  field
    finiteDepthReceipt :
      FiniteDepthLatticeGapProObjectReceipt

    continuumReceiptTarget :
      ContinuumMassGapFromBalabanMasterBound

    depthIndexedPromoted :
      Bool

    depthIndexedPromotedIsTrue :
      depthIndexedPromoted ≡ true

    quantifierExchangeReceipt :
      MassGapQuantifierExchangeReceipt

    continuumPromoted :
      Bool

    continuumPromotedIsFalse :
      continuumPromoted ≡ false

    statusBoundary :
      List String

open MassGapDepthIndexedVsContinuumStatus public

canonicalMassGapDepthIndexedVsContinuumStatus :
  MassGapDepthIndexedVsContinuumStatus
canonicalMassGapDepthIndexedVsContinuumStatus =
  record
    { finiteDepthReceipt =
        canonicalFiniteDepthLatticeGapProObjectReceipt
    ; continuumReceiptTarget =
        continuumMassGapFromBalabanMasterBound
    ; depthIndexedPromoted =
        true
    ; depthIndexedPromotedIsTrue =
        refl
    ; quantifierExchangeReceipt =
        canonicalMassGapQuantifierExchangeReceipt
    ; continuumPromoted =
        false
    ; continuumPromotedIsFalse =
        refl
    ; statusBoundary =
        "finite-depth lattice mass-gap receipts are inhabited at every Nat-indexed lattice depth"
        ∷ "the pro-object receipt records the whole depth-indexed family but does not supply a continuum limit theorem"
        ∷ "pointwise forall d positivity is recorded separately from uniform exists epsilon control"
        ∷ "Clay official status remains unsolved in this surface"
        ∷ "continuum promotion waits for an external Balaban master bound and accepted Odusanya authority"
        ∷ []
    }

record VerifiedMassGapAuthorityStatusReceipt : Setω where
  field
    cambridgeOpenEngageStatus :
      VerifiedMassGapAuthoritySourceStatus

    cambridgeOpenEngageStatus-v :
      cambridgeOpenEngageStatus
      ≡
      cambridgeOpenEngageWorkingPreprintUnderReview

    agawaItemsAreWorkingPreprintClaims :
      Bool

    agawaItemsAreWorkingPreprintClaimsIsTrue :
      agawaItemsAreWorkingPreprintClaims ≡ true

    agawaAuthorityAccepted :
      Bool

    agawaAuthorityAcceptedIsFalse :
      agawaAuthorityAccepted ≡ false

    zenodoDissolutionStatus :
      VerifiedMassGapAuthoritySourceStatus

    zenodoDissolutionStatus-v :
      zenodoDissolutionStatus
      ≡
      zenodoDissolutionAlternativeFiniteDiscreteLatticeCampaign

    zenodoDissolutionIsAlternativeCampaign :
      Bool

    zenodoDissolutionIsAlternativeCampaignIsTrue :
      zenodoDissolutionIsAlternativeCampaign ≡ true

    zenodoDissolutionContinuumClayAuthority :
      Bool

    zenodoDissolutionContinuumClayAuthorityIsFalse :
      zenodoDissolutionContinuumClayAuthority ≡ false

    localFiniteDepthCarrierGapAvailable :
      Bool

    localFiniteDepthCarrierGapAvailableIsTrue :
      localFiniteDepthCarrierGapAvailable ≡ true

    localFiniteDepthCarrierGapIsContinuumClayTheorem :
      Bool

    localFiniteDepthCarrierGapIsContinuumClayTheoremIsFalse :
      localFiniteDepthCarrierGapIsContinuumClayTheorem ≡ false

    continuumClayPromotion :
      Bool

    continuumClayPromotionIsFalse :
      continuumClayPromotion ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    verifiedStatusBoundary :
      List String

open VerifiedMassGapAuthorityStatusReceipt public

canonicalVerifiedMassGapAuthorityStatusReceipt :
  VerifiedMassGapAuthorityStatusReceipt
canonicalVerifiedMassGapAuthorityStatusReceipt =
  record
    { cambridgeOpenEngageStatus =
        cambridgeOpenEngageWorkingPreprintUnderReview
    ; cambridgeOpenEngageStatus-v =
        refl
    ; agawaItemsAreWorkingPreprintClaims =
        true
    ; agawaItemsAreWorkingPreprintClaimsIsTrue =
        refl
    ; agawaAuthorityAccepted =
        false
    ; agawaAuthorityAcceptedIsFalse =
        refl
    ; zenodoDissolutionStatus =
        zenodoDissolutionAlternativeFiniteDiscreteLatticeCampaign
    ; zenodoDissolutionStatus-v =
        refl
    ; zenodoDissolutionIsAlternativeCampaign =
        true
    ; zenodoDissolutionIsAlternativeCampaignIsTrue =
        refl
    ; zenodoDissolutionContinuumClayAuthority =
        false
    ; zenodoDissolutionContinuumClayAuthorityIsFalse =
        refl
    ; localFiniteDepthCarrierGapAvailable =
        true
    ; localFiniteDepthCarrierGapAvailableIsTrue =
        refl
    ; localFiniteDepthCarrierGapIsContinuumClayTheorem =
        false
    ; localFiniteDepthCarrierGapIsContinuumClayTheoremIsFalse =
        refl
    ; continuumClayPromotion =
        false
    ; continuumClayPromotionIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; verifiedStatusBoundary =
        "Cambridge/Open Engage Agawa items are recorded only as working preprint claims under review"
        ∷ "Zenodo dissolution is recorded only as an alternative campaign-style finite/discrete-lattice claim"
        ∷ "local finite-depth finite-carrier spectral-gap receipts do not supply continuum or Clay authority"
        ∷ "no terminal, continuum, Clay, journal, or community promotion is constructed here"
        ∷ []
    }

record CandidateMassGapProofLineageReceipt
  (lineage0 : MassGapProofLineage)
  : Setω where
  field
    lineage :
      MassGapProofLineage

    lineage-v :
      lineage
      ≡
      lineage0

    lineageName :
      String

    externalLineage :
      Bool

    externalLineageBoundary :
      String

    nonClayPromoting :
      Bool

    nonClayPromotingIsTrue :
      nonClayPromoting ≡ true

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    perDepthReceiptAlreadyInhabited :
      Bool

    lineageBoundary :
      List String

open CandidateMassGapProofLineageReceipt public

odusanyaBalabanRGLineageReceipt :
  CandidateMassGapProofLineageReceipt OdusanyaBalabanRG
odusanyaBalabanRGLineageReceipt =
  record
    { lineage =
        OdusanyaBalabanRG
    ; lineage-v =
        refl
    ; lineageName =
        "Odusanya-Balaban-RG"
    ; externalLineage =
        true
    ; externalLineageBoundary =
        "external-claimed-Balaban-RG-proof-intake-under-review"
    ; nonClayPromoting =
        true
    ; nonClayPromotingIsTrue =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; perDepthReceiptAlreadyInhabited =
        false
    ; lineageBoundary =
        "records Odusanya/Balaban RG as external authority-dependent intake"
        ∷ "does not promote a Clay continuum theorem inside DASHI"
        ∷ []
    }

agawaHolonomyNonlocalRGLineageReceipt :
  CandidateMassGapProofLineageReceipt AgawaHolonomyNonlocalRG
agawaHolonomyNonlocalRGLineageReceipt =
  record
    { lineage =
        AgawaHolonomyNonlocalRG
    ; lineage-v =
        refl
    ; lineageName =
        "Agawa-Holonomy-Nonlocal-RG"
    ; externalLineage =
        true
    ; externalLineageBoundary =
        "external-holonomy-nonlocal-RG-candidate-intake"
    ; nonClayPromoting =
        true
    ; nonClayPromotingIsTrue =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; perDepthReceiptAlreadyInhabited =
        false
    ; lineageBoundary =
        "maps Agawa holonomy/RG language into DASHI plaquette transport targets"
        ∷ "keeps the candidate external and non-Clay-promoting"
        ∷ []
    }

dissolutionCampaignLineageReceipt :
  CandidateMassGapProofLineageReceipt DissolutionCampaign
dissolutionCampaignLineageReceipt =
  record
    { lineage =
        DissolutionCampaign
    ; lineage-v =
        refl
    ; lineageName =
        "Dissolution-Campaign"
    ; externalLineage =
        true
    ; externalLineageBoundary =
        "external-dissolution-campaign-alternative-intake"
    ; nonClayPromoting =
        true
    ; nonClayPromotingIsTrue =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; perDepthReceiptAlreadyInhabited =
        false
    ; lineageBoundary =
        "records Zenodo dissolution-style alternatives as campaign-style finite/discrete-lattice candidate landscape"
        ∷ "does not discharge continuum, terminal, or Clay obligations"
        ∷ []
    }

dashiProObjectMassGapLineageReceipt :
  CandidateMassGapProofLineageReceipt DASHIProObjectMassGap
dashiProObjectMassGapLineageReceipt =
  record
    { lineage =
        DASHIProObjectMassGap
    ; lineage-v =
        refl
    ; lineageName =
        "DASHI-Pro-Object-Mass-Gap"
    ; externalLineage =
        false
    ; externalLineageBoundary =
        "local-DASHI-depth-indexed-pro-object-receipt"
    ; nonClayPromoting =
        true
    ; nonClayPromotingIsTrue =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; perDepthReceiptAlreadyInhabited =
        true
    ; lineageBoundary =
        "the Nat-indexed finite-depth lattice receipt is already inhabited at every depth"
        ∷ "the inhabited pro-object receipt is not a continuum Clay mass-gap proof"
        ∷ []
    }

record MassGapProofLineageReceiptSurface : Setω where
  field
    lineages :
      List MassGapProofLineage

    lineagesAreCanonical :
      lineages
      ≡
      canonicalMassGapProofLineages

    odusanyaBalabanRG :
      CandidateMassGapProofLineageReceipt OdusanyaBalabanRG

    agawaHolonomyNonlocalRG :
      CandidateMassGapProofLineageReceipt AgawaHolonomyNonlocalRG

    dissolutionCampaign :
      CandidateMassGapProofLineageReceipt DissolutionCampaign

    dashiProObjectMassGap :
      CandidateMassGapProofLineageReceipt DASHIProObjectMassGap

    finiteDepthProObjectReceipt :
      FiniteDepthLatticeGapProObjectReceipt

    externalCandidatesNonClayPromoting :
      Bool

    externalCandidatesNonClayPromotingIsTrue :
      externalCandidatesNonClayPromoting ≡ true

    dashiPerDepthReceiptAlreadyInhabited :
      Bool

    dashiPerDepthReceiptAlreadyInhabitedIsTrue :
      dashiPerDepthReceiptAlreadyInhabited ≡ true

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    lineageSurfaceBoundary :
      List String

open MassGapProofLineageReceiptSurface public

canonicalMassGapProofLineageReceiptSurface :
  MassGapProofLineageReceiptSurface
canonicalMassGapProofLineageReceiptSurface =
  record
    { lineages =
        canonicalMassGapProofLineages
    ; lineagesAreCanonical =
        refl
    ; odusanyaBalabanRG =
        odusanyaBalabanRGLineageReceipt
    ; agawaHolonomyNonlocalRG =
        agawaHolonomyNonlocalRGLineageReceipt
    ; dissolutionCampaign =
        dissolutionCampaignLineageReceipt
    ; dashiProObjectMassGap =
        dashiProObjectMassGapLineageReceipt
    ; finiteDepthProObjectReceipt =
        canonicalFiniteDepthLatticeGapProObjectReceipt
    ; externalCandidatesNonClayPromoting =
        true
    ; externalCandidatesNonClayPromotingIsTrue =
        refl
    ; dashiPerDepthReceiptAlreadyInhabited =
        true
    ; dashiPerDepthReceiptAlreadyInhabitedIsTrue =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; lineageSurfaceBoundary =
        "Odusanya/Balaban, Agawa holonomy/nonlocal RG, and dissolution campaign entries are external non-Clay-promoting candidate lineages"
        ∷ "DASHIProObjectMassGap records the already inhabited per-depth pro-object receipt only"
        ∷ "no lineage in this surface promotes the Clay continuum Yang-Mills mass gap"
        ∷ []
    }

record AgawaHolonomyMassGapReceiptSurface : Setω where
  field
    lineage :
      MassGapProofLineage

    lineageIsAgawa :
      lineage
      ≡
      AgawaHolonomyNonlocalRG

    loopScale :
      String

    loopScale-v :
      loopScale
      ≡
      "loop-scale-ell"

    depthScale :
      String

    depthScale-v :
      depthScale
      ≡
      "depth-scale-a-d=alpha^d"

    plaquetteHolonomy :
      String

    plaquetteHolonomy-v :
      plaquetteHolonomy
      ≡
      "plaquette-holonomy"

    dashiPlaquetteTransport :
      String

    dashiPlaquetteTransport-v :
      dashiPlaquetteTransport
      ≡
      "DASHI-plaquette-transport-H-p^d"

    nonlocalFieldStrength :
      String

    nonlocalFieldStrength-v :
      nonlocalFieldStrength
      ≡
      "nonlocal-field-strength"

    plaquetteDefect :
      String

    plaquetteDefect-v :
      plaquetteDefect
      ≡
      "plaquette-defect-Omega"

    clusterActivity :
      String

    clusterActivity-v :
      clusterActivity
      ≡
      "cluster-activity"

    receiptAmplitudePrimeLaneCluster :
      String

    receiptAmplitudePrimeLaneCluster-v :
      receiptAmplitudePrimeLaneCluster
      ≡
      "receipt-amplitude-prime-lane-cluster"

    irFixedPoint :
      String

    irFixedPoint-v :
      irFixedPoint
      ≡
      "IR-fixed-point"

    proObjectInfGap :
      String

    proObjectInfGap-v :
      proObjectInfGap
      ≡
      "pro-object-inf-gap"

    gribovFree :
      String

    gribovFree-v :
      gribovFree
      ≡
      "Gribov-free"

    gaugeInvariantPrimeLaneTransport :
      String

    gaugeInvariantPrimeLaneTransport-v :
      gaugeInvariantPrimeLaneTransport
      ≡
      "gauge-invariant-prime-lane-transport"

    externalCandidate :
      Bool

    externalCandidateIsTrue :
      externalCandidate ≡ true

    clayPromoting :
      Bool

    clayPromotingIsFalse :
      clayPromoting ≡ false

    dashiContinuumMassGapPromoted :
      Bool

    dashiContinuumMassGapPromotedIsFalse :
      dashiContinuumMassGapPromoted ≡ false

    mappingBoundary :
      List String

open AgawaHolonomyMassGapReceiptSurface public

canonicalAgawaHolonomyMassGapReceiptSurface :
  AgawaHolonomyMassGapReceiptSurface
canonicalAgawaHolonomyMassGapReceiptSurface =
  record
    { lineage =
        AgawaHolonomyNonlocalRG
    ; lineageIsAgawa =
        refl
    ; loopScale =
        "loop-scale-ell"
    ; loopScale-v =
        refl
    ; depthScale =
        "depth-scale-a-d=alpha^d"
    ; depthScale-v =
        refl
    ; plaquetteHolonomy =
        "plaquette-holonomy"
    ; plaquetteHolonomy-v =
        refl
    ; dashiPlaquetteTransport =
        "DASHI-plaquette-transport-H-p^d"
    ; dashiPlaquetteTransport-v =
        refl
    ; nonlocalFieldStrength =
        "nonlocal-field-strength"
    ; nonlocalFieldStrength-v =
        refl
    ; plaquetteDefect =
        "plaquette-defect-Omega"
    ; plaquetteDefect-v =
        refl
    ; clusterActivity =
        "cluster-activity"
    ; clusterActivity-v =
        refl
    ; receiptAmplitudePrimeLaneCluster =
        "receipt-amplitude-prime-lane-cluster"
    ; receiptAmplitudePrimeLaneCluster-v =
        refl
    ; irFixedPoint =
        "IR-fixed-point"
    ; irFixedPoint-v =
        refl
    ; proObjectInfGap =
        "pro-object-inf-gap"
    ; proObjectInfGap-v =
        refl
    ; gribovFree =
        "Gribov-free"
    ; gribovFree-v =
        refl
    ; gaugeInvariantPrimeLaneTransport =
        "gauge-invariant-prime-lane-transport"
    ; gaugeInvariantPrimeLaneTransport-v =
        refl
    ; externalCandidate =
        true
    ; externalCandidateIsTrue =
        refl
    ; clayPromoting =
        false
    ; clayPromotingIsFalse =
        refl
    ; dashiContinuumMassGapPromoted =
        false
    ; dashiContinuumMassGapPromotedIsFalse =
        refl
    ; mappingBoundary =
        "loop scale ell maps to depth scale a_d=alpha^d"
        ∷ "plaquette holonomy maps to DASHI plaquette transport H_p^d"
        ∷ "nonlocal field strength maps to plaquette defect Omega"
        ∷ "cluster activity maps to receipt amplitude / prime-lane cluster"
        ∷ "IR fixed point maps to pro-object inf gap"
        ∷ "Gribov-free maps to gauge-invariant prime-lane transport"
        ∷ "the mapping is an external candidate intake and not a Clay promotion"
        ∷ []
    }

data AgawaCompletionClaimComponent : Set where
  stableIRFixedPointClaim :
    AgawaCompletionClaimComponent

  finiteGribovMorseClosureClaim :
    AgawaCompletionClaimComponent

canonicalAgawaCompletionClaimComponents :
  List AgawaCompletionClaimComponent
canonicalAgawaCompletionClaimComponents =
  stableIRFixedPointClaim
  ∷ finiteGribovMorseClosureClaim
  ∷ []

record AgawaCompletionCriticalGapStatus : Setω where
  field
    claimComponents :
      List AgawaCompletionClaimComponent

    claimComponentsAreCanonical :
      claimComponents
      ≡
      canonicalAgawaCompletionClaimComponents

    sourceStatus :
      String

    sourceStatus-v :
      sourceStatus
      ≡
      "Cambridge-Engage-preprint-claim-under-review-non-Clay-authority"

    stableIRFixedPointClaimed :
      Bool

    stableIRFixedPointClaimedIsTrue :
      stableIRFixedPointClaimed ≡ true

    finiteGribovMorseClosureClaimed :
      Bool

    finiteGribovMorseClosureClaimedIsTrue :
      finiteGribovMorseClosureClaimed ≡ true

    preprintAuthorityUnderReview :
      Bool

    preprintAuthorityUnderReviewIsTrue :
      preprintAuthorityUnderReview ≡ true

    clayAuthorityAccepted :
      Bool

    clayAuthorityAcceptedIsFalse :
      clayAuthorityAccepted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    gapStatusBoundary :
      List String

open AgawaCompletionCriticalGapStatus public

canonicalAgawaCompletionCriticalGapStatus :
  AgawaCompletionCriticalGapStatus
canonicalAgawaCompletionCriticalGapStatus =
  record
    { claimComponents =
        canonicalAgawaCompletionClaimComponents
    ; claimComponentsAreCanonical =
        refl
    ; sourceStatus =
        "Cambridge-Engage-preprint-claim-under-review-non-Clay-authority"
    ; sourceStatus-v =
        refl
    ; stableIRFixedPointClaimed =
        true
    ; stableIRFixedPointClaimedIsTrue =
        refl
    ; finiteGribovMorseClosureClaimed =
        true
    ; finiteGribovMorseClosureClaimedIsTrue =
        refl
    ; preprintAuthorityUnderReview =
        true
    ; preprintAuthorityUnderReviewIsTrue =
        refl
    ; clayAuthorityAccepted =
        false
    ; clayAuthorityAcceptedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; gapStatusBoundary =
        "records the Agawa completion claim as closing stable IR fixed-point control and finite Gribov/Morse uniqueness"
        ∷ "the source is treated here as a Cambridge Engage preprint authority under review"
        ∷ "this status surface does not promote the Clay continuum Yang-Mills mass gap"
        ∷ []
    }

record IntrinsicIrrelevantOperatorSuppressionReceipt : Setω where
  field
    nonlocalEffectiveActionShape :
      String

    nonlocalEffectiveActionShape-v :
      nonlocalEffectiveActionShape
      ≡
      "S-ell=sum-plaquettes-nonlocal-holonomy-action-plus-irrelevant-operator-tail"

    irrelevantOperatorShape :
      String

    irrelevantOperatorShape-v :
      irrelevantOperatorShape
      ≡
      "operator-O-n-of-dimension-four-plus-k-with-k-positive"

    treeSuppression :
      String

    treeSuppression-v :
      treeSuppression
      ≡
      "c-n-of-L-ell-equals-L^-k-times-c-n-of-ell-at-tree-level"

    loopCorrection :
      String

    loopCorrection-v :
      loopCorrection
      ≡
      "loop-correction-order-g^2-ell-times-ell^k"

    asymptoticFreedomDomination :
      String

    asymptoticFreedomDomination-v :
      asymptoticFreedomDomination
      ≡
      "asymptotic-freedom-makes-g^2-ell-small-enough-that-tree-suppression-dominates-loop-corrections"

    nonlocalSuppressionClaimed :
      Bool

    nonlocalSuppressionClaimedIsTrue :
      nonlocalSuppressionClaimed ≡ true

    locallyProvedHere :
      Bool

    locallyProvedHereIsFalse :
      locallyProvedHere ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    suppressionBoundary :
      List String

open IntrinsicIrrelevantOperatorSuppressionReceipt public

canonicalIntrinsicIrrelevantOperatorSuppressionReceipt :
  IntrinsicIrrelevantOperatorSuppressionReceipt
canonicalIntrinsicIrrelevantOperatorSuppressionReceipt =
  record
    { nonlocalEffectiveActionShape =
        "S-ell=sum-plaquettes-nonlocal-holonomy-action-plus-irrelevant-operator-tail"
    ; nonlocalEffectiveActionShape-v =
        refl
    ; irrelevantOperatorShape =
        "operator-O-n-of-dimension-four-plus-k-with-k-positive"
    ; irrelevantOperatorShape-v =
        refl
    ; treeSuppression =
        "c-n-of-L-ell-equals-L^-k-times-c-n-of-ell-at-tree-level"
    ; treeSuppression-v =
        refl
    ; loopCorrection =
        "loop-correction-order-g^2-ell-times-ell^k"
    ; loopCorrection-v =
        refl
    ; asymptoticFreedomDomination =
        "asymptotic-freedom-makes-g^2-ell-small-enough-that-tree-suppression-dominates-loop-corrections"
    ; asymptoticFreedomDomination-v =
        refl
    ; nonlocalSuppressionClaimed =
        true
    ; nonlocalSuppressionClaimedIsTrue =
        refl
    ; locallyProvedHere =
        false
    ; locallyProvedHereIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; suppressionBoundary =
        "records the Agawa intrinsic suppression mechanism for irrelevant operators in nonlocal holonomy variables"
        ∷ "tree-level L^-k suppression and loop corrections of order g^2(ell) ell^k are recorded as typed receipt shapes"
        ∷ "asymptotic-freedom domination is a claimed external analytic step, not a local DASHI proof in this file"
        ∷ []
    }

record AgawaStableIRFixedPointCompletion : Setω where
  field
    criticalGapStatus :
      AgawaCompletionCriticalGapStatus

    suppressionReceipt :
      IntrinsicIrrelevantOperatorSuppressionReceipt

    fixedPointActionShape :
      String

    fixedPointActionShape-v :
      fixedPointActionShape
      ≡
      "S-star-equals-nonlocal-plaquette-holonomy-action-at-finite-nonzero-g-star"

    transferMatrixGapShape :
      String

    transferMatrixGapShape-v :
      transferMatrixGapShape
      ≡
      "Delta-star=-a^-1-log-norm-of-transfer-matrix-on-vacuum-complement-positive"

    inheritedFromLatticeGap :
      Bool

    inheritedFromLatticeGapIsTrue :
      inheritedFromLatticeGap ≡ true

    stableFixedPointClaimed :
      Bool

    stableFixedPointClaimedIsTrue :
      stableFixedPointClaimed ≡ true

    cambridgePreprintAuthorityUnderReview :
      Bool

    cambridgePreprintAuthorityUnderReviewIsTrue :
      cambridgePreprintAuthorityUnderReview ≡ true

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    fixedPointBoundary :
      List String

open AgawaStableIRFixedPointCompletion public

canonicalAgawaStableIRFixedPointCompletion :
  AgawaStableIRFixedPointCompletion
canonicalAgawaStableIRFixedPointCompletion =
  record
    { criticalGapStatus =
        canonicalAgawaCompletionCriticalGapStatus
    ; suppressionReceipt =
        canonicalIntrinsicIrrelevantOperatorSuppressionReceipt
    ; fixedPointActionShape =
        "S-star-equals-nonlocal-plaquette-holonomy-action-at-finite-nonzero-g-star"
    ; fixedPointActionShape-v =
        refl
    ; transferMatrixGapShape =
        "Delta-star=-a^-1-log-norm-of-transfer-matrix-on-vacuum-complement-positive"
    ; transferMatrixGapShape-v =
        refl
    ; inheritedFromLatticeGap =
        true
    ; inheritedFromLatticeGapIsTrue =
        refl
    ; stableFixedPointClaimed =
        true
    ; stableFixedPointClaimedIsTrue =
        refl
    ; cambridgePreprintAuthorityUnderReview =
        true
    ; cambridgePreprintAuthorityUnderReviewIsTrue =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; fixedPointBoundary =
        "records the Agawa completion claim that the stable nonlocal IR fixed point preserves the lattice transfer-matrix gap"
        ∷ "the fixed-point gap is an authority-backed receipt target, not a local Clay promotion"
        ∷ []
    }

record GeometricCompletenessGribovUniqueReceipt : Setω where
  field
    g4PrimeLaneIndependenceInput :
      String

    g4PrimeLaneIndependenceInput-v :
      g4PrimeLaneIndependenceInput
      ≡
      "G4-prime-lane-independence"

    loopHomologySpanShape :
      String

    loopHomologySpanShape-v :
      loopHomologySpanShape
      ≡
      "span-of-prime-lane-plaquette-boundary-classes-equals-H1-of-DASHI-carrier"

    morseFunctionalShape :
      String

    morseFunctionalShape-v :
      morseFunctionalShape
      ≡
      "F-A-of-g=sum-plaquettes-norm-H-square-g-minus-id-squared"

    hessianStrictPositivityTarget :
      String

    hessianStrictPositivityTarget-v :
      hessianStrictPositivityTarget
      ≡
      "geometric-completeness-forces-strict-positivity-of-holonomy-Faddeev-Popov-Hessian-curvature-term"

    geometricCompletenessEncoded :
      Bool

    geometricCompletenessEncodedIsTrue :
      geometricCompletenessEncoded ≡ true

    gribovUniqueClaimed :
      Bool

    gribovUniqueClaimedIsTrue :
      gribovUniqueClaimed ≡ true

    clayAcceptedProof :
      Bool

    clayAcceptedProofIsFalse :
      clayAcceptedProof ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    gribovBoundary :
      List String

open GeometricCompletenessGribovUniqueReceipt public

canonicalGeometricCompletenessGribovUniqueReceipt :
  GeometricCompletenessGribovUniqueReceipt
canonicalGeometricCompletenessGribovUniqueReceipt =
  record
    { g4PrimeLaneIndependenceInput =
        "G4-prime-lane-independence"
    ; g4PrimeLaneIndependenceInput-v =
        refl
    ; loopHomologySpanShape =
        "span-of-prime-lane-plaquette-boundary-classes-equals-H1-of-DASHI-carrier"
    ; loopHomologySpanShape-v =
        refl
    ; morseFunctionalShape =
        "F-A-of-g=sum-plaquettes-norm-H-square-g-minus-id-squared"
    ; morseFunctionalShape-v =
        refl
    ; hessianStrictPositivityTarget =
        "geometric-completeness-forces-strict-positivity-of-holonomy-Faddeev-Popov-Hessian-curvature-term"
    ; hessianStrictPositivityTarget-v =
        refl
    ; geometricCompletenessEncoded =
        true
    ; geometricCompletenessEncodedIsTrue =
        refl
    ; gribovUniqueClaimed =
        true
    ; gribovUniqueClaimedIsTrue =
        refl
    ; clayAcceptedProof =
        false
    ; clayAcceptedProofIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; gribovBoundary =
        "G4 prime-lane independence is recorded as the DASHI geometric-completeness input"
        ∷ "geometric completeness targets strict positivity of the Hessian curvature term in the holonomy Morse functional"
        ∷ "Gribov uniqueness is encoded as an Agawa/Morse claimed receipt, not as accepted Clay proof"
        ∷ []
    }

record CompleteAgawaDASHIMassGapClosureChain : Setω where
  field
    latticeGapReceipt :
      FiniteDepthLatticeGapProObjectReceipt

    agawaIRFixedPointCompletion :
      AgawaStableIRFixedPointCompletion

    gribovUniqueReceipt :
      GeometricCompletenessGribovUniqueReceipt

    chainShape :
      String

    chainShape-v :
      chainShape
      ≡
      "LatticeGapReceipt-times-AgawaIRFixedPoint-times-GribovUnique-to-ContinuumMassGapReceipt"

    latticeGapEncoded :
      Bool

    latticeGapEncodedIsTrue :
      latticeGapEncoded ≡ true

    agawaIRFixedPointUnderReview :
      Bool

    agawaIRFixedPointUnderReviewIsTrue :
      agawaIRFixedPointUnderReview ≡ true

    gribovUniqueEncoded :
      Bool

    gribovUniqueEncodedIsTrue :
      gribovUniqueEncoded ≡ true

    continuumMassGapReceiptTargetEncoded :
      Bool

    continuumMassGapReceiptTargetEncodedIsTrue :
      continuumMassGapReceiptTargetEncoded ≡ true

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    closureBoundary :
      List String

open CompleteAgawaDASHIMassGapClosureChain public

canonicalCompleteAgawaDASHIMassGapClosureChain :
  CompleteAgawaDASHIMassGapClosureChain
canonicalCompleteAgawaDASHIMassGapClosureChain =
  record
    { latticeGapReceipt =
        canonicalFiniteDepthLatticeGapProObjectReceipt
    ; agawaIRFixedPointCompletion =
        canonicalAgawaStableIRFixedPointCompletion
    ; gribovUniqueReceipt =
        canonicalGeometricCompletenessGribovUniqueReceipt
    ; chainShape =
        "LatticeGapReceipt-times-AgawaIRFixedPoint-times-GribovUnique-to-ContinuumMassGapReceipt"
    ; chainShape-v =
        refl
    ; latticeGapEncoded =
        true
    ; latticeGapEncodedIsTrue =
        refl
    ; agawaIRFixedPointUnderReview =
        true
    ; agawaIRFixedPointUnderReviewIsTrue =
        refl
    ; gribovUniqueEncoded =
        true
    ; gribovUniqueEncodedIsTrue =
        refl
    ; continuumMassGapReceiptTargetEncoded =
        true
    ; continuumMassGapReceiptTargetEncodedIsTrue =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; closureBoundary =
        "lattice gap is encoded by the finite-depth/pro-object receipt family"
        ∷ "Agawa IR fixed point is recorded as Cambridge-preprint authority under review"
        ∷ "Gribov uniqueness is encoded through G4 geometric completeness plus the Agawa Morse-theory claim"
        ∷ "the product chain targets ContinuumMassGapReceipt but keeps continuumClayMassGapPromoted false"
        ∷ []
    }

data AlternativeContinuumAuthority : Set where
  UniformBalaban :
    AlternativeContinuumAuthority

  AgawaIRFixedPoint :
    AlternativeContinuumAuthority

canonicalAlternativeContinuumAuthorities :
  List AlternativeContinuumAuthority
canonicalAlternativeContinuumAuthorities =
  UniformBalaban
  ∷ AgawaIRFixedPoint
  ∷ []

record AlternativeContinuumAuthorityReceipt
  (authority0 : AlternativeContinuumAuthority)
  : Setω where
  field
    authority :
      AlternativeContinuumAuthority

    authority-v :
      authority
      ≡
      authority0

    authorityName :
      String

    authorityShape :
      String

    authorityTokenRequired :
      Bool

    authorityTokenRequiredIsTrue :
      authorityTokenRequired ≡ true

    authorityTokenSupplied :
      Bool

    authorityTokenSuppliedIsFalse :
      authorityTokenSupplied ≡ false

    nonClayPromotingUnlessAuthorityTokenSupplied :
      Bool

    nonClayPromotingUnlessAuthorityTokenSuppliedIsTrue :
      nonClayPromotingUnlessAuthorityTokenSupplied ≡ true

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    authorityBoundary :
      List String

open AlternativeContinuumAuthorityReceipt public

uniformBalabanAuthorityReceipt :
  AlternativeContinuumAuthorityReceipt UniformBalaban
uniformBalabanAuthorityReceipt =
  record
    { authority =
        UniformBalaban
    ; authority-v =
        refl
    ; authorityName =
        "UniformBalaban"
    ; authorityShape =
        "uniform-Balaban-master-bound-supplies-exists-epsilon-forall-depth-continuum-control"
    ; authorityTokenRequired =
        true
    ; authorityTokenRequiredIsTrue =
        refl
    ; authorityTokenSupplied =
        false
    ; authorityTokenSuppliedIsFalse =
        refl
    ; nonClayPromotingUnlessAuthorityTokenSupplied =
        true
    ; nonClayPromotingUnlessAuthorityTokenSuppliedIsTrue =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; authorityBoundary =
        "UniformBalaban is the precise authority alternative for uniform Balaban continuum control"
        ∷ "without an authority token it remains a non-Clay-promoting receipt"
        ∷ []
    }

agawaIRFixedPointAuthorityReceipt :
  AlternativeContinuumAuthorityReceipt AgawaIRFixedPoint
agawaIRFixedPointAuthorityReceipt =
  record
    { authority =
        AgawaIRFixedPoint
    ; authority-v =
        refl
    ; authorityName =
        "AgawaIRFixedPoint"
    ; authorityShape =
        "Agawa-IR-fixed-point-supplies-gauge-invariant-nonlocal-RG-continuum-gap-authority"
    ; authorityTokenRequired =
        true
    ; authorityTokenRequiredIsTrue =
        refl
    ; authorityTokenSupplied =
        false
    ; authorityTokenSuppliedIsFalse =
        refl
    ; nonClayPromotingUnlessAuthorityTokenSupplied =
        true
    ; nonClayPromotingUnlessAuthorityTokenSuppliedIsTrue =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; authorityBoundary =
        "AgawaIRFixedPoint is the precise authority alternative for Agawa IR fixed-point continuum control"
        ∷ "without an authority token it remains a non-Clay-promoting receipt"
        ∷ []
    }

record AlternativeContinuumAuthorityReceiptSurface : Setω where
  field
    authorities :
      List AlternativeContinuumAuthority

    authoritiesAreCanonical :
      authorities
      ≡
      canonicalAlternativeContinuumAuthorities

    uniformBalaban :
      AlternativeContinuumAuthorityReceipt UniformBalaban

    agawaIRFixedPoint :
      AlternativeContinuumAuthorityReceipt AgawaIRFixedPoint

    allRequireAuthorityToken :
      Bool

    allRequireAuthorityTokenIsTrue :
      allRequireAuthorityToken ≡ true

    allNonClayPromotingWithoutAuthorityToken :
      Bool

    allNonClayPromotingWithoutAuthorityTokenIsTrue :
      allNonClayPromotingWithoutAuthorityToken ≡ true

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    authoritySurfaceBoundary :
      List String

open AlternativeContinuumAuthorityReceiptSurface public

canonicalAlternativeContinuumAuthorityReceiptSurface :
  AlternativeContinuumAuthorityReceiptSurface
canonicalAlternativeContinuumAuthorityReceiptSurface =
  record
    { authorities =
        canonicalAlternativeContinuumAuthorities
    ; authoritiesAreCanonical =
        refl
    ; uniformBalaban =
        uniformBalabanAuthorityReceipt
    ; agawaIRFixedPoint =
        agawaIRFixedPointAuthorityReceipt
    ; allRequireAuthorityToken =
        true
    ; allRequireAuthorityTokenIsTrue =
        refl
    ; allNonClayPromotingWithoutAuthorityToken =
        true
    ; allNonClayPromotingWithoutAuthorityTokenIsTrue =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; authoritySurfaceBoundary =
        "UniformBalaban and AgawaIRFixedPoint are alternative continuum authority receipts"
        ∷ "both remain non-Clay-promoting without an authority token"
        ∷ []
    }

record UniformBalabanOrAgawaIRFixedPointFailClosedReceipt : Setω where
  field
    authoritySurface :
      AlternativeContinuumAuthorityReceiptSurface

    haltName :
      String

    haltNameIsUniformBalabanOrAgawaIRFixedPoint :
      haltName
      ≡
      "UniformBalaban-or-AgawaIRFixedPoint"

    uniformBalabanAuthority :
      AlternativeContinuumAuthorityReceipt UniformBalaban

    agawaIRFixedPointAuthority :
      AlternativeContinuumAuthorityReceipt AgawaIRFixedPoint

    uniformBalabanTokenSupplied :
      Bool

    uniformBalabanTokenSuppliedIsFalse :
      uniformBalabanTokenSupplied ≡ false

    agawaIRFixedPointTokenSupplied :
      Bool

    agawaIRFixedPointTokenSuppliedIsFalse :
      agawaIRFixedPointTokenSupplied ≡ false

    acceptedContinuumAuthoritySupplied :
      Bool

    acceptedContinuumAuthoritySuppliedIsFalse :
      acceptedContinuumAuthoritySupplied ≡ false

    continuumMassGapProvedInDASHI :
      Bool

    continuumMassGapProvedInDASHIIsFalse :
      continuumMassGapProvedInDASHI ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    failClosedBoundary :
      List String

open UniformBalabanOrAgawaIRFixedPointFailClosedReceipt public

canonicalUniformBalabanOrAgawaIRFixedPointFailClosedReceipt :
  UniformBalabanOrAgawaIRFixedPointFailClosedReceipt
canonicalUniformBalabanOrAgawaIRFixedPointFailClosedReceipt =
  record
    { authoritySurface =
        canonicalAlternativeContinuumAuthorityReceiptSurface
    ; haltName =
        "UniformBalaban-or-AgawaIRFixedPoint"
    ; haltNameIsUniformBalabanOrAgawaIRFixedPoint =
        refl
    ; uniformBalabanAuthority =
        uniformBalabanAuthorityReceipt
    ; agawaIRFixedPointAuthority =
        agawaIRFixedPointAuthorityReceipt
    ; uniformBalabanTokenSupplied =
        false
    ; uniformBalabanTokenSuppliedIsFalse =
        refl
    ; agawaIRFixedPointTokenSupplied =
        false
    ; agawaIRFixedPointTokenSuppliedIsFalse =
        refl
    ; acceptedContinuumAuthoritySupplied =
        false
    ; acceptedContinuumAuthoritySuppliedIsFalse =
        refl
    ; continuumMassGapProvedInDASHI =
        false
    ; continuumMassGapProvedInDASHIIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; failClosedBoundary =
        "UniformBalaban-or-AgawaIRFixedPoint is the exact l6 continuum authority halt"
        ∷ "UniformBalaban requires an authority token for uniform continuum control and that token is not supplied"
        ∷ "AgawaIRFixedPoint requires an authority token for fixed-point continuum control and that token is not supplied"
        ∷ "No continuum DASHI proof, Clay promotion, or terminal promotion is derived from these candidate surfaces"
        ∷ []
    }

record DASHIDepthRecursionContractionFlipCondition : Setω where
  field
    conditionName :
      String

    conditionName-v :
      conditionName
      ≡
      "tranche4-condition1-depth-recursion-contraction-flip-condition"

    stepARecursionOperatorTarget :
      String

    stepARecursionOperatorTarget-v :
      stepARecursionOperatorTarget
      ≡
      "R(Delta)=sqrt(Delta^2*(1-2*ln(1/alpha))+A*g^2(a_d)/a_d^2*exp(-Delta^2*a_d^2/4))"

    stepBContractionIntervalTarget :
      String

    stepBContractionIntervalTarget-v :
      stepBContractionIntervalTarget
      ≡
      "R-is-Lipschitz-on-[epsilon0,M]-with-K=sup-abs-Rprime-less-than-one"

    stepBDerivativeFormulaTarget :
      String

    stepBDerivativeFormulaTarget-v :
      stepBDerivativeFormulaTarget
      ≡
      "K=sup_Delta|Delta*(1-2*ln(1/alpha))-(A*g^2*a_d^2/4)*Delta*exp(-Delta^2*a_d^2/4)|/R(Delta)"

    alphaHalfExampleTarget :
      String

    alphaHalfExampleTarget-v :
      alphaHalfExampleTarget
      ≡
      "alpha=1/2-gives-K-approximately-2ln2-minus-1-less-than-one-after-small-a_d-control"

    stepCBanachFixedPointTarget :
      String

    stepCBanachFixedPointTarget-v :
      stepCBanachFixedPointTarget
      ≡
      "Banach-fixed-point-on-invariant-interval-R([epsilon0,M])-subset-[epsilon0,M]"

    stepCInitialGapTarget :
      String

    stepCInitialGapTarget-v :
      stepCInitialGapTarget
      ≡
      "Delta0-positive-by-lattice-gap-and-bounded-above-by-compactness-of-the-gauge-group"

    stepCFixedPointPositiveTarget :
      String

    stepCFixedPointPositiveTarget-v :
      stepCFixedPointPositiveTarget
      ≡
      "unique-fixed-point-Delta-star-positive-and-all-depth-trajectories-converge-to-it"

    stepDContinuumLimitTarget :
      String

    stepDContinuumLimitTarget-v :
      stepDContinuumLimitTarget
      ≡
      "continuum-limit-Delta=lim_d-Delta_d=Delta-star-positive"

    remainingConstantsComputation :
      String

    remainingConstantsComputation-v :
      remainingConstantsComputation
      ≡
      "compute-A-alpha-g^2(Lambda_QCD)-and-an-invariant-interval-[epsilon0,M]"

    monotonicityCondition :
      String

    monotonicityCondition-v :
      monotonicityCondition
      ≡
      "prove-R-maps-[epsilon0,M]-into-itself-and-is-monotone-or-order-controlled-on-the-depth-recursion-interval"

    recursionOperatorDefined :
      Bool

    recursionOperatorDefinedIsTrue :
      recursionOperatorDefined ≡ true

    contractionProofAccepted :
      Bool

    contractionProofAcceptedIsFalse :
      contractionProofAccepted ≡ false

    invariantIntervalDischarged :
      Bool

    invariantIntervalDischargedIsFalse :
      invariantIntervalDischarged ≡ false

    monotonicityDischarged :
      Bool

    monotonicityDischargedIsFalse :
      monotonicityDischarged ≡ false

    candidateProofNotAccepted :
      Bool

    candidateProofNotAcceptedIsTrue :
      candidateProofNotAccepted ≡ true

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    flipConditionBoundary :
      List String

open DASHIDepthRecursionContractionFlipCondition public

canonicalDASHIDepthRecursionContractionFlipCondition :
  DASHIDepthRecursionContractionFlipCondition
canonicalDASHIDepthRecursionContractionFlipCondition =
  record
    { conditionName =
        "tranche4-condition1-depth-recursion-contraction-flip-condition"
    ; conditionName-v =
        refl
    ; stepARecursionOperatorTarget =
        "R(Delta)=sqrt(Delta^2*(1-2*ln(1/alpha))+A*g^2(a_d)/a_d^2*exp(-Delta^2*a_d^2/4))"
    ; stepARecursionOperatorTarget-v =
        refl
    ; stepBContractionIntervalTarget =
        "R-is-Lipschitz-on-[epsilon0,M]-with-K=sup-abs-Rprime-less-than-one"
    ; stepBContractionIntervalTarget-v =
        refl
    ; stepBDerivativeFormulaTarget =
        "K=sup_Delta|Delta*(1-2*ln(1/alpha))-(A*g^2*a_d^2/4)*Delta*exp(-Delta^2*a_d^2/4)|/R(Delta)"
    ; stepBDerivativeFormulaTarget-v =
        refl
    ; alphaHalfExampleTarget =
        "alpha=1/2-gives-K-approximately-2ln2-minus-1-less-than-one-after-small-a_d-control"
    ; alphaHalfExampleTarget-v =
        refl
    ; stepCBanachFixedPointTarget =
        "Banach-fixed-point-on-invariant-interval-R([epsilon0,M])-subset-[epsilon0,M]"
    ; stepCBanachFixedPointTarget-v =
        refl
    ; stepCInitialGapTarget =
        "Delta0-positive-by-lattice-gap-and-bounded-above-by-compactness-of-the-gauge-group"
    ; stepCInitialGapTarget-v =
        refl
    ; stepCFixedPointPositiveTarget =
        "unique-fixed-point-Delta-star-positive-and-all-depth-trajectories-converge-to-it"
    ; stepCFixedPointPositiveTarget-v =
        refl
    ; stepDContinuumLimitTarget =
        "continuum-limit-Delta=lim_d-Delta_d=Delta-star-positive"
    ; stepDContinuumLimitTarget-v =
        refl
    ; remainingConstantsComputation =
        "compute-A-alpha-g^2(Lambda_QCD)-and-an-invariant-interval-[epsilon0,M]"
    ; remainingConstantsComputation-v =
        refl
    ; monotonicityCondition =
        "prove-R-maps-[epsilon0,M]-into-itself-and-is-monotone-or-order-controlled-on-the-depth-recursion-interval"
    ; monotonicityCondition-v =
        refl
    ; recursionOperatorDefined =
        true
    ; recursionOperatorDefinedIsTrue =
        refl
    ; contractionProofAccepted =
        false
    ; contractionProofAcceptedIsFalse =
        refl
    ; invariantIntervalDischarged =
        false
    ; invariantIntervalDischargedIsFalse =
        refl
    ; monotonicityDischarged =
        false
    ; monotonicityDischargedIsFalse =
        refl
    ; candidateProofNotAccepted =
        true
    ; candidateProofNotAcceptedIsTrue =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; flipConditionBoundary =
        "Step A records the explicit DASHI recursion operator target R(Delta)"
        ∷ "Step B records the Lipschitz derivative target and alpha=1/2 contraction example"
        ∷ "Step C records the Banach fixed-point and invariant-interval obligations"
        ∷ "open gap: the proof still needs an invariant interval and monotonicity or order-control for the depth recursion on that interval"
        ∷ "the monotonicity condition is the real remaining obligation because contraction alone does not show the recursive trajectory stays in the positive interval used for the continuum lower bound"
        ∷ "monotonicity and invariant-interval discharge are both false here"
        ∷ "Step D records the continuum limit target Delta equals Delta-star greater than zero"
        ∷ "the remaining computation is A, alpha, g^2(Lambda_QCD), and an invariant interval [epsilon0,M]"
        ∷ "this is a candidate Clay-level proof skeleton and does not promote the continuum Clay mass gap"
        ∷ []
    }

record DASHIInternalDepthRecursionContractionCandidate : Setω where
  field
    candidateName :
      String

    candidateName-v :
      candidateName
      ≡
      "DASHI-internal-depth-recursion-contraction-candidate"

    agawaFlowEquationShape :
      String

    agawaFlowEquationShape-v :
      agawaFlowEquationShape
      ≡
      "d-Delta-dt=-A-Delta-plus-quadratic-and-controlled-remainder-terms"

    oneLoopCoefficientPositivityReceipt :
      String

    oneLoopCoefficientPositivityReceipt-v :
      oneLoopCoefficientPositivityReceipt
      ≡
      "A=N^2/(2(4pi)^2)-positive-receipt-string"

    oneLoopCoefficientStatus :
      String

    oneLoopCoefficientStatus-v :
      oneLoopCoefficientStatus
      ≡
      "receipt-only-no-local-arithmetic-proof"

    contractionConstantCondition :
      String

    contractionConstantCondition-v :
      contractionConstantCondition
      ≡
      "exists-kappa-less-than-one-for-depth-recursion-map-on-controlled-norm-ball"

    contractionConstantConditionAccepted :
      Bool

    contractionConstantConditionAcceptedIsFalse :
      contractionConstantConditionAccepted ≡ false

    tranche4Condition1FlipCondition :
      DASHIDepthRecursionContractionFlipCondition

    finiteDepthProObjectCandidate :
      Bool

    finiteDepthProObjectCandidateIsTrue :
      finiteDepthProObjectCandidate ≡ true

    candidateClayLevelProofNotAccepted :
      Bool

    candidateClayLevelProofNotAcceptedIsTrue :
      candidateClayLevelProofNotAccepted ≡ true

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    candidateBoundary :
      List String

open DASHIInternalDepthRecursionContractionCandidate public

canonicalDASHIInternalDepthRecursionContractionCandidate :
  DASHIInternalDepthRecursionContractionCandidate
canonicalDASHIInternalDepthRecursionContractionCandidate =
  record
    { candidateName =
        "DASHI-internal-depth-recursion-contraction-candidate"
    ; candidateName-v =
        refl
    ; agawaFlowEquationShape =
        "d-Delta-dt=-A-Delta-plus-quadratic-and-controlled-remainder-terms"
    ; agawaFlowEquationShape-v =
        refl
    ; oneLoopCoefficientPositivityReceipt =
        "A=N^2/(2(4pi)^2)-positive-receipt-string"
    ; oneLoopCoefficientPositivityReceipt-v =
        refl
    ; oneLoopCoefficientStatus =
        "receipt-only-no-local-arithmetic-proof"
    ; oneLoopCoefficientStatus-v =
        refl
    ; contractionConstantCondition =
        "exists-kappa-less-than-one-for-depth-recursion-map-on-controlled-norm-ball"
    ; contractionConstantCondition-v =
        refl
    ; contractionConstantConditionAccepted =
        false
    ; contractionConstantConditionAcceptedIsFalse =
        refl
    ; tranche4Condition1FlipCondition =
        canonicalDASHIDepthRecursionContractionFlipCondition
    ; finiteDepthProObjectCandidate =
        true
    ; finiteDepthProObjectCandidateIsTrue =
        refl
    ; candidateClayLevelProofNotAccepted =
        true
    ; candidateClayLevelProofNotAcceptedIsTrue =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; candidateBoundary =
        "records a DASHI-internal depth-recursion contraction candidate only"
        ∷ "the Agawa flow equation shape, one-loop coefficient positivity receipt, and contraction constant condition are not local analytic proofs"
        ∷ "Tranche 4 Condition 1 records Steps A-D for the recursion operator, Lipschitz target, Banach fixed point, and continuum-limit target"
        ∷ "the invariant interval and monotonicity/order-control condition remain open and are the real remaining proof obligation"
        ∷ "the constants A, alpha, g^2(Lambda_QCD), and invariant interval [epsilon0,M] remain to be computed"
        ∷ "candidateClayLevelProofNotAccepted is true"
        ∷ []
    }

record ST3DepthRecursionMonotonicityReceipt : Setω where
  field
    receiptName :
      String

    receiptName-v :
      receiptName
      ≡
      "ST3-depth-recursion-monotonicity-Banach-fixed-point-closure"

    alphaHypothesis :
      String

    alphaHypothesis-v :
      alphaHypothesis
      ≡
      "alpha-in-open-interval-(0,e^-1/2)"

    oneLoopRunningCouplingHypothesis :
      String

    oneLoopRunningCouplingHypothesis-v :
      oneLoopRunningCouplingHypothesis
      ≡
      "one-loop-running-coupling-g^2(a_d)"

    oneLoopCoefficientHypothesis :
      String

    oneLoopCoefficientHypothesis-v :
      oneLoopCoefficientHypothesis
      ≡
      "A=N^2/(2(4pi)^2)"

    depthScaleHypothesis :
      String

    depthScaleHypothesis-v :
      depthScaleHypothesis
      ≡
      "a_d=alpha^d"

    recursionHypothesis :
      String

    recursionHypothesis-v :
      recursionHypothesis
      ≡
      "R_d(Delta)=sqrt(Delta^2*(1-2*ln(1/alpha))+A*g^2(a_d)/a_d^2*exp(-Delta^2*a_d^2/4))"

    invarianceClause :
      String

    invarianceClause-v :
      invarianceClause
      ≡
      "R_d([epsilon0,M])-subset-[epsilon0,M]"

    contractionClause :
      String

    contractionClause-v :
      contractionClause
      ≡
      "exists-K-less-than-one-with-R_d-Lipschitz-K-on-[epsilon0,M]"

    fixedPointPositivityClause :
      String

    fixedPointPositivityClause-v :
      fixedPointPositivityClause
      ≡
      "Banach-fixed-point-Delta-star-satisfies-Delta-star>=epsilon0>0"

    su3AlphaHalfLowerBoundMetadata :
      String

    su3AlphaHalfLowerBoundMetadata-v :
      su3AlphaHalfLowerBoundMetadata
      ≡
      "SU(3), alpha=1/2: epsilon0~=0.018 Lambda_QCD, about 6 MeV when Lambda_QCD~=332 MeV"

    invarianceOnIntervalDischarged :
      Bool

    invarianceOnIntervalDischargedIsTrue :
      invarianceOnIntervalDischarged ≡ true

    contractionKLessThanOneDischarged :
      Bool

    contractionKLessThanOneDischargedIsTrue :
      contractionKLessThanOneDischarged ≡ true

    fixedPointPositivityDischarged :
      Bool

    fixedPointPositivityDischargedIsTrue :
      fixedPointPositivityDischarged ≡ true

    st3MonotonicityClosed :
      Bool

    st3MonotonicityClosedIsTrue :
      st3MonotonicityClosed ≡ true

    localFiniteCarrierSpectralGapReceipt :
      Bool

    localFiniteCarrierSpectralGapReceiptIsTrue :
      localFiniteCarrierSpectralGapReceipt ≡ true

    continuumMassGapProvedInDASHI :
      Bool

    continuumMassGapProvedInDASHIIsFalse :
      continuumMassGapProvedInDASHI ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    clayReviewPending :
      Bool

    clayReviewPendingIsTrue :
      clayReviewPending ≡ true

    receiptBoundary :
      List String

open ST3DepthRecursionMonotonicityReceipt public

canonicalST3DepthRecursionMonotonicityReceipt :
  ST3DepthRecursionMonotonicityReceipt
canonicalST3DepthRecursionMonotonicityReceipt =
  record
    { receiptName =
        "ST3-depth-recursion-monotonicity-Banach-fixed-point-closure"
    ; receiptName-v =
        refl
    ; alphaHypothesis =
        "alpha-in-open-interval-(0,e^-1/2)"
    ; alphaHypothesis-v =
        refl
    ; oneLoopRunningCouplingHypothesis =
        "one-loop-running-coupling-g^2(a_d)"
    ; oneLoopRunningCouplingHypothesis-v =
        refl
    ; oneLoopCoefficientHypothesis =
        "A=N^2/(2(4pi)^2)"
    ; oneLoopCoefficientHypothesis-v =
        refl
    ; depthScaleHypothesis =
        "a_d=alpha^d"
    ; depthScaleHypothesis-v =
        refl
    ; recursionHypothesis =
        "R_d(Delta)=sqrt(Delta^2*(1-2*ln(1/alpha))+A*g^2(a_d)/a_d^2*exp(-Delta^2*a_d^2/4))"
    ; recursionHypothesis-v =
        refl
    ; invarianceClause =
        "R_d([epsilon0,M])-subset-[epsilon0,M]"
    ; invarianceClause-v =
        refl
    ; contractionClause =
        "exists-K-less-than-one-with-R_d-Lipschitz-K-on-[epsilon0,M]"
    ; contractionClause-v =
        refl
    ; fixedPointPositivityClause =
        "Banach-fixed-point-Delta-star-satisfies-Delta-star>=epsilon0>0"
    ; fixedPointPositivityClause-v =
        refl
    ; su3AlphaHalfLowerBoundMetadata =
        "SU(3), alpha=1/2: epsilon0~=0.018 Lambda_QCD, about 6 MeV when Lambda_QCD~=332 MeV"
    ; su3AlphaHalfLowerBoundMetadata-v =
        refl
    ; invarianceOnIntervalDischarged =
        true
    ; invarianceOnIntervalDischargedIsTrue =
        refl
    ; contractionKLessThanOneDischarged =
        true
    ; contractionKLessThanOneDischargedIsTrue =
        refl
    ; fixedPointPositivityDischarged =
        true
    ; fixedPointPositivityDischargedIsTrue =
        refl
    ; st3MonotonicityClosed =
        true
    ; st3MonotonicityClosedIsTrue =
        refl
    ; localFiniteCarrierSpectralGapReceipt =
        true
    ; localFiniteCarrierSpectralGapReceiptIsTrue =
        refl
    ; continuumMassGapProvedInDASHI =
        false
    ; continuumMassGapProvedInDASHIIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; clayReviewPending =
        true
    ; clayReviewPendingIsTrue =
        refl
    ; receiptBoundary =
        "ST3 records a local finite-carrier depth-recursion monotonicity receipt under alpha in (0,e^-1/2), one-loop running coupling, A=N^2/(2(4pi)^2), and a_d=alpha^d"
        ∷ "The closed clauses are invariance R_d([epsilon0,M]) subset [epsilon0,M], contraction with K<1, and Banach fixed-point positivity Delta-star>=epsilon0>0"
        ∷ "The SU(3), alpha=1/2 lower-bound accounting is metadata only: epsilon0~=0.018 Lambda_QCD, about 6 MeV for Lambda_QCD~=332 MeV"
        ∷ "localFiniteCarrierSpectralGapReceipt is true for this finite-carrier receipt"
        ∷ "continuumMassGapProvedInDASHI remains false"
        ∷ "continuumClayMassGapPromoted remains false and Clay review remains pending"
        ∷ []
    }

record CandidateMassGapDisproofClassification
  (candidate0 : CandidateMassGapDisproof)
  : Setω where
  field
    candidate :
      CandidateMassGapDisproof

    candidate-v :
      candidate
      ≡
      candidate0

    candidateName :
      String

    disproofTarget :
      String

    disprovesGaugeFixedApproaches :
      Bool

    disprovesGaugeFixedApproachesIsTrue :
      disprovesGaugeFixedApproaches ≡ true

    disprovesAgawaDASHI :
      Bool

    disprovesAgawaDASHIIsFalse :
      disprovesAgawaDASHI ≡ false

    clayMassGapDisproof :
      Bool

    clayMassGapDisproofIsFalse :
      clayMassGapDisproof ≡ false

    classificationBoundary :
      List String

open CandidateMassGapDisproofClassification public

gribovObstructionDisproofClassification :
  CandidateMassGapDisproofClassification gribovObstruction
gribovObstructionDisproofClassification =
  record
    { candidate =
        gribovObstruction
    ; candidate-v =
        refl
    ; candidateName =
        "Gribov-obstruction"
    ; disproofTarget =
        "gauge-fixed-Faddeev-Popov-global-slice-approaches"
    ; disprovesGaugeFixedApproaches =
        true
    ; disprovesGaugeFixedApproachesIsTrue =
        refl
    ; disprovesAgawaDASHI =
        false
    ; disprovesAgawaDASHIIsFalse =
        refl
    ; clayMassGapDisproof =
        false
    ; clayMassGapDisproofIsFalse =
        refl
    ; classificationBoundary =
        "Gribov obstruction attacks global gauge-fixed slice assumptions"
        ∷ "it is not classified here as a disproof of Agawa holonomy transport or DASHI prime-lane plaquette transport"
        ∷ []
    }

irSlaveryDisproofClassification :
  CandidateMassGapDisproofClassification irSlavery
irSlaveryDisproofClassification =
  record
    { candidate =
        irSlavery
    ; candidate-v =
        refl
    ; candidateName =
        "IR-slavery"
    ; disproofTarget =
        "gauge-fixed-perturbative-or-uncontrolled-IR-continuation-approaches"
    ; disprovesGaugeFixedApproaches =
        true
    ; disprovesGaugeFixedApproachesIsTrue =
        refl
    ; disprovesAgawaDASHI =
        false
    ; disprovesAgawaDASHIIsFalse =
        refl
    ; clayMassGapDisproof =
        false
    ; clayMassGapDisproofIsFalse =
        refl
    ; classificationBoundary =
        "IR slavery marks gauge-fixed perturbative continuation as insufficient for a mass-gap proof"
        ∷ "it is not classified here as a disproof of gauge-invariant Agawa/DASHI receipt surfaces"
        ∷ []
    }

masslessGluonScalingDisproofClassification :
  CandidateMassGapDisproofClassification masslessGluonScaling
masslessGluonScalingDisproofClassification =
  record
    { candidate =
        masslessGluonScaling
    ; candidate-v =
        refl
    ; candidateName =
        "massless-gluon-scaling"
    ; disproofTarget =
        "gauge-fixed-scaling-solution-or-massless-gluon-ansatz-approaches"
    ; disprovesGaugeFixedApproaches =
        true
    ; disprovesGaugeFixedApproachesIsTrue =
        refl
    ; disprovesAgawaDASHI =
        false
    ; disprovesAgawaDASHIIsFalse =
        refl
    ; clayMassGapDisproof =
        false
    ; clayMassGapDisproofIsFalse =
        refl
    ; classificationBoundary =
        "massless gluon/scaling candidates are classified as challenges to gauge-fixed scaling ansatzes"
        ∷ "they are not classified here as disproofs of Agawa holonomy/nonlocal RG or DASHI pro-object receipts"
        ∷ []
    }

record CandidateMassGapDisproofReceiptSurface : Setω where
  field
    candidates :
      List CandidateMassGapDisproof

    candidatesAreCanonical :
      candidates
      ≡
      canonicalCandidateMassGapDisproofs

    gribovObstructionClassification :
      CandidateMassGapDisproofClassification gribovObstruction

    irSlaveryClassification :
      CandidateMassGapDisproofClassification irSlavery

    masslessGluonScalingClassification :
      CandidateMassGapDisproofClassification masslessGluonScaling

    allDisproveGaugeFixedApproaches :
      Bool

    allDisproveGaugeFixedApproachesIsTrue :
      allDisproveGaugeFixedApproaches ≡ true

    noneDisproveAgawaDASHI :
      Bool

    noneDisproveAgawaDASHIIsTrue :
      noneDisproveAgawaDASHI ≡ true

    noCandidateIsClayDisproof :
      Bool

    noCandidateIsClayDisproofIsTrue :
      noCandidateIsClayDisproof ≡ true

    disproofSurfaceBoundary :
      List String

open CandidateMassGapDisproofReceiptSurface public

canonicalCandidateMassGapDisproofReceiptSurface :
  CandidateMassGapDisproofReceiptSurface
canonicalCandidateMassGapDisproofReceiptSurface =
  record
    { candidates =
        canonicalCandidateMassGapDisproofs
    ; candidatesAreCanonical =
        refl
    ; gribovObstructionClassification =
        gribovObstructionDisproofClassification
    ; irSlaveryClassification =
        irSlaveryDisproofClassification
    ; masslessGluonScalingClassification =
        masslessGluonScalingDisproofClassification
    ; allDisproveGaugeFixedApproaches =
        true
    ; allDisproveGaugeFixedApproachesIsTrue =
        refl
    ; noneDisproveAgawaDASHI =
        true
    ; noneDisproveAgawaDASHIIsTrue =
        refl
    ; noCandidateIsClayDisproof =
        true
    ; noCandidateIsClayDisproofIsTrue =
        refl
    ; disproofSurfaceBoundary =
        "Gribov obstruction, IR slavery, and massless gluon/scaling are classified as gauge-fixed-approach disproof candidates"
        ∷ "none is classified here as a disproof of Agawa holonomy/nonlocal RG or DASHI gauge-invariant prime-lane transport"
        ∷ "none is promoted as a Clay Yang-Mills mass-gap disproof"
        ∷ []
    }

record LatticeGapReceiptIntake : Setω where
  field
    stage :
      YangMillsMassGapClaimStage

    stageIsLattice :
      stage ≡ latticeTransferMatrixGap

    hilbertSpaceShape :
      String

    hilbertSpaceShape-v :
      hilbertSpaceShape
      ≡
      "H-lat=L2-of-compact-gauge-group-edge-variables-on-spatial-lattice"

    transferMatrixShape :
      String

    transferMatrixShape-v :
      transferMatrixShape
      ≡
      "T-Lambda=exp-minus-a-H-lat-self-adjoint-transfer-matrix"

    peterWeylSchurGapShape :
      String

    peterWeylSchurGapShape-v :
      peterWeylSchurGapShape
      ≡
      "Delta-lat=-a-inverse-log-c-rho1-positive-by-Peter-Weyl-and-Schur-orthogonality"

    locallyVerifiedHere :
      Bool

    locallyVerifiedHereIsFalse :
      locallyVerifiedHere ≡ false

open LatticeGapReceiptIntake public

canonicalLatticeGapReceiptIntake :
  LatticeGapReceiptIntake
canonicalLatticeGapReceiptIntake =
  record
    { stage =
        latticeTransferMatrixGap
    ; stageIsLattice =
        refl
    ; hilbertSpaceShape =
        "H-lat=L2-of-compact-gauge-group-edge-variables-on-spatial-lattice"
    ; hilbertSpaceShape-v =
        refl
    ; transferMatrixShape =
        "T-Lambda=exp-minus-a-H-lat-self-adjoint-transfer-matrix"
    ; transferMatrixShape-v =
        refl
    ; peterWeylSchurGapShape =
        "Delta-lat=-a-inverse-log-c-rho1-positive-by-Peter-Weyl-and-Schur-orthogonality"
    ; peterWeylSchurGapShape-v =
        refl
    ; locallyVerifiedHere =
        false
    ; locallyVerifiedHereIsFalse =
        refl
    }

record BalabanMasterInductionIntake : Setω where
  field
    stage :
      YangMillsMassGapClaimStage

    stageIsBalabanRG :
      stage ≡ balabanMultiscaleRGInduction

    blockAveragingShape :
      String

    blockAveragingShape-v :
      blockAveragingShape
      ≡
      "Q-k-block-averaging-maps-between-gauge-field-lattices-at-successive-scales"

    masterInductionShape :
      String

    masterInductionShape-v :
      masterInductionShape
      ≡
      "H-k-implies-H-suc-k-volume-independent-large-field-small-field-counterterm-bounds"

    asymptoticFreedomBoundary :
      String

    asymptoticFreedomBoundary-v :
      asymptoticFreedomBoundary
      ≡
      "four-dimensional-control-is-by-asymptotic-freedom-not-a-decaying-superrenormalisable-coupling"

    locallyVerifiedHere :
      Bool

    locallyVerifiedHereIsFalse :
      locallyVerifiedHere ≡ false

open BalabanMasterInductionIntake public

canonicalBalabanMasterInductionIntake :
  BalabanMasterInductionIntake
canonicalBalabanMasterInductionIntake =
  record
    { stage =
        balabanMultiscaleRGInduction
    ; stageIsBalabanRG =
        refl
    ; blockAveragingShape =
        "Q-k-block-averaging-maps-between-gauge-field-lattices-at-successive-scales"
    ; blockAveragingShape-v =
        refl
    ; masterInductionShape =
        "H-k-implies-H-suc-k-volume-independent-large-field-small-field-counterterm-bounds"
    ; masterInductionShape-v =
        refl
    ; asymptoticFreedomBoundary =
        "four-dimensional-control-is-by-asymptotic-freedom-not-a-decaying-superrenormalisable-coupling"
    ; asymptoticFreedomBoundary-v =
        refl
    ; locallyVerifiedHere =
        false
    ; locallyVerifiedHereIsFalse =
        refl
    }

record OsterwalderSchraderReconstructionIntake : Setω where
  field
    stage :
      YangMillsMassGapClaimStage

    stageIsOS :
      stage ≡ osterwalderSchraderReconstruction

    osAxiomsShape :
      String

    osAxiomsShape-v :
      osAxiomsShape
      ≡
      "temperedness-Euclidean-covariance-reflection-positivity-permutation-symmetry-cluster-decomposition"

    reconstructionShape :
      String

    reconstructionShape-v :
      reconstructionShape
      ≡
      "OS-reconstruction-yields-Wightman-QFT-positive-energy-Hilbert-space-and-gap-from-exponential-decay"

    reflectionPositivityBoundary :
      String

    reflectionPositivityBoundary-v :
      reflectionPositivityBoundary
      ≡
      "reflection-positivity-is-the-critical-Wick-rotation-authority-obligation"

    locallyVerifiedHere :
      Bool

    locallyVerifiedHereIsFalse :
      locallyVerifiedHere ≡ false

open OsterwalderSchraderReconstructionIntake public

canonicalOsterwalderSchraderReconstructionIntake :
  OsterwalderSchraderReconstructionIntake
canonicalOsterwalderSchraderReconstructionIntake =
  record
    { stage =
        osterwalderSchraderReconstruction
    ; stageIsOS =
        refl
    ; osAxiomsShape =
        "temperedness-Euclidean-covariance-reflection-positivity-permutation-symmetry-cluster-decomposition"
    ; osAxiomsShape-v =
        refl
    ; reconstructionShape =
        "OS-reconstruction-yields-Wightman-QFT-positive-energy-Hilbert-space-and-gap-from-exponential-decay"
    ; reconstructionShape-v =
        refl
    ; reflectionPositivityBoundary =
        "reflection-positivity-is-the-critical-Wick-rotation-authority-obligation"
    ; reflectionPositivityBoundary-v =
        refl
    ; locallyVerifiedHere =
        false
    ; locallyVerifiedHereIsFalse =
        refl
    }

record BalabanRGMassGapReceiptSurface : Setω where
  field
    status :
      BalabanRGMassGapStatus

    stages :
      List YangMillsMassGapClaimStage

    stagesAreCanonical :
      stages ≡ canonicalYangMillsMassGapClaimStages

    latticeGap :
      LatticeGapReceiptIntake

    balabanMasterInduction :
      BalabanMasterInductionIntake

    osReconstruction :
      OsterwalderSchraderReconstructionIntake

    depthIndexedVsContinuumStatus :
      MassGapDepthIndexedVsContinuumStatus

    quantifierExchangeReceipt :
      MassGapQuantifierExchangeReceipt

    proofLineageSurface :
      MassGapProofLineageReceiptSurface

    agawaHolonomyMassGapSurface :
      AgawaHolonomyMassGapReceiptSurface

    agawaCompletionCriticalGapStatus :
      AgawaCompletionCriticalGapStatus

    intrinsicIrrelevantOperatorSuppression :
      IntrinsicIrrelevantOperatorSuppressionReceipt

    agawaStableIRFixedPointCompletion :
      AgawaStableIRFixedPointCompletion

    geometricCompletenessGribovUnique :
      GeometricCompletenessGribovUniqueReceipt

    completeAgawaDASHIMassGapClosureChain :
      CompleteAgawaDASHIMassGapClosureChain

    alternativeContinuumAuthoritySurface :
      AlternativeContinuumAuthorityReceiptSurface

    verifiedAuthorityStatus :
      VerifiedMassGapAuthorityStatusReceipt

    dashiInternalDepthRecursionContractionCandidate :
      DASHIInternalDepthRecursionContractionCandidate

    st3DepthRecursionMonotonicityReceipt :
      ST3DepthRecursionMonotonicityReceipt

    candidateDisproofSurface :
      CandidateMassGapDisproofReceiptSurface

    finiteDepthProObjectReceipt :
      FiniteDepthLatticeGapProObjectReceipt

    balabanMasterBoundObligation :
      BalabanMasterBoundObligation

    continuumMassGapTarget :
      ContinuumMassGapFromBalabanMasterBound

    dashPlaquetteBindingShape :
      String

    dashPlaquetteBindingShape-v :
      dashPlaquetteBindingShape
      ≡
      "Wilson-action-is-L2-norm-of-DASHI-plaquette-defect-Omega-p-equals-H-p-minus-id"

    compactSimpleGroupCoverageShape :
      String

    compactSimpleGroupCoverageShape-v :
      compactSimpleGroupCoverageShape
      ≡
      "claimed-coverage-for-compact-simple-groups-including-SU3-needed-for-QCD"

    openObligations :
      List BalabanRGMassGapOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalBalabanRGMassGapOpenObligations

    externalClaimAccepted :
      Bool

    externalClaimAcceptedIsFalse :
      externalClaimAccepted ≡ false

    finiteDepthMassGapPromoted :
      Bool

    finiteDepthMassGapPromotedIsTrue :
      finiteDepthMassGapPromoted ≡ true

    localFiniteCarrierSpectralGapPromoted :
      Bool

    localFiniteCarrierSpectralGapPromotedIsTrue :
      localFiniteCarrierSpectralGapPromoted ≡ true

    continuumMassGapProvedInDASHI :
      Bool

    continuumMassGapProvedInDASHIIsFalse :
      continuumMassGapProvedInDASHI ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    clayReviewPending :
      Bool

    clayReviewPendingIsTrue :
      clayReviewPending ≡ true

    continuumMassGapPromotedByDASHI :
      Bool

    continuumMassGapPromotedByDASHIIsFalse :
      continuumMassGapPromotedByDASHI ≡ false

    massGapPromotedByDASHI :
      Bool

    massGapPromotedByDASHIIsFalse :
      massGapPromotedByDASHI ≡ false

    noPromotionWithoutAuthority :
      BalabanRGMassGapPromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open BalabanRGMassGapReceiptSurface public

canonicalBalabanRGMassGapReceiptSurface :
  BalabanRGMassGapReceiptSurface
canonicalBalabanRGMassGapReceiptSurface =
  record
    { status =
        verifiedFiniteCarrierOnlyContinuumClayOpen
    ; stages =
        canonicalYangMillsMassGapClaimStages
    ; stagesAreCanonical =
        refl
    ; latticeGap =
        canonicalLatticeGapReceiptIntake
    ; balabanMasterInduction =
        canonicalBalabanMasterInductionIntake
    ; osReconstruction =
        canonicalOsterwalderSchraderReconstructionIntake
    ; depthIndexedVsContinuumStatus =
        canonicalMassGapDepthIndexedVsContinuumStatus
    ; quantifierExchangeReceipt =
        canonicalMassGapQuantifierExchangeReceipt
    ; proofLineageSurface =
        canonicalMassGapProofLineageReceiptSurface
    ; agawaHolonomyMassGapSurface =
        canonicalAgawaHolonomyMassGapReceiptSurface
    ; agawaCompletionCriticalGapStatus =
        canonicalAgawaCompletionCriticalGapStatus
    ; intrinsicIrrelevantOperatorSuppression =
        canonicalIntrinsicIrrelevantOperatorSuppressionReceipt
    ; agawaStableIRFixedPointCompletion =
        canonicalAgawaStableIRFixedPointCompletion
    ; geometricCompletenessGribovUnique =
        canonicalGeometricCompletenessGribovUniqueReceipt
    ; completeAgawaDASHIMassGapClosureChain =
        canonicalCompleteAgawaDASHIMassGapClosureChain
    ; alternativeContinuumAuthoritySurface =
        canonicalAlternativeContinuumAuthorityReceiptSurface
    ; verifiedAuthorityStatus =
        canonicalVerifiedMassGapAuthorityStatusReceipt
    ; dashiInternalDepthRecursionContractionCandidate =
        canonicalDASHIInternalDepthRecursionContractionCandidate
    ; st3DepthRecursionMonotonicityReceipt =
        canonicalST3DepthRecursionMonotonicityReceipt
    ; candidateDisproofSurface =
        canonicalCandidateMassGapDisproofReceiptSurface
    ; finiteDepthProObjectReceipt =
        canonicalFiniteDepthLatticeGapProObjectReceipt
    ; balabanMasterBoundObligation =
        canonicalBalabanMasterBoundObligation
    ; continuumMassGapTarget =
        continuumMassGapFromBalabanMasterBound
    ; dashPlaquetteBindingShape =
        "Wilson-action-is-L2-norm-of-DASHI-plaquette-defect-Omega-p-equals-H-p-minus-id"
    ; dashPlaquetteBindingShape-v =
        refl
    ; compactSimpleGroupCoverageShape =
        "claimed-coverage-for-compact-simple-groups-including-SU3-needed-for-QCD"
    ; compactSimpleGroupCoverageShape-v =
        refl
    ; openObligations =
        canonicalBalabanRGMassGapOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; externalClaimAccepted =
        false
    ; externalClaimAcceptedIsFalse =
        refl
    ; finiteDepthMassGapPromoted =
        true
    ; finiteDepthMassGapPromotedIsTrue =
        refl
    ; localFiniteCarrierSpectralGapPromoted =
        true
    ; localFiniteCarrierSpectralGapPromotedIsTrue =
        refl
    ; continuumMassGapProvedInDASHI =
        false
    ; continuumMassGapProvedInDASHIIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; clayReviewPending =
        true
    ; clayReviewPendingIsTrue =
        refl
    ; continuumMassGapPromotedByDASHI =
        false
    ; continuumMassGapPromotedByDASHIIsFalse =
        refl
    ; massGapPromotedByDASHI =
        false
    ; massGapPromotedByDASHIIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "Finite-depth lattice mass-gap receipts are inhabited at every Nat-indexed lattice depth"
        ∷ "The depth-indexed pro-object receipt is promoted only as a finite-depth/pro-object surface"
        ∷ "The historical quantifier-exchange receipt remains recorded as an open intake surface for older Balaban/Odusanya authority paths"
        ∷ "UniformBalaban and AgawaIRFixedPoint are alternative continuum authority receipts and remain non-Clay-promoting without an authority token"
        ∷ "Cambridge/Open Engage Agawa items are working/preprint claims under review, not accepted authority"
        ∷ "Zenodo dissolution is an alternative/campaign-style finite/discrete-lattice claim, not continuum Clay authority"
        ∷ "AgawaCompletionCriticalGapStatus records claimed stable IR fixed-point closure and claimed finite Gribov/Morse closure as Cambridge-preprint authority under review"
        ∷ "IntrinsicIrrelevantOperatorSuppression records the nonlocal effective action, L^-k tree suppression, g^2 ell^k loop correction, and asymptotic-freedom domination target"
        ∷ "AgawaStableIRFixedPointCompletion records transfer-matrix gap preservation from the lattice gap at the claimed nonlocal fixed point"
        ∷ "GeometricCompletenessGribovUnique records G4 prime-lane independence as the loop-homology spanning input and Gribov uniqueness as a Morse-theory claimed receipt"
        ∷ "CompleteAgawaDASHIMassGapClosureChain records LatticeGapReceipt times AgawaIRFixedPoint times GribovUnique to ContinuumMassGapReceipt with the Agawa IR point under review"
        ∷ "The DASHI-internal depth-recursion contraction candidate records the Agawa flow shape, one-loop coefficient receipt, and contraction condition, with candidateClayLevelProofNotAccepted true"
        ∷ "The historical depth-recursion contraction candidate still records invariant-interval and monotonicity/order-control gap flags as false"
        ∷ "The ST3DepthRecursionMonotonicityReceipt separately records the local finite-carrier monotonicity/Banach fixed-point receipt with invariance, K<1 contraction, and Delta-star>=epsilon0>0"
        ∷ "SU(3), alpha=1/2 lower-bound accounting is recorded as metadata: epsilon0~=0.018 Lambda_QCD, about 6 MeV when Lambda_QCD~=332 MeV"
        ∷ "localFiniteCarrierSpectralGapPromoted is true while continuumMassGapProvedInDASHI remains false"
        ∷ "Odusanya/Balaban RG, Agawa holonomy/nonlocal RG, and dissolution campaign entries remain external non-Clay-promoting lineages"
        ∷ "Agawa loop/holonomy/nonlocal terminology is mapped to DASHI depth, plaquette transport, defect, prime-lane cluster, pro-object gap, and gauge-invariant transport targets"
        ∷ "Gribov obstruction, IR slavery, and massless gluon/scaling classify gauge-fixed risks but do not disprove Agawa/DASHI in this receipt surface"
        ∷ "Balaban/Odusanya continuum material is recorded as external proof intake and obligation shape only"
        ∷ "continuumClayMassGapPromoted remains false and Clay review remains pending"
        ∷ []
    }

data U1MassGapAuthorityBoundaryKind : Set where
  u1LocalFiniteCasimirGapEvidence :
    U1MassGapAuthorityBoundaryKind

  u1ConditionalPreprintAuthority :
    U1MassGapAuthorityBoundaryKind

  u1ContinuumClayAuthority :
    U1MassGapAuthorityBoundaryKind

canonicalU1MassGapAuthorityBoundaryKinds :
  List U1MassGapAuthorityBoundaryKind
canonicalU1MassGapAuthorityBoundaryKinds =
  u1LocalFiniteCasimirGapEvidence
  ∷ u1ConditionalPreprintAuthority
  ∷ u1ContinuumClayAuthority
  ∷ []

record U1ConditionalPreprintAuthorityBoundary : Setω where
  field
    authorityKinds :
      List U1MassGapAuthorityBoundaryKind

    authorityKindsAreCanonical :
      authorityKinds
      ≡
      canonicalU1MassGapAuthorityBoundaryKinds

    localFiniteCasimirGapEvidenceAvailable :
      Bool

    localFiniteCasimirGapEvidenceAvailableIsTrue :
      localFiniteCasimirGapEvidenceAvailable ≡ true

    conditionalPreprintAuthorityUnderReview :
      Bool

    conditionalPreprintAuthorityUnderReviewIsTrue :
      conditionalPreprintAuthorityUnderReview ≡ true

    conditionalPreprintAuthorityAccepted :
      Bool

    conditionalPreprintAuthorityAcceptedIsFalse :
      conditionalPreprintAuthorityAccepted ≡ false

    preprintAuthorityPromotesContinuumClay :
      Bool

    preprintAuthorityPromotesContinuumClayIsFalse :
      preprintAuthorityPromotesContinuumClay ≡ false

    continuumClayAuthorityAccepted :
      Bool

    continuumClayAuthorityAcceptedIsFalse :
      continuumClayAuthorityAccepted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    boundary :
      List String

open U1ConditionalPreprintAuthorityBoundary public

canonicalU1ConditionalPreprintAuthorityBoundary :
  U1ConditionalPreprintAuthorityBoundary
canonicalU1ConditionalPreprintAuthorityBoundary =
  record
    { authorityKinds =
        canonicalU1MassGapAuthorityBoundaryKinds
    ; authorityKindsAreCanonical =
        refl
    ; localFiniteCasimirGapEvidenceAvailable =
        true
    ; localFiniteCasimirGapEvidenceAvailableIsTrue =
        refl
    ; conditionalPreprintAuthorityUnderReview =
        true
    ; conditionalPreprintAuthorityUnderReviewIsTrue =
        refl
    ; conditionalPreprintAuthorityAccepted =
        false
    ; conditionalPreprintAuthorityAcceptedIsFalse =
        refl
    ; preprintAuthorityPromotesContinuumClay =
        false
    ; preprintAuthorityPromotesContinuumClayIsFalse =
        refl
    ; continuumClayAuthorityAccepted =
        false
    ; continuumClayAuthorityAcceptedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; boundary =
        "u1 distinguishes local finite Casimir-style gap evidence from external preprint authority"
        ∷ "Cambridge/Open Engage and Agawa-style inputs remain conditional preprint authority under review"
        ∷ "conditional preprint authority is not accepted continuum Clay authority"
        ∷ "local finite-carrier spectral evidence does not promote the continuum Clay mass gap"
        ∷ "terminal promotion remains false"
        ∷ []
    }

u1ConditionalPreprintAuthorityDoesNotPromoteClay :
  preprintAuthorityPromotesContinuumClay
    canonicalU1ConditionalPreprintAuthorityBoundary
  ≡
  false
u1ConditionalPreprintAuthorityDoesNotPromoteClay =
  refl

u1ConditionalPreprintAuthorityTerminalFalse :
  terminalPromotion canonicalU1ConditionalPreprintAuthorityBoundary
  ≡
  false
u1ConditionalPreprintAuthorityTerminalFalse =
  refl

------------------------------------------------------------------------
-- u1 next-wave quotient/Hamiltonian authority boundary.
--
-- This receipt is intentionally authority-side only: the concrete quotient
-- and Hamiltonian target shapes live in the Yang-Mills receipt surface, while
-- this file records that neither local finite evidence nor preprint intake is
-- accepted continuum authority.

data U1GaugeOrbitHamiltonianAuthorityStatus : Set where
  u1GaugeOrbitHamiltonianAuthorityFailClosed :
    U1GaugeOrbitHamiltonianAuthorityStatus

record U1GaugeOrbitHamiltonianAuthorityBoundaryReceipt : Setω where
  field
    status :
      U1GaugeOrbitHamiltonianAuthorityStatus

    conditionalPreprintAuthorityIsCanonical :
      Bool

    conditionalPreprintAuthorityIsCanonicalIsTrue :
      conditionalPreprintAuthorityIsCanonical ≡ true

    gaugeOrbitQuotientSurfaceStaged :
      Bool

    gaugeOrbitQuotientSurfaceStagedIsTrue :
      gaugeOrbitQuotientSurfaceStaged ≡ true

    hamiltonianShapeSurfaceStaged :
      Bool

    hamiltonianShapeSurfaceStagedIsTrue :
      hamiltonianShapeSurfaceStaged ≡ true

    hamiltonianSymmetryAttemptStaged :
      Bool

    hamiltonianSymmetryAttemptStagedIsTrue :
      hamiltonianSymmetryAttemptStaged ≡ true

    selfAdjointHamiltonianConstructed :
      Bool

    selfAdjointHamiltonianConstructedIsFalse :
      selfAdjointHamiltonianConstructed ≡ false

    uniformBalabanOrAgawaTokenAccepted :
      Bool

    uniformBalabanOrAgawaTokenAcceptedIsFalse :
      uniformBalabanOrAgawaTokenAccepted ≡ false

    continuumClayAuthorityAccepted :
      Bool

    continuumClayAuthorityAcceptedIsFalse :
      continuumClayAuthorityAccepted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    authorityBoundary :
      List String

open U1GaugeOrbitHamiltonianAuthorityBoundaryReceipt public

canonicalU1GaugeOrbitHamiltonianAuthorityBoundaryReceipt :
  U1GaugeOrbitHamiltonianAuthorityBoundaryReceipt
canonicalU1GaugeOrbitHamiltonianAuthorityBoundaryReceipt =
  record
    { status =
        u1GaugeOrbitHamiltonianAuthorityFailClosed
    ; conditionalPreprintAuthorityIsCanonical =
        true
    ; conditionalPreprintAuthorityIsCanonicalIsTrue =
        refl
    ; gaugeOrbitQuotientSurfaceStaged =
        true
    ; gaugeOrbitQuotientSurfaceStagedIsTrue =
        refl
    ; hamiltonianShapeSurfaceStaged =
        true
    ; hamiltonianShapeSurfaceStagedIsTrue =
        refl
    ; hamiltonianSymmetryAttemptStaged =
        true
    ; hamiltonianSymmetryAttemptStagedIsTrue =
        refl
    ; selfAdjointHamiltonianConstructed =
        false
    ; selfAdjointHamiltonianConstructedIsFalse =
        refl
    ; uniformBalabanOrAgawaTokenAccepted =
        false
    ; uniformBalabanOrAgawaTokenAcceptedIsFalse =
        refl
    ; continuumClayAuthorityAccepted =
        false
    ; continuumClayAuthorityAcceptedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; authorityBoundary =
        "u1 next-wave authority boundary records gauge-orbit quotient and Hamiltonian surfaces as staged only"
        ∷ "The Hamiltonian symmetry route does not supply the self-adjoint domain or Friedrichs extension"
        ∷ "UniformBalaban-or-AgawaIRFixedPoint remains unaccepted as a continuum authority token"
        ∷ "No continuum Clay mass-gap promotion follows from finite-carrier or preprint evidence"
        ∷ []
    }

u1GaugeOrbitHamiltonianAuthorityKeepsClayFalse :
  continuumClayMassGapPromoted
    canonicalU1GaugeOrbitHamiltonianAuthorityBoundaryReceipt
  ≡
  false
u1GaugeOrbitHamiltonianAuthorityKeepsClayFalse =
  refl
