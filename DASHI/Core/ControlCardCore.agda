module DASHI.Core.ControlCardCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Core.AdapterCanonicalityCore as Adapter
import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Core.CandidateOnlyCore as Candidate
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Reusable control-card core.
--
-- This module factors a fail-closed control-card spine with eight slot
-- names and the usual row/surface/receipt layering.  It stays candidate-only,
-- non-promoting, and authority-closed while still providing compatibility
-- names for orchestration-style receipt concepts.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Slot vocabulary.

data ControlCardSlot : Set where
  orchestrationSlot :
    ControlCardSlot

  receiptSlot :
    ControlCardSlot

  candidateSlot :
    ControlCardSlot

  surfaceSlot :
    ControlCardSlot

  lensSlot :
    ControlCardSlot

  promotionSlot :
    ControlCardSlot

  governanceSlot :
    ControlCardSlot

  failClosedSlot :
    ControlCardSlot

  namedControlCardSlot :
    String →
    ControlCardSlot

canonicalControlCardSlots : List ControlCardSlot
canonicalControlCardSlots =
  orchestrationSlot
  ∷ receiptSlot
  ∷ candidateSlot
  ∷ surfaceSlot
  ∷ lensSlot
  ∷ promotionSlot
  ∷ governanceSlot
  ∷ failClosedSlot
  ∷ []

canonicalControlCardSlotCount : Nat
canonicalControlCardSlotCount =
  listCount canonicalControlCardSlots

------------------------------------------------------------------------
-- Control-card row.

record ControlCardRow : Set where
  constructor controlCardRow
  field
    rowLabel :
      String

    rowOwner :
      String

    rowSurface :
      String

    rowSlot :
      ControlCardSlot

    rowStatement :
      String

    rowRemainingGap :
      String

    candidateOnly :
      Bool

    promoted :
      Bool

    lensAuthority :
      Bool

    truthAuthority :
      Bool

    supportAuthority :
      Bool

    admissibilityAuthority :
      Bool

    tradingAuthority :
      Bool

    runtimeAuthority :
      Bool

    theoremAuthority :
      Bool

    governanceAuthority :
      Bool

    promotionAuthority :
      Bool

open ControlCardRow public

record ControlCardRowReceipt
  (row : ControlCardRow) :
  Set where
  constructor controlCardRowReceipt
  field
    rowCandidateOnlyIsTrue :
      candidateOnly row ≡ true

    rowPromotedIsFalse :
      promoted row ≡ false

    rowLensAuthorityIsFalse :
      lensAuthority row ≡ false

    rowTruthAuthorityIsFalse :
      truthAuthority row ≡ false

    rowSupportAuthorityIsFalse :
      supportAuthority row ≡ false

    rowAdmissibilityAuthorityIsFalse :
      admissibilityAuthority row ≡ false

    rowTradingAuthorityIsFalse :
      tradingAuthority row ≡ false

    rowRuntimeAuthorityIsFalse :
      runtimeAuthority row ≡ false

    rowTheoremAuthorityIsFalse :
      theoremAuthority row ≡ false

    rowGovernanceAuthorityIsFalse :
      governanceAuthority row ≡ false

    rowPromotionAuthorityIsFalse :
      promotionAuthority row ≡ false

open ControlCardRowReceipt public

mkControlCardRow :
  String →
  String →
  String →
  ControlCardSlot →
  String →
  String →
  ControlCardRow
mkControlCardRow
  label
  owner
  surface
  slot
  statement
  remainingGap =
  controlCardRow
    label
    owner
    surface
    slot
    statement
    remainingGap
    true
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false

mkControlCardRowReceipt :
  (row : ControlCardRow) →
  candidateOnly row ≡ true →
  promoted row ≡ false →
  lensAuthority row ≡ false →
  truthAuthority row ≡ false →
  supportAuthority row ≡ false →
  admissibilityAuthority row ≡ false →
  tradingAuthority row ≡ false →
  runtimeAuthority row ≡ false →
  theoremAuthority row ≡ false →
  governanceAuthority row ≡ false →
  promotionAuthority row ≡ false →
  ControlCardRowReceipt row
mkControlCardRowReceipt
  row
  candidateOnlyProof
  promotedProof
  lensProof
  truthProof
  supportProof
  admissibilityProof
  tradingProof
  runtimeProof
  theoremProof
  governanceProof
  promotionProof =
  controlCardRowReceipt
    candidateOnlyProof
    promotedProof
    lensProof
    truthProof
    supportProof
    admissibilityProof
    tradingProof
    runtimeProof
    theoremProof
    governanceProof
    promotionProof

mkCanonicalControlCardRowReceipt :
  (row : ControlCardRow) →
  candidateOnly row ≡ true →
  promoted row ≡ false →
  lensAuthority row ≡ false →
  truthAuthority row ≡ false →
  supportAuthority row ≡ false →
  admissibilityAuthority row ≡ false →
  tradingAuthority row ≡ false →
  runtimeAuthority row ≡ false →
  theoremAuthority row ≡ false →
  governanceAuthority row ≡ false →
  promotionAuthority row ≡ false →
  ControlCardRowReceipt row
mkCanonicalControlCardRowReceipt =
  mkControlCardRowReceipt

------------------------------------------------------------------------
-- Control-card surface.

record ControlCardSurface : Set where
  constructor controlCardSurface
  field
    surfaceLabel :
      String

    surfaceOwner :
      String

    surfaceSurface :
      String

    surfaceValidationCommand :
      String

    surfaceControlSlot :
      ControlCardSlot

    surfaceRow :
      ControlCardRow

    surfaceRowReceipt :
      ControlCardRowReceipt surfaceRow

    surfaceCandidateRow :
      Candidate.CandidateOnlyRow

    surfaceCandidateReceipt :
      Candidate.CandidateOnlyReceipt surfaceCandidateRow

    surfaceAuthorityBundle :
      Authority.AuthorityNonPromotionBundle

    surfaceCandidateAdapter :
      Adapter.AdapterCanonicalityReceipt
        Candidate.CandidateOnlyRow
        Candidate.canonicalRowCandidateOnlyRow

    surfaceAuthorityAdapter :
      Adapter.AdapterCanonicalityReceipt
        Authority.AuthorityNonPromotionBundle
        Authority.canonicalAuthorityNonPromotionBundle

    surfaceAdapterAdapter :
      Adapter.AdapterCanonicalityReceipt
        Adapter.AdapterSurface
        Adapter.canonicalAdapter

    surfaceStatement :
      String

    surfaceRemainingGap :
      String

open ControlCardSurface public

------------------------------------------------------------------------
-- Generic receipt adapter.

controlCardGenericReceipt :
  ControlCardSurface →
  GenericReceipt.GenericReceipt
controlCardGenericReceipt surface =
  GenericReceipt.mkNonPromotingReceipt
    (surfaceLabel surface)
    (surfaceOwner surface)
    (surfaceSurface surface)
    (surfaceStatement surface)
    (surfaceRemainingGap surface)
    (surfaceValidationCommand surface)

record ControlCardSurfaceReceipt
  (surface : ControlCardSurface) :
  Set where
  constructor controlCardSurfaceReceipt
  field
    surfaceRowReceiptCanonical :
      ControlCardRowReceipt (surfaceRow surface)

    surfaceCandidateOnlyIsTrue :
      candidateOnly (surfaceRow surface) ≡ true

    surfacePromotedIsFalse :
      promoted (surfaceRow surface) ≡ false

    surfaceLensAuthorityIsFalse :
      lensAuthority (surfaceRow surface) ≡ false

    surfaceTruthAuthorityIsFalse :
      truthAuthority (surfaceRow surface) ≡ false

    surfaceSupportAuthorityIsFalse :
      supportAuthority (surfaceRow surface) ≡ false

    surfaceAdmissibilityAuthorityIsFalse :
      admissibilityAuthority (surfaceRow surface) ≡ false

    surfaceTradingAuthorityIsFalse :
      tradingAuthority (surfaceRow surface) ≡ false

    surfaceRuntimeAuthorityIsFalse :
      runtimeAuthority (surfaceRow surface) ≡ false

    surfaceTheoremAuthorityIsFalse :
      theoremAuthority (surfaceRow surface) ≡ false

    surfaceGovernanceAuthorityIsFalse :
      governanceAuthority (surfaceRow surface) ≡ false

    surfacePromotionAuthorityIsFalse :
      promotionAuthority (surfaceRow surface) ≡ false

    surfaceCandidateReceiptCanonical :
      Candidate.CandidateOnlyReceipt (surfaceCandidateRow surface)

    surfaceAuthorityBundleNonPromoting :
      Authority.promotesAnyAuthority (surfaceAuthorityBundle surface)
      ≡
      false

    surfaceCandidateAdapterCanonical :
      Adapter.adapter (surfaceCandidateAdapter surface)
      ≡
      Candidate.canonicalRowCandidateOnlyRow

    surfaceAuthorityAdapterCanonical :
      Adapter.adapter (surfaceAuthorityAdapter surface)
      ≡
      Authority.canonicalAuthorityNonPromotionBundle

    surfaceAdapterAdapterCanonical :
      Adapter.adapter (surfaceAdapterAdapter surface)
      ≡
      Adapter.canonicalAdapter

    surfaceGenericReceiptNonPromoting :
      GenericReceipt.promotesClaim (controlCardGenericReceipt surface)
      ≡
      false

open ControlCardSurfaceReceipt public

mkControlCardSurface :
  String →
  String →
  String →
  String →
  ControlCardSlot →
  (row : ControlCardRow) →
  ControlCardRowReceipt row →
  (candidateRow : Candidate.CandidateOnlyRow) →
  Candidate.CandidateOnlyReceipt candidateRow →
  (authorityBundle : Authority.AuthorityNonPromotionBundle) →
  Adapter.AdapterCanonicalityReceipt
    Candidate.CandidateOnlyRow
    Candidate.canonicalRowCandidateOnlyRow →
  Adapter.AdapterCanonicalityReceipt
    Authority.AuthorityNonPromotionBundle
    Authority.canonicalAuthorityNonPromotionBundle →
  Adapter.AdapterCanonicalityReceipt
    Adapter.AdapterSurface
    Adapter.canonicalAdapter →
  String →
  String →
  ControlCardSurface
mkControlCardSurface
  label
  owner
  surface
  validationCommand
  slot
  row
  rowReceipt
  candidateRow
  candidateReceipt
  authorityBundle
  candidateAdapter
  authorityAdapter
  adapterAdapter
  statement
  remainingGap =
  controlCardSurface
    label
    owner
    surface
    validationCommand
    slot
    row
    rowReceipt
    candidateRow
    candidateReceipt
    authorityBundle
    candidateAdapter
    authorityAdapter
    adapterAdapter
    statement
    remainingGap

mkControlCardSurfaceReceipt :
  (surface : ControlCardSurface) →
  ControlCardRowReceipt (surfaceRow surface) →
  candidateOnly (surfaceRow surface) ≡ true →
  promoted (surfaceRow surface) ≡ false →
  lensAuthority (surfaceRow surface) ≡ false →
  truthAuthority (surfaceRow surface) ≡ false →
  supportAuthority (surfaceRow surface) ≡ false →
  admissibilityAuthority (surfaceRow surface) ≡ false →
  tradingAuthority (surfaceRow surface) ≡ false →
  runtimeAuthority (surfaceRow surface) ≡ false →
  theoremAuthority (surfaceRow surface) ≡ false →
  governanceAuthority (surfaceRow surface) ≡ false →
  promotionAuthority (surfaceRow surface) ≡ false →
  Candidate.CandidateOnlyReceipt (surfaceCandidateRow surface) →
  Authority.promotesAnyAuthority (surfaceAuthorityBundle surface) ≡ false →
  Adapter.adapter (surfaceCandidateAdapter surface)
    ≡
    Candidate.canonicalRowCandidateOnlyRow →
  Adapter.adapter (surfaceAuthorityAdapter surface)
    ≡
    Authority.canonicalAuthorityNonPromotionBundle →
  Adapter.adapter (surfaceAdapterAdapter surface)
    ≡
    Adapter.canonicalAdapter →
  GenericReceipt.promotesClaim (controlCardGenericReceipt surface)
    ≡
    false →
  ControlCardSurfaceReceipt surface
mkControlCardSurfaceReceipt
  surface
  rowReceipt
  candidateOnlyProof
  promotedProof
  lensProof
  truthProof
  supportProof
  admissibilityProof
  tradingProof
  runtimeProof
  theoremProof
  governanceProof
  promotionProof
  candidateReceiptProof
  authorityProof
  candidateAdapterProof
  authorityAdapterProof
  adapterAdapterProof
  genericReceiptProof =
  controlCardSurfaceReceipt
    rowReceipt
    candidateOnlyProof
    promotedProof
    lensProof
    truthProof
    supportProof
    admissibilityProof
    tradingProof
    runtimeProof
    theoremProof
    governanceProof
    promotionProof
    candidateReceiptProof
    authorityProof
    candidateAdapterProof
    authorityAdapterProof
    adapterAdapterProof
    genericReceiptProof

canonicalControlCardCandidateAdapter :
  Adapter.AdapterCanonicalityReceipt
    Candidate.CandidateOnlyRow
    Candidate.canonicalRowCandidateOnlyRow
canonicalControlCardCandidateAdapter =
  Adapter.mkCanonicalAdapterReceipt
    "control-card candidate adapter"
    "DASHI.Core.ControlCardCore"
    "surface candidate row"
    Adapter.genericAdapterKind
    Candidate.canonicalRowCandidateOnlyRow

canonicalControlCardAuthorityAdapter :
  Adapter.AdapterCanonicalityReceipt
    Authority.AuthorityNonPromotionBundle
    Authority.canonicalAuthorityNonPromotionBundle
canonicalControlCardAuthorityAdapter =
  Adapter.mkCanonicalAdapterReceipt
    "control-card authority adapter"
    "DASHI.Core.ControlCardCore"
    "surface authority bundle"
    Adapter.authorityAdapterKind
    Authority.canonicalAuthorityNonPromotionBundle

canonicalControlCardAdapterAdapter :
  Adapter.AdapterCanonicalityReceipt
    Adapter.AdapterSurface
    Adapter.canonicalAdapter
canonicalControlCardAdapterAdapter =
  Adapter.mkCanonicalAdapterReceipt
    "control-card adapter adapter"
    "DASHI.Core.ControlCardCore"
    "adapter canonical surface"
    Adapter.receiptAdapterKind
    Adapter.canonicalAdapter

------------------------------------------------------------------------
-- Compatibility names for orchestration receipt concepts.

ControlCardOrchestrationRow : Set
ControlCardOrchestrationRow =
  ControlCardRow

ControlCardOrchestrationSurface : Set
ControlCardOrchestrationSurface =
  ControlCardSurface

ControlCardOrchestrationReceipt :
  (surface : ControlCardSurface) →
  Set
ControlCardOrchestrationReceipt =
  ControlCardSurfaceReceipt

orchestrationReceiptCandidateOnlyIsTrue :
  {surface : ControlCardSurface} →
  ControlCardSurfaceReceipt surface →
  candidateOnly (surfaceRow surface) ≡ true
orchestrationReceiptCandidateOnlyIsTrue receipt =
  surfaceCandidateOnlyIsTrue receipt

orchestrationReceiptPromotedIsFalse :
  {surface : ControlCardSurface} →
  ControlCardSurfaceReceipt surface →
  promoted (surfaceRow surface) ≡ false
orchestrationReceiptPromotedIsFalse receipt =
  surfacePromotedIsFalse receipt

orchestrationReceiptNonPromoting :
  {surface : ControlCardSurface} →
  ControlCardSurfaceReceipt surface →
  GenericReceipt.promotesClaim (controlCardGenericReceipt surface)
  ≡
  false
orchestrationReceiptNonPromoting receipt =
  surfaceGenericReceiptNonPromoting receipt

orchestrationReceiptAuthorityClosed :
  {surface : ControlCardSurface} →
  ControlCardSurfaceReceipt surface →
  Authority.promotesAnyAuthority (surfaceAuthorityBundle surface) ≡ false
orchestrationReceiptAuthorityClosed receipt =
  surfaceAuthorityBundleNonPromoting receipt

------------------------------------------------------------------------
-- Canonical control-card rows, surfaces, and receipts.

canonicalControlCardRow :
  ControlCardRow
canonicalControlCardRow =
  mkControlCardRow
    "control-card spine"
    "DASHI.Core.ControlCardCore"
    "canonicalControlCardRow"
    orchestrationSlot
    "control-card rows stay candidate-only and non-promoting across orchestration, receipt, candidate, surface, lens, promotion, governance, and fail-closed slots"
    "downstream modules must still provide any domain-specific acceptance gate separately"

canonicalControlCardRowReceipt :
  ControlCardRowReceipt canonicalControlCardRow
canonicalControlCardRowReceipt =
  controlCardRowReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalControlCardSurface :
  ControlCardSurface
canonicalControlCardSurface =
  mkControlCardSurface
    "control-card spine"
    "DASHI.Core.ControlCardCore"
    "canonicalControlCardSurface"
    "agda -i . DASHI/Core/ControlCardCore.agda"
    orchestrationSlot
    canonicalControlCardRow
    canonicalControlCardRowReceipt
    Candidate.canonicalRowCandidateOnlyRow
    Candidate.canonicalRowCandidateOnlyReceipt
    Authority.canonicalAuthorityNonPromotionBundle
    canonicalControlCardCandidateAdapter
    canonicalControlCardAuthorityAdapter
    canonicalControlCardAdapterAdapter
    "control-card rows and surfaces stay candidate-only, non-promoting, and authority-closed"
    "the top-level orchestration surface remains a compatibility spine only"

canonicalControlCardSurfaceReceipt :
  ControlCardSurfaceReceipt canonicalControlCardSurface
canonicalControlCardSurfaceReceipt =
  controlCardSurfaceReceipt
    canonicalControlCardRowReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    Candidate.canonicalRowCandidateOnlyReceipt
    Authority.canonicalPromotesAnyAuthorityIsFalse
    refl
    refl
    refl
    refl

canonicalControlCardRowCandidateOnlyIsTrue :
  candidateOnly canonicalControlCardRow ≡ true
canonicalControlCardRowCandidateOnlyIsTrue =
  rowCandidateOnlyIsTrue canonicalControlCardRowReceipt

canonicalControlCardRowPromotedIsFalse :
  promoted canonicalControlCardRow ≡ false
canonicalControlCardRowPromotedIsFalse =
  rowPromotedIsFalse canonicalControlCardRowReceipt

canonicalControlCardSurfaceCandidateOnlyIsTrue :
  candidateOnly (surfaceRow canonicalControlCardSurface) ≡ true
canonicalControlCardSurfaceCandidateOnlyIsTrue =
  surfaceCandidateOnlyIsTrue canonicalControlCardSurfaceReceipt

canonicalControlCardSurfacePromotedIsFalse :
  promoted (surfaceRow canonicalControlCardSurface) ≡ false
canonicalControlCardSurfacePromotedIsFalse =
  surfacePromotedIsFalse canonicalControlCardSurfaceReceipt

canonicalControlCardSurfaceAuthorityClosed :
  Authority.promotesAnyAuthority (surfaceAuthorityBundle canonicalControlCardSurface)
  ≡
  false
canonicalControlCardSurfaceAuthorityClosed =
  surfaceAuthorityBundleNonPromoting canonicalControlCardSurfaceReceipt

canonicalControlCardGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalControlCardGenericReceipt =
  controlCardGenericReceipt canonicalControlCardSurface

canonicalControlCardGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim canonicalControlCardGenericReceipt ≡ false
canonicalControlCardGenericReceiptNonPromoting =
  refl

canonicalControlCardGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalControlCardGenericReceipts =
  canonicalControlCardGenericReceipt
  ∷ []

canonicalControlCardGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting
    canonicalControlCardGenericReceipts
canonicalControlCardGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalControlCardGenericReceipts
