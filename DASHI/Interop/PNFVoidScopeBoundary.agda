module DASHI.Interop.PNFVoidScopeBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFSpectralFieldCore as Core
import DASHI.Interop.PNFResidualFieldInvariants as Invariants
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- PNF fibre boundary to void/scope receipt surface.
--
-- This module is only a typed receipt surface.  It distinguishes a failed
-- typed meet inside a declared fibre from an outside-comparison/scope
-- boundary.  Neither boundary grants semantic truth, evidential support, or
-- admissibility, and no live political/economic actor classification is made.

data PNFVoidScopeBoundaryStatus : Set where
  comparedInFibre_noTypedMeet :
    PNFVoidScopeBoundaryStatus

  outsideComparison_scopeExceeded :
    PNFVoidScopeBoundaryStatus

  fibreCollapse_scopeExceeded :
    PNFVoidScopeBoundaryStatus

data PNFVoidScopeBoundaryComponent : Set where
  sameFibreNoTypedMeetComponent :
    PNFVoidScopeBoundaryComponent

  outsideComparisonScopeExceededComponent :
    PNFVoidScopeBoundaryComponent

  fibreCollapseScopeExceededComponent :
    PNFVoidScopeBoundaryComponent

  noTruthSupportAdmissibilityPromotionComponent :
    PNFVoidScopeBoundaryComponent

canonicalPNFVoidScopeBoundaryComponents :
  List PNFVoidScopeBoundaryComponent
canonicalPNFVoidScopeBoundaryComponents =
  sameFibreNoTypedMeetComponent
  ∷ outsideComparisonScopeExceededComponent
  ∷ fibreCollapseScopeExceededComponent
  ∷ noTruthSupportAdmissibilityPromotionComponent
  ∷ []

data PNFVoidScopeBoundaryPromotion : Set where

pnfVoidScopeBoundaryPromotionImpossible :
  PNFVoidScopeBoundaryPromotion →
  ⊥
pnfVoidScopeBoundaryPromotionImpossible ()

boundaryStatusPromotesTruth :
  PNFVoidScopeBoundaryStatus →
  Bool
boundaryStatusPromotesTruth _ =
  false

boundaryStatusPromotesSupport :
  PNFVoidScopeBoundaryStatus →
  Bool
boundaryStatusPromotesSupport _ =
  false

boundaryStatusPromotesAdmissibility :
  PNFVoidScopeBoundaryStatus →
  Bool
boundaryStatusPromotesAdmissibility _ =
  false

boundaryStatusTruthGateFalse :
  ∀ status →
  boundaryStatusPromotesTruth status ≡ false
boundaryStatusTruthGateFalse status =
  refl

boundaryStatusSupportGateFalse :
  ∀ status →
  boundaryStatusPromotesSupport status ≡ false
boundaryStatusSupportGateFalse status =
  refl

boundaryStatusAdmissibilityGateFalse :
  ∀ status →
  boundaryStatusPromotesAdmissibility status ≡ false
boundaryStatusAdmissibilityGateFalse status =
  refl

------------------------------------------------------------------------
-- Same-fibre NO_TYPED_MEET: compared in a fibre, no typed meet found.

record NoTypedMeetComparedInFibre : Set where
  constructor noTypedMeetComparedInFibre
  field
    ntmLeftReceipt :
      Residual.PNFEmissionReceipt

    ntmRightReceipt :
      Residual.PNFEmissionReceipt

    ntmFibre :
      Core.FibreRef

    ntmStatus :
      PNFVoidScopeBoundaryStatus

    ntmStatusIsComparedInFibre :
      ntmStatus ≡ comparedInFibre_noTypedMeet

    ntmComparedInsideFibre :
      Bool

    ntmComparedInsideFibreIsTrue :
      ntmComparedInsideFibre ≡ true

    ntmOutsideComparison :
      Bool

    ntmOutsideComparisonIsFalse :
      ntmOutsideComparison ≡ false

    ntmFourLevelResidual :
      Residual.ResidualLevel

    ntmFourLevelResidualIsNoTypedMeet :
      ntmFourLevelResidual ≡ Invariants.NO_TYPED_MEET

    ntmSixLevelResidual :
      Residual.SixResidualLevel

    ntmSixLevelResidualIsNoTypedMeet :
      ntmSixLevelResidual ≡ Residual.noTypedMeet6

    ntmTruthPromotion :
      Bool

    ntmTruthPromotionIsFalse :
      ntmTruthPromotion ≡ false

    ntmSupportPromotion :
      Bool

    ntmSupportPromotionIsFalse :
      ntmSupportPromotion ≡ false

    ntmAdmissibilityPromotion :
      Bool

    ntmAdmissibilityPromotionIsFalse :
      ntmAdmissibilityPromotion ≡ false

------------------------------------------------------------------------
-- Cross-domain SCOPE_EXCEEDED: not compared in the fibre.

record ScopeExceededOutsideComparison : Set where
  constructor scopeExceededOutsideComparison
  field
    scopeLeftReceipt :
      Residual.PNFEmissionReceipt

    scopeRightReceipt :
      Residual.PNFEmissionReceipt

    scopeSourceFibre :
      Core.FibreRef

    scopeTargetFibre :
      Core.FibreRef

    scopeStatus :
      PNFVoidScopeBoundaryStatus

    scopeStatusIsOutsideComparison :
      scopeStatus ≡ outsideComparison_scopeExceeded

    scopeComparedInsideFibre :
      Bool

    scopeComparedInsideFibreIsFalse :
      scopeComparedInsideFibre ≡ false

    scopeOutsideComparison :
      Bool

    scopeOutsideComparisonIsTrue :
      scopeOutsideComparison ≡ true

    scopeSixLevelResidual :
      Residual.SixResidualLevel

    scopeSixLevelResidualIsScopeExceeded :
      scopeSixLevelResidual ≡ Residual.scopeExceeded6

    scopeTruthPromotion :
      Bool

    scopeTruthPromotionIsFalse :
      scopeTruthPromotion ≡ false

    scopeSupportPromotion :
      Bool

    scopeSupportPromotionIsFalse :
      scopeSupportPromotion ≡ false

    scopeAdmissibilityPromotion :
      Bool

    scopeAdmissibilityPromotionIsFalse :
      scopeAdmissibilityPromotion ≡ false

record FibreCollapseBoundary : Set where
  constructor fibreCollapseBoundary
  field
    collapseSourceFibre :
      Core.FibreRef

    collapseTargetFibre :
      Core.FibreRef

    collapseStatus :
      PNFVoidScopeBoundaryStatus

    collapseStatusIsFibreCollapse :
      collapseStatus ≡ fibreCollapse_scopeExceeded

    collapseResidual :
      Residual.SixResidualLevel

    collapseResidualIsScopeExceeded :
      collapseResidual ≡ Residual.scopeExceeded6

    collapseGrantsTruth :
      Bool

    collapseGrantsTruthIsFalse :
      collapseGrantsTruth ≡ false

    collapseGrantsSupport :
      Bool

    collapseGrantsSupportIsFalse :
      collapseGrantsSupport ≡ false

    collapseGrantsAdmissibility :
      Bool

    collapseGrantsAdmissibilityIsFalse :
      collapseGrantsAdmissibility ≡ false

------------------------------------------------------------------------
-- Canonical receipt rows.

canonicalVoidScopePredicate :
  Residual.PredicatePNF
canonicalVoidScopePredicate =
  Residual.predicatePNF
    "canonical void-scope predicate"
    Residual.sig-agent-theme
    (Residual.opaqueArg "typed-agent")
    (Residual.opaqueArg "typed-theme")
    Residual.absent
    Residual.positive
    Residual.directEvidence
    "void-scope-canonical-example"

canonicalVoidScopeReceipt :
  Residual.PNFEmissionReceipt
canonicalVoidScopeReceipt =
  Residual.pnfEmissionReceipt
    "canonical-parser"
    "canonical-reducer"
    "canonical void-scope source span"
    canonicalVoidScopePredicate

canonicalOutsideScopePredicate :
  Residual.PredicatePNF
canonicalOutsideScopePredicate =
  Residual.predicatePNF
    "canonical outside-scope predicate"
    Residual.sig-theme-only
    Residual.absent
    (Residual.opaqueArg "typed-theme")
    Residual.absent
    Residual.positive
    Residual.directEvidence
    "void-scope-canonical-example"

canonicalOutsideScopeReceipt :
  Residual.PNFEmissionReceipt
canonicalOutsideScopeReceipt =
  Residual.pnfEmissionReceipt
    "canonical-parser"
    "canonical-reducer"
    "canonical outside-scope source span"
    canonicalOutsideScopePredicate

canonicalNoTypedMeetComparedInFibre :
  NoTypedMeetComparedInFibre
canonicalNoTypedMeetComparedInFibre =
  noTypedMeetComparedInFibre
    canonicalVoidScopeReceipt
    canonicalVoidScopeReceipt
    Core.fibreFallback
    comparedInFibre_noTypedMeet
    refl
    true
    refl
    false
    refl
    Invariants.NO_TYPED_MEET
    refl
    Residual.noTypedMeet6
    refl
    false
    refl
    false
    refl
    false
    refl

canonicalScopeExceededOutsideComparison :
  ScopeExceededOutsideComparison
canonicalScopeExceededOutsideComparison =
  scopeExceededOutsideComparison
    canonicalVoidScopeReceipt
    canonicalOutsideScopeReceipt
    Core.fibreFallback
    (Core.fibreRef 1)
    outsideComparison_scopeExceeded
    refl
    false
    refl
    true
    refl
    Residual.scopeExceeded6
    refl
    false
    refl
    false
    refl
    false
    refl

canonicalFibreCollapseBoundary :
  FibreCollapseBoundary
canonicalFibreCollapseBoundary =
  fibreCollapseBoundary
    Core.fibreFallback
    (Core.fibreRef 1)
    fibreCollapse_scopeExceeded
    refl
    Residual.scopeExceeded6
    refl
    false
    refl
    false
    refl
    false
    refl

data PNFVoidScopeBoundaryRow : Set where
  noTypedMeetBoundaryRow :
    NoTypedMeetComparedInFibre →
    PNFVoidScopeBoundaryRow

  scopeExceededBoundaryRow :
    ScopeExceededOutsideComparison →
    PNFVoidScopeBoundaryRow

  fibreCollapseBoundaryRow :
    FibreCollapseBoundary →
    PNFVoidScopeBoundaryRow

canonicalPNFVoidScopeBoundaryRows :
  List PNFVoidScopeBoundaryRow
canonicalPNFVoidScopeBoundaryRows =
  noTypedMeetBoundaryRow canonicalNoTypedMeetComparedInFibre
  ∷ scopeExceededBoundaryRow canonicalScopeExceededOutsideComparison
  ∷ fibreCollapseBoundaryRow canonicalFibreCollapseBoundary
  ∷ []

canonicalNoTypedMeetRowIsComparedInFibre :
  NoTypedMeetComparedInFibre.ntmStatus
    canonicalNoTypedMeetComparedInFibre
  ≡
  comparedInFibre_noTypedMeet
canonicalNoTypedMeetRowIsComparedInFibre =
  refl

canonicalNoTypedMeetRowResidualIsNoTypedMeet :
  NoTypedMeetComparedInFibre.ntmFourLevelResidual
    canonicalNoTypedMeetComparedInFibre
  ≡
  Invariants.NO_TYPED_MEET
canonicalNoTypedMeetRowResidualIsNoTypedMeet =
  refl

canonicalNoTypedMeetRowIsNotScopeExceeded :
  NoTypedMeetComparedInFibre.ntmSixLevelResidual
    canonicalNoTypedMeetComparedInFibre
  ≡
  Residual.noTypedMeet6
canonicalNoTypedMeetRowIsNotScopeExceeded =
  refl

canonicalScopeExceededRowIsOutsideComparison :
  ScopeExceededOutsideComparison.scopeStatus
    canonicalScopeExceededOutsideComparison
  ≡
  outsideComparison_scopeExceeded
canonicalScopeExceededRowIsOutsideComparison =
  refl

canonicalScopeExceededRowResidualIsScopeExceeded :
  ScopeExceededOutsideComparison.scopeSixLevelResidual
    canonicalScopeExceededOutsideComparison
  ≡
  Residual.scopeExceeded6
canonicalScopeExceededRowResidualIsScopeExceeded =
  refl

canonicalFibreCollapseResidualIsScopeExceeded :
  FibreCollapseBoundary.collapseResidual canonicalFibreCollapseBoundary
  ≡
  Residual.scopeExceeded6
canonicalFibreCollapseResidualIsScopeExceeded =
  refl

canonicalNoTypedMeetTruthGateFalse :
  NoTypedMeetComparedInFibre.ntmTruthPromotion
    canonicalNoTypedMeetComparedInFibre
  ≡
  false
canonicalNoTypedMeetTruthGateFalse =
  refl

canonicalScopeExceededSupportGateFalse :
  ScopeExceededOutsideComparison.scopeSupportPromotion
    canonicalScopeExceededOutsideComparison
  ≡
  false
canonicalScopeExceededSupportGateFalse =
  refl

canonicalFibreCollapseAdmissibilityGateFalse :
  FibreCollapseBoundary.collapseGrantsAdmissibility
    canonicalFibreCollapseBoundary
  ≡
  false
canonicalFibreCollapseAdmissibilityGateFalse =
  refl

pnfVoidScopeBoundaryStatement :
  String
pnfVoidScopeBoundaryStatement =
  "NO_TYPED_MEET is a compared-in-fibre typed-meet failure; SCOPE_EXCEEDED is an outside-comparison or fibre-collapse boundary in the six-level residual surface. Neither grants truth, support, or admissibility."

pnfVoidScopeNoActorClassificationStatement :
  String
pnfVoidScopeNoActorClassificationStatement =
  "This receipt surface contains only canonical placeholder rows and asserts no live political or economic actor classification."
