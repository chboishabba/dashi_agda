module DASHI.Core.OrthogonalStatusDecompositionAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Interop.CrossLaneProofArchaeologyLedgerExact as Archaeology
import DASHI.Analysis.RiemannG2ExplicitCutoffTargetWindowFrontierExact as Riemann
import DASHI.Governance.AustralianSenateAutismInquiryExact as Governance
import DASHI.Papers.NavierStokes.FourLaneProofProgramExact as NS
import DASHI.Interop.SLRGWBExecutionRoadmapExact as Wiki

------------------------------------------------------------------------
-- ORTHOGONAL STATUS DECOMPOSITION AUDIT
--
-- This owner does NOT introduce a replacement mega-enum.  It audits existing
-- lanes and classifies the semantic axis actually carried by their status
-- constructors/coordinates.  The point is to prove that enum/type naming is
-- too coarse to determine meaning before any future migration to a product-
-- style status record is designed.
--
-- The multilingual Wikimedia lane adds a second guard: even a well-factored
-- status product is not the complete provenance/context state.  Target-surface
-- assertion, language-surface provenance and semantic-equivalence debt must not
-- be silently absorbed into payment/routing/ownership/certification/residual.
------------------------------------------------------------------------

data StatusAxis : Set where
  paymentAxis : StatusAxis
  routingAxis : StatusAxis
  ownershipAxis : StatusAxis
  certificationAxis : StatusAxis
  residualAxis : StatusAxis

data NonStatusContextAxis : Set where
  sourceSurfaceAssertionAxis : NonStatusContextAxis
  languageSurfaceProvenanceAxis : NonStatusContextAxis
  semanticEquivalenceAxis : NonStatusContextAxis

------------------------------------------------------------------------
-- Archaeology: genuine evidentiary/payment state.
------------------------------------------------------------------------

archaeologyAxis : Archaeology.PaymentStatus → StatusAxis
archaeologyAxis Archaeology.paid = paymentAxis
archaeologyAxis Archaeology.conditionalPayment = paymentAxis
archaeologyAxis Archaeology.unpaid = paymentAxis
archaeologyAxis Archaeology.notApplicable = paymentAxis

archaeologyPaidIsPayment :
  archaeologyAxis Archaeology.paid ≡ paymentAxis
archaeologyPaidIsPayment = refl

archaeologyUnpaidIsPayment :
  archaeologyAxis Archaeology.unpaid ≡ paymentAxis
archaeologyUnpaidIsPayment = refl

------------------------------------------------------------------------
-- Riemann: the local type named PaymentStatus is not a pure payment axis.
-- `ownedExternally` is ownership; `live/pruned/optional` are routing/frontier
-- dispositions.
------------------------------------------------------------------------

riemannAxis : Riemann.PaymentStatus → StatusAxis
riemannAxis Riemann.ownedExternally = ownershipAxis
riemannAxis Riemann.live = routingAxis
riemannAxis Riemann.pruned = routingAxis
riemannAxis Riemann.optional = routingAxis

riemannOwnedExternallyIsOwnership :
  riemannAxis Riemann.ownedExternally ≡ ownershipAxis
riemannOwnedExternallyIsOwnership = refl

riemannLiveIsRouting : riemannAxis Riemann.live ≡ routingAxis
riemannLiveIsRouting = refl

riemannPrunedIsRouting : riemannAxis Riemann.pruned ≡ routingAxis
riemannPrunedIsRouting = refl

------------------------------------------------------------------------
-- Governance: one local proposition-status type mixes present source payment
-- with the class of residual payment still open downstream.
------------------------------------------------------------------------

data GovernanceResidualKind : Set where
  sameObjectWeldResidual : GovernanceResidualKind
  implementationResidual : GovernanceResidualKind
  outcomeResidual : GovernanceResidualKind

governanceAxis : Governance.PropositionPaymentStatus → StatusAxis
governanceAxis Governance.externalRecordPaid = paymentAxis
governanceAxis Governance.downstreamSameObjectWeldOpen = residualAxis
governanceAxis Governance.implementationPaymentOpen = residualAxis
governanceAxis Governance.outcomePaymentOpen = residualAxis

governanceResidualKind :
  (status : Governance.PropositionPaymentStatus) →
  governanceAxis status ≡ residualAxis → GovernanceResidualKind
governanceResidualKind Governance.externalRecordPaid ()
governanceResidualKind Governance.downstreamSameObjectWeldOpen refl = sameObjectWeldResidual
governanceResidualKind Governance.implementationPaymentOpen refl = implementationResidual
governanceResidualKind Governance.outcomePaymentOpen refl = outcomeResidual

governanceExternalRecordIsPayment :
  governanceAxis Governance.externalRecordPaid ≡ paymentAxis
governanceExternalRecordIsPayment = refl

governanceImplementationOpenIsResidual :
  governanceAxis Governance.implementationPaymentOpen ≡ residualAxis
governanceImplementationOpenIsResidual = refl

------------------------------------------------------------------------
-- Certification: Navier-Stokes already retains this independently from route,
-- recovery/source and theorem-payment coordinates.
------------------------------------------------------------------------

nsCertificationAxis : StatusAxis
nsCertificationAxis = certificationAxis

nsCommutatorRecoveryAssumptionActive :
  NS.periodicBCommutatorSpineRecoveryAssumptionActive
    NS.canonicalNSFourLaneProofProgram ≡ true
nsCommutatorRecoveryAssumptionActive =
  NS.periodicBCommutatorSpineRecoveryAssumptionActiveIsTrue

nsCommutatorCertificationObserved :
  NS.periodicBCommutatorSpineCertificationObserved
    NS.canonicalNSFourLaneProofProgram ≡ false
nsCommutatorCertificationObserved =
  NS.periodicBCommutatorSpineCertificationObservedIsFalse

------------------------------------------------------------------------
-- Wikimedia multilingual refinement.
--
-- SLR/GWB already pays shared-QID multilingual parser/PNF compatibility and
-- per-surface semantic closure, while explicitly refusing three promotions:
--   shared QID -> translation equivalence;
--   propagated atom -> assertion by the target article/surface;
--   SimpleWiki -> subset/translation of English Wikipedia.
--
-- These are not merely payment/routing statuses.  They retain provenance and
-- source-surface semantics that any future status-product migration must keep
-- outside, or explicitly alongside, the five candidate status axes.
------------------------------------------------------------------------

wikiSourceSurfaceAssertionAxis : NonStatusContextAxis
wikiSourceSurfaceAssertionAxis = sourceSurfaceAssertionAxis

wikiLanguageSurfaceProvenanceAxis : NonStatusContextAxis
wikiLanguageSurfaceProvenanceAxis = languageSurfaceProvenanceAxis

wikiSemanticEquivalenceAxis : NonStatusContextAxis
wikiSemanticEquivalenceAxis = semanticEquivalenceAxis

wikiSharedQidDoesNotPromoteTranslationEquivalence :
  Wiki.sharedQidMayPromoteTranslationEquivalence
    Wiki.canonicalGWBExecutionBoundary ≡ false
wikiSharedQidDoesNotPromoteTranslationEquivalence = refl

wikiSemanticPropagationDoesNotRewriteTargetSurface :
  Wiki.semanticPropagationMayRewriteTargetSurface
    Wiki.canonicalGWBExecutionBoundary ≡ false
wikiSemanticPropagationDoesNotRewriteTargetSurface = refl

wikiSimpleWikiIsNotEnglishSubset :
  Wiki.simpleWikiMayBePresumedEnglishSubset
    Wiki.canonicalGWBExecutionBoundary ≡ false
wikiSimpleWikiIsNotEnglishSubset = refl

------------------------------------------------------------------------
-- Audit result.  The representative lanes support orthogonal factorisation,
-- but this file is intentionally not the replacement product or migration
-- layer.  Canonical promotion remains false until an exact record, translations
-- and consumer-by-consumer migration obligations are designed and checked.
-- The multilingual audit further requires preservation of non-status context.
------------------------------------------------------------------------

record OrthogonalStatusAuditBoundary : Set where
  constructor orthogonal-status-audit-boundary
  field
    archaeologyPaymentStatusIsPurePaymentAxis : Bool
    riemannPaymentStatusIsPurePaymentAxis : Bool
    governancePropositionStatusIsPurePaymentAxis : Bool
    certificationObservedIsIndependentCoordinate : Bool
    sameEnumNameDeterminesSemanticAxis : Bool
    representativeAuditSupportsOrthogonalFactorisation : Bool
    canonicalFiveAxisProductReadyForPromotion : Bool
    singleMegaEnumWouldPreserveAllDistinctions : Bool

    multilingualSurfaceAssertionIsIndependentCoordinate : Bool
    fiveStatusAxesSufficientForMultilingualSurfaceSemantics : Bool
    sharedQidPaysTranslationEquivalence : Bool
    semanticPropagationAssertsTargetSurface : Bool
    simpleWikiPresumedEnglishSubset : Bool
    provenanceContextMustSurviveStatusMigration : Bool

open OrthogonalStatusAuditBoundary public

canonicalOrthogonalStatusAuditBoundary : OrthogonalStatusAuditBoundary
canonicalOrthogonalStatusAuditBoundary =
  orthogonal-status-audit-boundary
    true
    false
    false
    true
    false
    true
    false
    false
    true
    false
    false
    false
    false
    true

record StatusAuditReading : Set where
  constructor status-audit-reading
  field
    archaeologyReading : String
    riemannReading : String
    governanceReading : String
    certificationReading : String
    multilingualReading : String
    nextDesignStep : String

open StatusAuditReading public

canonicalStatusAuditReading : StatusAuditReading
canonicalStatusAuditReading = status-audit-reading
  "CrossLaneProofArchaeologyLedgerExact.PaymentStatus is an evidentiary/payment axis: paid, conditional, unpaid, not-applicable."
  "RiemannG2ExplicitCutoffTargetWindowFrontierExact.PaymentStatus mixes ownership (ownedExternally) with route/frontier disposition (live, pruned, optional); the shared type name therefore cannot be treated as evidence of shared semantics."
  "AustralianSenateAutismInquiryExact.PropositionPaymentStatus mixes a paid external-record state with distinct downstream residual classes: same-object weld, implementation and outcome."
  "FourLaneProofProgramExact explicitly retains recovery/source progress independently from observed Agda certification; source-written/recovered structure cannot manufacture a kernel receipt."
  "SLRGWBExecutionRoadmapExact shows that shared-QID identity, multilingual parser/PNF compatibility, target-surface assertion and semantic equivalence are distinct: propagation keeps target_surface_asserted=false, and SimpleWiki remains a peer evidence surface rather than a presumed English subset or translation. These provenance/context coordinates must survive any status migration rather than being squeezed into payment or residual status."
  "A later design may factor status into PaymentState × RoutingState × OwnershipState × CertificationState × ResidualKind, but only with exact translations, consumer-preservation proofs, and explicit retention of orthogonal provenance/context coordinates such as language surface and target-surface assertion. This audit does not yet promote that product as canonical."
