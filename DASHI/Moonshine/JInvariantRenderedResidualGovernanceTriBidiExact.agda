module DASHI.Moonshine.JInvariantRenderedResidualGovernanceTriBidiExact where

------------------------------------------------------------------------
-- RH / LIGHT-TRANSPORT / j RENDERED RESIDUAL GOVERNANCE
--
-- Exact certificate-schema reuse only.  No theorem is transferred between
-- RH, physical rendering and the analytic j-invariant.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.JInvariantRiemannObserverResidualSufficiencyBidiExact as RHJ
import DASHI.Moonshine.JInvariantRenderedIntervalOrbitRecognitionBidiExact as JBox
import DASHI.Physics.Closure.LightTransportFibreClosure as Light
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

------------------------------------------------------------------------
-- 1. Shared governance rule.
------------------------------------------------------------------------

data ResidualGovernanceRule : Set where
  retainUntilConsumerSufficient : ResidualGovernanceRule
  retainSideInformationUntilReceipt : ResidualGovernanceRule
  retainRenderedUncertaintyUntilUnique : ResidualGovernanceRule

canonicalResidualGovernanceRules : List ResidualGovernanceRule
canonicalResidualGovernanceRules =
  retainUntilConsumerSufficient
  ∷ retainSideInformationUntilReceipt
  ∷ retainRenderedUncertaintyUntilUnique
  ∷ []

------------------------------------------------------------------------
-- 2. Existing witnesses are imported as separate coordinates.
------------------------------------------------------------------------

rhJLocalCollisionAlreadyConstructed : Bool
rhJLocalCollisionAlreadyConstructed = true

lightTransportForbidsHiddenResidualDiscard : Bool
lightTransportForbidsHiddenResidualDiscard = true

jRenderedBoxRetainedUntilUnique : Bool
jRenderedBoxRetainedUntilUnique = JBox.renderedBoxMustBeRetainedUntilUnique

nearestPixelIsNotAnalyticAuthority : Bool
nearestPixelIsNotAnalyticAuthority =
  JBox.nearestPixelAloneEntitlesOrbitTheorem

------------------------------------------------------------------------
-- 3. Relation strength firewall.
------------------------------------------------------------------------

triBidiRelation : Relation.RelationKind
triBidiRelation = Relation.exactCertificateSchemaReuse

triBidiReuse : Relation.ReuseCapability triBidiRelation
triBidiReuse = Relation.reuseExactCertificateSchema

triBidiHasNoDirectTheoremTransfer :
  Relation.TheoremTransferCapability triBidiRelation → ⊥
triBidiHasNoDirectTheoremTransfer =
  Relation.certificateSchemaCannotDirectlyTransferTheorem

------------------------------------------------------------------------
-- 4. Normalized rendered-j admission rule.
------------------------------------------------------------------------

record RenderedJAdmissionGovernance : Set where
  constructor rendered-j-admission-governance
  field
    pixelSideInformationRetained : Bool
    analyticBoxResidualRetained : Bool
    orbitUniquenessRequiredBeforeIndexPromotion : Bool
    fullJFineRetainedAfterRecognition : Bool
    consumerMayLaterQuotientWithSufficiencyReceipt : Bool
    rhTheoremTransferredToJ : Bool
    lightTransportTheoremTransferredToJ : Bool

canonicalRenderedJAdmissionGovernance : RenderedJAdmissionGovernance
canonicalRenderedJAdmissionGovernance =
  rendered-j-admission-governance
    true true true true true false false
