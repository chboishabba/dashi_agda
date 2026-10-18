module DASHI.Physics.Foundations.RFMutualCouplingSnowballExact where

open import DASHI.Core.Prelude

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Discovery
import DASHI.Physics.Foundations.RFMutualCouplingManifoldExact as Coupling

------------------------------------------------------------------------
-- COUPLING-DRIVEN MANIFOLD REPAIR
--
-- Source evidence may reveal that an isolated-element manifold is inadequate
-- for a consumer because neighboring elements alter the effective response.
-- That observation can propose a refinement axis, but it cannot self-certify
-- the refined model, identify hardware, or create authority.
------------------------------------------------------------------------

data CouplingRefinementAxis : Set where
  interElementCouplingAxis : CouplingRefinementAxis
  activeReflectionAxis : CouplingRefinementAxis
  embeddedElementResponseAxis : CouplingRefinementAxis
  couplingCorrectedManifoldAxis : CouplingRefinementAxis

couplingObservationProposal :
  Discovery.AxisProposal CouplingRefinementAxis
couplingObservationProposal = Discovery.axis-proposal
  interElementCouplingAxis
  Discovery.externalKnowledgeComparison
  "RF-port / array-response consumer"
  "does the isolated-element observer remain adequate after neighboring-element coupling is admitted?"
  "primary S-parameter sources show inter-element coupling contributes to active array response"
  "source payment is bounded to measured/modelled coupling relationships"
  "coupling evidence does not identify an exact emitter or authorize action"

activeReflectionProposal :
  Discovery.AxisProposal CouplingRefinementAxis
activeReflectionProposal = Discovery.axis-proposal
  activeReflectionAxis
  Discovery.residualObservation
  "active-array response consumer"
  "which port-level coordinate captures excitation-dependent reflection after coupling?"
  "active reflection is source-paid as depending on self-reflection and mutual-coupling terms"
  "active reflection remains a port observable rather than a bearing"
  "port response does not determine exact array identity"

embeddedResponseProposal :
  Discovery.AxisProposal CouplingRefinementAxis
embeddedResponseProposal = Discovery.axis-proposal
  embeddedElementResponseAxis
  Discovery.failedFactorsThrough
  "coupling-corrected array-pattern consumer"
  "can an isolated element response represent the embedded element in the coupled array?"
  "embedded-element references retain neighboring-element coupling in the element response"
  "documentation pays the bounded representation relationship only"
  "the corrected response is not exact world recovery"

correctedManifoldProposal :
  Discovery.AxisProposal CouplingRefinementAxis
correctedManifoldProposal = Discovery.axis-proposal
  couplingCorrectedManifoldAxis
  Discovery.proofSearch
  "array-manifold consumer"
  "should the manifold retain coupling-sensitive element response for this consumer?"
  "RFMutualCouplingManifoldExact exposes a distinct coupling-correction coordinate"
  "repository synthesis relates source-paid leaves without importing source proof"
  "additional state must remain consumer-indexed rather than universally preferred"

record CouplingRepairProposalBundle : Set where
  constructor coupling-repair-proposal-bundle
  field
    couplingAxisProposal :
      Discovery.AxisProposal CouplingRefinementAxis
    activeReflectionAxisProposal :
      Discovery.AxisProposal CouplingRefinementAxis
    embeddedResponseAxisProposal :
      Discovery.AxisProposal CouplingRefinementAxis
    correctedManifoldAxisProposal :
      Discovery.AxisProposal CouplingRefinementAxis
    couplingReceiptRetained :
      Coupling.MutualCouplingObservationReceipt
    activeElementReceiptRetained :
      Coupling.ActiveElementResponseReceipt
    correctedManifoldReceiptRetained :
      Coupling.CouplingCorrectedManifoldReceipt
open CouplingRepairProposalBundle public

canonicalCouplingRepairProposalBundle : CouplingRepairProposalBundle
canonicalCouplingRepairProposalBundle =
  coupling-repair-proposal-bundle
    couplingObservationProposal
    activeReflectionProposal
    embeddedResponseProposal
    correctedManifoldProposal
    Coupling.canonicalMutualCouplingObservationReceipt
    Coupling.canonicalActiveElementResponseReceipt
    Coupling.canonicalCouplingCorrectedManifoldReceipt

record CouplingProofSearchRoute : Set where
  constructor coupling-proof-search-route
  field
    routeAdmission : ProofSearch.RouteAdmission
    repairBundle : CouplingRepairProposalBundle

    sourceDiscoveryMayProposeCorrection : Bool
    sourceDiscoveryMayProposeCorrectionIsTrue :
      sourceDiscoveryMayProposeCorrection ≡ true

    proofSearchMaySelfCertifyCouplingModel : Bool
    proofSearchMaySelfCertifyCouplingModelIsFalse :
      proofSearchMaySelfCertifyCouplingModel ≡ false

    correctionAxisMayBeDroppedWithoutConsumerCheck : Bool
    correctionAxisMayBeDroppedWithoutConsumerCheckIsFalse :
      correctionAxisMayBeDroppedWithoutConsumerCheck ≡ false

open CouplingProofSearchRoute public

canonicalCouplingProofSearchRoute : CouplingProofSearchRoute
canonicalCouplingProofSearchRoute =
  coupling-proof-search-route
    ProofSearch.canonicalRouteAdmission
    canonicalCouplingRepairProposalBundle
    true refl
    false refl
    false refl

record CouplingAdmissionFirewall : Set where
  constructor coupling-admission-firewall
  field
    sourceCitationEqualsKernelProof : Bool
    sourceCitationEqualsKernelProofIsFalse :
      sourceCitationEqualsKernelProof ≡ false

    couplingCoordinateAlwaysNeeded : Bool
    couplingCoordinateAlwaysNeededIsFalse :
      couplingCoordinateAlwaysNeeded ≡ false

    activeReflectionEqualsBearing : Bool
    activeReflectionEqualsBearingIsFalse :
      activeReflectionEqualsBearing ≡ false

    correctedManifoldEqualsExactHardware : Bool
    correctedManifoldEqualsExactHardwareIsFalse :
      correctedManifoldEqualsExactHardware ≡ false

    moreElectromagneticDetailAutomaticallyImprovesEveryConsumer : Bool
    moreElectromagneticDetailAutomaticallyImprovesEveryConsumerIsFalse :
      moreElectromagneticDetailAutomaticallyImprovesEveryConsumer ≡ false

open CouplingAdmissionFirewall public

canonicalCouplingAdmissionFirewall : CouplingAdmissionFirewall
canonicalCouplingAdmissionFirewall =
  coupling-admission-firewall
    false refl
    false refl
    false refl
    false refl
    false refl
