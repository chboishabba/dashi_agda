module DASHI.Physics.Foundations.RFArrayManifoldSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Discovery
import DASHI.Physics.Foundations.RFArrayManifoldPhasorCrossPollinationExact as Manifold

------------------------------------------------------------------------
-- FAILED-FACTORISATION DRIVEN ARRAY-MANIFOLD SNOWBALL
--
-- The exact finite obstruction is owned by Manifold:
-- scalar magnitude alone cannot recover the angular answer in the witness.
-- This owner turns that failure into explicit repair proposals.  Proposal is
-- not admission, source truth, hardware identity, or operational authority.
------------------------------------------------------------------------

data ArrayRefinementAxis : Set where
  relativeSpatialPhaseAxis : ArrayRefinementAxis
  arrayDependentManifoldAxis : ArrayRefinementAxis
  wavefieldDependentManifoldAxis : ArrayRefinementAxis
  electromagneticCorrectionAxis : ArrayRefinementAxis
  angularConsumerAxis : ArrayRefinementAxis

relativePhaseRepairProposal : Discovery.AxisProposal ArrayRefinementAxis
relativePhaseRepairProposal = Discovery.axis-proposal
  relativeSpatialPhaseAxis
  Discovery.failedFactorsThrough
  "phase-sensitive angular consumer"
  "does scalar magnitude retain enough information for the requested angular answer?"
  "magnitudeAloneDoesNotRecoverBearing supplies an exact same-magnitude / different-bearing obstruction"
  "physical phase interpretation remains source-bounded by the RF source atlases"
  "the repair creates neither emitter identity nor operational authority"

arrayDependentProposal : Discovery.AxisProposal ArrayRefinementAxis
arrayDependentProposal = Discovery.axis-proposal
  arrayDependentManifoldAxis
  Discovery.proofSearch
  "array-manifold consumer"
  "which retained coordinates belong to the array rather than the incoming wavefield?"
  "Belloni manifold separation motivates an explicit array-dependent coordinate"
  "source claim pays only the bounded manifold distinction"
  "array coordinates do not identify exact hardware provenance"

wavefieldDependentProposal : Discovery.AxisProposal ArrayRefinementAxis
wavefieldDependentProposal = Discovery.axis-proposal
  wavefieldDependentManifoldAxis
  Discovery.proofSearch
  "array-manifold consumer"
  "which retained coordinates vary with the incident wavefield?"
  "Belloni manifold separation motivates an explicit wavefield-dependent coordinate"
  "source claim pays only the bounded manifold distinction"
  "wavefield coordinates do not determine an exact emitter world"

electromagneticCorrectionProposal : Discovery.AxisProposal ArrayRefinementAxis
electromagneticCorrectionProposal = Discovery.axis-proposal
  electromagneticCorrectionAxis
  Discovery.externalKnowledgeComparison
  "realistic array-manifold refinement"
  "when does an idealized array observer need an electromagnetic correction coordinate?"
  "Castellanos-Heath identifies coupling, near-field and polarization effects absent from simpler manifolds"
  "source payment is bounded to the cited electromagnetic-manifold model"
  "model refinement is not exact hardware identification"

record ArrayAxisProposalBundle : Set where
  constructor array-axis-proposal-bundle
  field
    phaseRepair : Discovery.AxisProposal ArrayRefinementAxis
    arrayDependentRepair : Discovery.AxisProposal ArrayRefinementAxis
    wavefieldDependentRepair : Discovery.AxisProposal ArrayRefinementAxis
    electromagneticRepair : Discovery.AxisProposal ArrayRefinementAxis
    factorisationFailureStillAvailable :
      ¬ Manifold.MagnitudeFactorsToBearing
open ArrayAxisProposalBundle public

canonicalArrayAxisProposalBundle : ArrayAxisProposalBundle
canonicalArrayAxisProposalBundle =
  array-axis-proposal-bundle
    relativePhaseRepairProposal
    arrayDependentProposal
    wavefieldDependentProposal
    electromagneticCorrectionProposal
    Manifold.magnitudeAloneDoesNotRecoverBearing

------------------------------------------------------------------------
-- LEAST-PRIVILEGE PROOF-SEARCH ROUTE
------------------------------------------------------------------------

record ArrayManifoldProofSearchRoute : Set where
  constructor array-manifold-proof-search-route
  field
    routeAdmission : ProofSearch.RouteAdmission
    proposals : ArrayAxisProposalBundle
    proofSearchMayProposeRepair : Bool
    proofSearchMayProposeRepairIsTrue :
      proofSearchMayProposeRepair ≡ true
    proofSearchCreatesPhysicalTruth : Bool
    proofSearchCreatesPhysicalTruthIsFalse :
      proofSearchCreatesPhysicalTruth ≡ false
    failedFactorisationMayBeIgnored : Bool
    failedFactorisationMayBeIgnoredIsFalse :
      failedFactorisationMayBeIgnored ≡ false
open ArrayManifoldProofSearchRoute public

canonicalArrayManifoldProofSearchRoute : ArrayManifoldProofSearchRoute
canonicalArrayManifoldProofSearchRoute =
  array-manifold-proof-search-route
    ProofSearch.canonicalRouteAdmission
    canonicalArrayAxisProposalBundle
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- ADMISSION / ATTRIBUTION FIREWALL
------------------------------------------------------------------------

record ArrayManifoldAdmissionFirewall : Set where
  constructor array-manifold-admission-firewall
  field
    proposalEqualsAdmission : Bool
    proposalEqualsAdmissionIsFalse : proposalEqualsAdmission ≡ false

    sourceCitationEqualsKernelProof : Bool
    sourceCitationEqualsKernelProofIsFalse :
      sourceCitationEqualsKernelProof ≡ false

    sourceManifoldEqualsRepositorySyntheticWitness : Bool
    sourceManifoldEqualsRepositorySyntheticWitnessIsFalse :
      sourceManifoldEqualsRepositorySyntheticWitness ≡ false

    additionalCoordinateAlwaysImprovesEveryConsumer : Bool
    additionalCoordinateAlwaysImprovesEveryConsumerIsFalse :
      additionalCoordinateAlwaysImprovesEveryConsumer ≡ false

    manifoldRefinementDeterminesExactWorld : Bool
    manifoldRefinementDeterminesExactWorldIsFalse :
      manifoldRefinementDeterminesExactWorld ≡ false

    manifoldRefinementCreatesOperationalAuthority : Bool
    manifoldRefinementCreatesOperationalAuthorityIsFalse :
      manifoldRefinementCreatesOperationalAuthority ≡ false

open ArrayManifoldAdmissionFirewall public

canonicalArrayManifoldAdmissionFirewall : ArrayManifoldAdmissionFirewall
canonicalArrayManifoldAdmissionFirewall =
  array-manifold-admission-firewall
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
