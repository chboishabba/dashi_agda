module DASHI.Biology.NeurodivergentAtlasGovernanceIntegration where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (tt)

import DASHI.Biology.NeurodivergentAtlasBodyMemoryBridge as Atlas
import DASHI.Biology.FMRIConnectomeProxyGovernance as FMRI
import DASHI.Biology.TraumaClinicalGovernanceBoundary as Trauma
import DASHI.Biology.ConsentAgencyGovernanceCore as Consent
import DASHI.Promotion.ExplanationAuthorityBoundaryCore as Explanation

record NeurodivergentAtlasGovernanceIntegration : Set where
  constructor mkNeurodivergentAtlasGovernanceIntegration
  field
    label : String
    atlasCandidateRoute : Atlas.NeurodivergentAtlasRoute
    atlasCandidateRouteAdmissible : Atlas.AdmissibleNeurodivergentAtlasRoute atlasCandidateRoute
    fmriGovernance : FMRI.FMRIConnectomeProxyGovernance
    traumaGovernance : Trauma.TraumaClinicalGovernanceBoundary
    consentGovernance : Consent.ConsentAgencyGovernance
    explanationBoundary : Explanation.ExplanationAuthorityBoundary
    atypicalReportIsNotAbsentAffect : Bool
    atypicalLabelIsNotPathology : Bool
    sensoryWeightDifferenceIsNotDefect : Bool
    socialCodeDifferenceIsNotDefect : Bool
    forcedNormalisationBlocked : Bool
    integrationHolds : Bool
    integrationHoldsIsTrue : integrationHolds ≡ true

open NeurodivergentAtlasGovernanceIntegration public

canonicalNeurodivergentAtlasGovernanceIntegration : NeurodivergentAtlasGovernanceIntegration
canonicalNeurodivergentAtlasGovernanceIntegration =
  mkNeurodivergentAtlasGovernanceIntegration
    "neurodivergent atlas governance integration"
    Atlas.candidateOnlyRoute tt
    FMRI.canonicalFMRIConnectomeProxyGovernance
    Trauma.canonicalTraumaClinicalGovernanceBoundary
    Consent.canonicalConsentAgencyGovernance
    Explanation.canonicalExplanationAuthorityBoundary
    true true true true true true refl
