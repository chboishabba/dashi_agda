module DASHI.Governance.BoloBoloTargetPilotAdmissibilityRegression where

-- RED-first contract: target pilot execution must remain separately governed.

import DASHI.Governance.BoloBoloTargetPilotAdmissibilityExact as Pilot

interventionAdmissionRequired :
  Pilot.interventionScopedGovernedAdmissionRequired
    Pilot.canonicalTargetPilotAdmissibilityBoundary ≡ true
interventionAdmissionRequired = refl

initialResearchConsentInsufficient :
  Pilot.initialResearchConsentAutomaticallyAuthorisesPilotIntervention
    Pilot.canonicalTargetPilotAdmissibilityBoundary ≡ false
initialResearchConsentInsufficient = refl

causalCertificateNotExecutionAuthority :
  Pilot.causalResultAutomaticallyAuthorisesPilot
    Pilot.canonicalTargetPilotAdmissibilityBoundary ≡ false
causalCertificateNotExecutionAuthority = refl

sameTargetRequired :
  Pilot.sameTargetBindingRequired
    Pilot.canonicalTargetPilotAdmissibilityBoundary ≡ true
sameTargetRequired = refl
