{-# OPTIONS --safe #-}
module DASHI.Unified.GovernedLegalCurrentTOEValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Unified.Everything as Unified
import DASHI.Unified.GovernedLegalWorkflowTOEBridgeExact as Governance
import DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact as Ibrahim
import DASHI.Unified.FleetFormalGapTargetTOEExact as Fleet

rootGovernanceHandoffIsCanonical :
  TOE.toeGovernedLegalWorkflowAuthorityInvariantHandoff
  ≡ Governance.canonicalGovernedLegalWorkflowAuthorityInvariantHandoff
rootGovernanceHandoffIsCanonical = refl

unifierGovernanceHandoffIsCanonical :
  Unifier.unifierGovernedLegalWorkflowAuthorityInvariantHandoff
  ≡ Governance.canonicalGovernedLegalWorkflowAuthorityInvariantHandoff
unifierGovernanceHandoffIsCanonical = refl

unifiedGovernanceHandoffIsCanonical :
  Unified.unifiedGovernedLegalWorkflowAuthorityInvariantHandoff
  ≡ Governance.canonicalGovernedLegalWorkflowAuthorityInvariantHandoff
unifiedGovernanceHandoffIsCanonical = refl

rootAndUnifierGovernanceAgree :
  TOE.toeGovernedLegalWorkflowAuthorityInvariantHandoff
  ≡ Unifier.unifierGovernedLegalWorkflowAuthorityInvariantHandoff
rootAndUnifierGovernanceAgree = refl

candidateSourceStillNotAuthority :
  Governance.CandidateSourceIsAuthoritative → ⊥
candidateSourceStillNotAuthority =
  TOE.toeCandidateSourceIsNotLegalAuthority

sameSystemStillNotAuthority :
  Governance.SameLegalSystemAutomaticallyMeansAuthority → ⊥
sameSystemStillNotAuthority =
  TOE.toeSameLegalSystemIsNotLegalAuthority

validityStillNotApplicability :
  Governance.CurrentValidityAutomaticallyMeansApplicability → ⊥
validityStillNotApplicability =
  TOE.toeCurrentValidityIsNotApplicability

semanticAdmissionStillNotAuthority :
  Governance.SemanticAdmissionAuthorityIsLegalSourceAuthority → ⊥
semanticAdmissionStillNotAuthority =
  TOE.toeSemanticAdmissionIsNotLegalAuthority

documentRoleStillNotAuthority :
  Governance.DocumentRoleSuppliesLegalSourceAuthority → ⊥
documentRoleStillNotAuthority =
  TOE.toeDocumentRoleIsNotLegalAuthority

-- Current-master Pareto/snowball and fleet boundaries remain independent owners.
recognitionParetoStillCanonical :
  TOE.toeIbrahimRecognitionParetoBoundary
  ≡ Ibrahim.ibrahimRecognitionParetoBoundary
recognitionParetoStillCanonical = refl

fleetTargetStillCanonical :
  TOE.toeFleetFormalGapTargetReceipt
  ≡ Fleet.canonicalFleetFormalGapTargetReceipt
fleetTargetStillCanonical = refl

fleetPaidFibresStayOut :
  Fleet.FleetDischargedFibreRetargetPermission → ⊥
fleetPaidFibresStayOut =
  TOE.toeFleetDischargedFibresRemainOutOfTarget

fleetContradictionsStaySeparate :
  Fleet.FleetContradictionGapReclassificationPermission → ⊥
fleetContradictionsStaySeparate =
  TOE.toeFleetContradictionGapsRemainSeparate
