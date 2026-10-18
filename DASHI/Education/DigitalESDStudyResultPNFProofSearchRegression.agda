module DASHI.Education.DigitalESDStudyResultPNFProofSearchRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Education.DigitalESDStudyResultPNFProofSearchExact as StudyPNF
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone
import DASHI.Reasoning.AristotleExperimentalProofSearchExact as ProofSearch

studyResultAssertionCountRegression : StudyPNF.studyResultAssertionCount ≡ 5
studyResultAssertionCountRegression = refl

proofSearchBoundaryReuseRegression :
  StudyPNF.proofSearchBoundary
  ≡ ProofSearch.canonicalAristotleExperimentalProofSearchBoundary
proofSearchBoundaryReuseRegression = refl

iaqInferentialForceRegression :
  PNF.PredicateNormalAssertion.inferentialForce StudyPNF.iaqObservedGainAssertion
  ≡ PNF.comparativeF
iaqInferentialForceRegression = refl

iaqCeilingRegression :
  StudyPNF.StudyResultAudit.strongestPaidImplication StudyPNF.iaqResultAudit
  ≡ Cone.derivesBoundedContrast
iaqCeilingRegression = refl

brasslerInferentialForceRegression :
  PNF.PredicateNormalAssertion.inferentialForce StudyPNF.brasslerInteractionAssertion
  ≡ PNF.comparativeF
brasslerInferentialForceRegression = refl

brasslerCeilingRegression :
  StudyPNF.StudyResultAudit.strongestPaidImplication StudyPNF.brasslerResultAudit
  ≡ Cone.derivesBoundedContrast
brasslerCeilingRegression = refl

descampsCeilingRegression :
  StudyPNF.StudyResultAudit.strongestPaidImplication StudyPNF.descampsResultAudit
  ≡ Cone.derivesBoundedContrast
descampsCeilingRegression = refl

greenInferentialForceRegression :
  PNF.PredicateNormalAssertion.inferentialForce StudyPNF.greenSimulationAssertion
  ≡ PNF.associationalF
greenInferentialForceRegression = refl

greenCeilingRegression :
  StudyPNF.StudyResultAudit.strongestPaidImplication StudyPNF.greenResultAudit
  ≡ Cone.associatesTreatmentAndOutcome
greenCeilingRegression = refl

firstUnpaidGreenRegression :
  StudyPNF.StudyResultAudit.firstUnpaidImplication StudyPNF.greenResultAudit
  ≡ Cone.attributesCausalEffect
firstUnpaidGreenRegression = refl

colladoInferentialForceRegression :
  PNF.PredicateNormalAssertion.inferentialForce StudyPNF.colladoLongitudinalAssertion
  ≡ PNF.comparativeF
colladoInferentialForceRegression = refl

colladoCeilingRegression :
  StudyPNF.StudyResultAudit.strongestPaidImplication StudyPNF.colladoResultAudit
  ≡ Cone.derivesBoundedContrast
colladoCeilingRegression = refl

colladoFirstUnpaidRegression :
  StudyPNF.StudyResultAudit.firstUnpaidImplication StudyPNF.colladoResultAudit
  ≡ Cone.attributesCausalEffect
colladoFirstUnpaidRegression = refl
