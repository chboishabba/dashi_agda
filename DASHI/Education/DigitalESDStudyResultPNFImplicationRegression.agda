module DASHI.Education.DigitalESDStudyResultPNFImplicationRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Education.DigitalESDStudyResultPNFImplicationExact as ResultPNF
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF

quantitativeAuditCountRegression : ResultPNF.quantitativeResultAuditCount ≡ 4
quantitativeAuditCountRegression = refl

dengForceRegression :
  PNF.PredicateNormalAssertion.inferentialForce ResultPNF.dengPaidAssertion
  ≡ PNF.comparativeF
dengForceRegression = refl

brasslerForceRegression :
  PNF.PredicateNormalAssertion.inferentialForce ResultPNF.brasslerPaidAssertion
  ≡ PNF.comparativeF
brasslerForceRegression = refl

greenForceRegression :
  PNF.PredicateNormalAssertion.inferentialForce ResultPNF.greenPaidAssertion
  ≡ PNF.associationalF
greenForceRegression = refl
