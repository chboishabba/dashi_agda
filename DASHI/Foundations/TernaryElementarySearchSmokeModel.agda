module DASHI.Foundations.TernaryElementarySearchSmokeModel where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)

open import DASHI.Foundations.ElementarySingleOperator using (Var)
open import DASHI.Foundations.TernaryElementaryOperatorCandidate
  using (varT)
open import DASHI.Foundations.TernaryElementarySearchCertificate
open import DASHI.Foundations.TernaryElementarySearchSoundness

------------------------------------------------------------------------
-- Fully concrete singleton model for the certificate checker.  This proves the
-- induction and side-condition plumbing without promoting any analytic rule.

data SmokeValue : Set where
  smokeValue : SmokeValue

data SmokeValid : Set where
  smokeValid : SmokeValid

smokeSideConditionAuthority : SideConditionAuthority
smokeSideConditionAuthority =
  record
    { Valid = λ _ → SmokeValid
    }

smokeRewriteOperations : RewriteOperations
smokeRewriteOperations =
  record
    { Value = SmokeValue
    ; oneV = smokeValue
    ; expV = λ _ → smokeValue
    ; logV = λ _ → smokeValue
    ; subV = λ _ _ → smokeValue
    ; mulV = λ _ _ → smokeValue
    ; divV = λ _ _ → smokeValue
    }

smokeRewriteSemanticModel :
  RewriteSemanticModel smokeSideConditionAuthority
smokeRewriteSemanticModel =
  record
    { operations = smokeRewriteOperations
    ; expLogSound = λ _ _ _ → refl
    ; logExpSound = λ _ _ _ → refl
    ; cancelMulDivSound = λ _ _ _ _ → refl
    ; cancelDivMulSound = λ _ _ _ _ → refl
    }

smokeSearchCandidate : SearchCandidate
smokeSearchCandidate =
  candidate
    unitTarget
    (varT zero)
    certified
    zero
    (suc zero)
    refl
    refl

smokeCertifiedCandidate :
  CertifiedSearchCandidate smokeSideConditionAuthority
smokeCertifiedCandidate =
  record
    { candidateData = smokeSearchCandidate
    ; normalizeTree = λ _ → oneR
    ; targetExpression = λ _ → oneR
    ; certificateTrace = rewriteRefl
    ; candidateStatusIsCertified = refl
    }

smokeEnvironment : Var → SmokeValue
smokeEnvironment _ = smokeValue

smokeCertifiedCandidateSound :
  evaluateExpr smokeRewriteOperations smokeEnvironment oneR
  ≡ evaluateExpr smokeRewriteOperations smokeEnvironment oneR
smokeCertifiedCandidateSound =
  certifiedCandidateSound
    smokeRewriteSemanticModel
    smokeCertifiedCandidate
    smokeEnvironment
