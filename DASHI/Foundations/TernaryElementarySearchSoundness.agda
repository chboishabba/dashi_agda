module DASHI.Foundations.TernaryElementarySearchSoundness where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.ElementarySingleOperator using (Var)
open import DASHI.Foundations.TernaryElementarySearchCertificate

------------------------------------------------------------------------
-- A certificate is promoted only relative to a semantic model whose primitive
-- side-condition rules are themselves proved.  Thus the external search may
-- propose a trace, but Agda checks both the trace and every analytic premise.

record RewriteOperations : Set₁ where
  field
    Value : Set
    oneV : Value
    expV logV : Value → Value
    subV mulV divV : Value → Value → Value

open RewriteOperations public

evaluateExpr :
  (O : RewriteOperations) →
  (Var → Value O) →
  RewriteExpr →
  Value O
evaluateExpr O ρ (variableR x) = ρ x
evaluateExpr O ρ oneR = oneV O
evaluateExpr O ρ (expR x) = expV O (evaluateExpr O ρ x)
evaluateExpr O ρ (logR x) = logV O (evaluateExpr O ρ x)
evaluateExpr O ρ (subR x y) =
  subV O (evaluateExpr O ρ x) (evaluateExpr O ρ y)
evaluateExpr O ρ (mulR x y) =
  mulV O (evaluateExpr O ρ x) (evaluateExpr O ρ y)
evaluateExpr O ρ (divR x y) =
  divV O (evaluateExpr O ρ x) (evaluateExpr O ρ y)

record RewriteSemanticModel
  (A : SideConditionAuthority) : Set₁ where
  field
    operations : RewriteOperations

    expLogSound :
      ∀ (ρ : Var → Value operations) x →
      Valid A (branchAdmissible x) →
      expV operations
        (logV operations (evaluateExpr operations ρ x))
      ≡ evaluateExpr operations ρ x

    logExpSound :
      ∀ (ρ : Var → Value operations) x →
      Valid A (principalStrip x) →
      logV operations
        (expV operations (evaluateExpr operations ρ x))
      ≡ evaluateExpr operations ρ x

    cancelMulDivSound :
      ∀ (ρ : Var → Value operations) x y →
      Valid A (nonzero y) →
      mulV operations
        (divV operations
          (evaluateExpr operations ρ x)
          (evaluateExpr operations ρ y))
        (evaluateExpr operations ρ y)
      ≡ evaluateExpr operations ρ x

    cancelDivMulSound :
      ∀ (ρ : Var → Value operations) x y →
      Valid A (nonzero y) →
      divV operations
        (mulV operations
          (evaluateExpr operations ρ x)
          (evaluateExpr operations ρ y))
        (evaluateExpr operations ρ y)
      ≡ evaluateExpr operations ρ x

open RewriteSemanticModel public

binaryCongruence :
  ∀ {A B C : Set}
    (f : A → B → C)
    {a a' : A} {b b' : B} →
  a ≡ a' →
  b ≡ b' →
  f a b ≡ f a' b'
binaryCongruence f refl refl = refl

rewriteCertificateSound :
  ∀ {A : SideConditionAuthority} →
  (M : RewriteSemanticModel A) →
  (ρ : Var → Value (operations M)) →
  ∀ {x y} →
  RewriteCertificate A x y →
  evaluateExpr (operations M) ρ x
  ≡ evaluateExpr (operations M) ρ y
rewriteCertificateSound M ρ rewriteRefl = refl
rewriteCertificateSound M ρ (rewriteSym certificate) =
  sym (rewriteCertificateSound M ρ certificate)
rewriteCertificateSound M ρ (rewriteTrans first second) =
  trans
    (rewriteCertificateSound M ρ first)
    (rewriteCertificateSound M ρ second)
rewriteCertificateSound M ρ (expCongruence certificate) =
  cong
    (expV (operations M))
    (rewriteCertificateSound M ρ certificate)
rewriteCertificateSound M ρ (logCongruence certificate) =
  cong
    (logV (operations M))
    (rewriteCertificateSound M ρ certificate)
rewriteCertificateSound M ρ (subCongruence left right) =
  binaryCongruence
    (subV (operations M))
    (rewriteCertificateSound M ρ left)
    (rewriteCertificateSound M ρ right)
rewriteCertificateSound M ρ (mulCongruence left right) =
  binaryCongruence
    (mulV (operations M))
    (rewriteCertificateSound M ρ left)
    (rewriteCertificateSound M ρ right)
rewriteCertificateSound M ρ (divCongruence left right) =
  binaryCongruence
    (divV (operations M))
    (rewriteCertificateSound M ρ left)
    (rewriteCertificateSound M ρ right)
rewriteCertificateSound M ρ (expLogStep x admissible) =
  expLogSound M ρ x admissible
rewriteCertificateSound M ρ (logExpStep x inStrip) =
  logExpSound M ρ x inStrip
rewriteCertificateSound M ρ (cancelMulDivStep x y nonzeroY) =
  cancelMulDivSound M ρ x y nonzeroY
rewriteCertificateSound M ρ (cancelDivMulStep x y nonzeroY) =
  cancelDivMulSound M ρ x y nonzeroY

certifiedCandidateSound :
  ∀ {A : SideConditionAuthority} →
  (M : RewriteSemanticModel A) →
  (C : CertifiedSearchCandidate A) →
  (ρ : Var → Value (operations M)) →
  evaluateExpr (operations M) ρ
    (normalizeTree C (tree (candidateData C)))
  ≡ evaluateExpr (operations M) ρ
      (targetExpression C (target (candidateData C)))
certifiedCandidateSound M C ρ =
  rewriteCertificateSound M ρ (certificateTrace C)
