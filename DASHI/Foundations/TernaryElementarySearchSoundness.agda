module DASHI.Foundations.TernaryElementarySearchSoundness where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.ElementarySingleOperator using (Var)
open import DASHI.Foundations.TernaryElementarySearchCertificate

------------------------------------------------------------------------
-- A certificate is promoted only relative to a semantic model whose primitive
-- side-condition rules are themselves proved.  Thus the external search may
-- propose a trace, but Agda checks both the trace and every analytic premise.

record RewriteSemanticModel
  (A : SideConditionAuthority) : Set₁ where
  field
    Value : Set
    oneV : Value
    expV logV : Value → Value
    subV mulV divV : Value → Value → Value

    expLogSound :
      ∀ (ρ : Var → Value) x →
      Valid A (branchAdmissible x) →
      expV (logV (evaluateExpr ρ x)) ≡ evaluateExpr ρ x

    logExpSound :
      ∀ (ρ : Var → Value) x →
      Valid A (principalStrip x) →
      logV (expV (evaluateExpr ρ x)) ≡ evaluateExpr ρ x

    cancelMulDivSound :
      ∀ (ρ : Var → Value) x y →
      Valid A (nonzero y) →
      mulV
        (divV (evaluateExpr ρ x) (evaluateExpr ρ y))
        (evaluateExpr ρ y)
      ≡ evaluateExpr ρ x

    cancelDivMulSound :
      ∀ (ρ : Var → Value) x y →
      Valid A (nonzero y) →
      divV
        (mulV (evaluateExpr ρ x) (evaluateExpr ρ y))
        (evaluateExpr ρ y)
      ≡ evaluateExpr ρ x

  evaluateExpr : (Var → Value) → RewriteExpr → Value
  evaluateExpr ρ (variableR x) = ρ x
  evaluateExpr ρ oneR = oneV
  evaluateExpr ρ (expR x) = expV (evaluateExpr ρ x)
  evaluateExpr ρ (logR x) = logV (evaluateExpr ρ x)
  evaluateExpr ρ (subR x y) =
    subV (evaluateExpr ρ x) (evaluateExpr ρ y)
  evaluateExpr ρ (mulR x y) =
    mulV (evaluateExpr ρ x) (evaluateExpr ρ y)
  evaluateExpr ρ (divR x y) =
    divV (evaluateExpr ρ x) (evaluateExpr ρ y)

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
  (ρ : Var → Value M) →
  ∀ {x y} →
  RewriteCertificate A x y →
  evaluateExpr M ρ x ≡ evaluateExpr M ρ y
rewriteCertificateSound M ρ rewriteRefl = refl
rewriteCertificateSound M ρ (rewriteSym certificate) =
  sym (rewriteCertificateSound M ρ certificate)
rewriteCertificateSound M ρ (rewriteTrans first second) =
  trans
    (rewriteCertificateSound M ρ first)
    (rewriteCertificateSound M ρ second)
rewriteCertificateSound M ρ (expCongruence certificate) =
  cong (expV M) (rewriteCertificateSound M ρ certificate)
rewriteCertificateSound M ρ (logCongruence certificate) =
  cong (logV M) (rewriteCertificateSound M ρ certificate)
rewriteCertificateSound M ρ (subCongruence left right) =
  binaryCongruence
    (subV M)
    (rewriteCertificateSound M ρ left)
    (rewriteCertificateSound M ρ right)
rewriteCertificateSound M ρ (mulCongruence left right) =
  binaryCongruence
    (mulV M)
    (rewriteCertificateSound M ρ left)
    (rewriteCertificateSound M ρ right)
rewriteCertificateSound M ρ (divCongruence left right) =
  binaryCongruence
    (divV M)
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
  (ρ : Var → Value M) →
  evaluateExpr M ρ
    (normalizeTree C (tree (candidateData C)))
  ≡ evaluateExpr M ρ
      (targetExpression C (target (candidateData C)))
certifiedCandidateSound M C ρ =
  rewriteCertificateSound M ρ (certificateTrace C)
