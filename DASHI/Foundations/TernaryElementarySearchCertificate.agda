module DASHI.Foundations.TernaryElementarySearchCertificate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)

open import DASHI.Foundations.ElementarySingleOperator using (Var)
open import DASHI.Foundations.TernaryElementaryOperatorCandidate
  using (TernaryExpr; varT; nodeT)

------------------------------------------------------------------------
-- Structural accounting for bounded enumeration.

nodeCount : TernaryExpr → Nat
nodeCount (varT _) = suc zero
nodeCount (nodeT a b c) =
  suc (nodeCount a + nodeCount b + nodeCount c)

structuralDepthUpperBound : TernaryExpr → Nat
structuralDepthUpperBound (varT _) = zero
structuralDepthUpperBound (nodeT a b c) =
  suc
    (structuralDepthUpperBound a
     + structuralDepthUpperBound b
     + structuralDepthUpperBound c)

variableOccurrences : Var → TernaryExpr → Nat
variableOccurrences x (varT y) = occurrencesAtVariable x y
  where
    occurrencesAtVariable : Var → Var → Nat
    occurrencesAtVariable zero zero = suc zero
    occurrencesAtVariable zero (suc _) = zero
    occurrencesAtVariable (suc _) zero = zero
    occurrencesAtVariable (suc a) (suc b) = occurrencesAtVariable a b
variableOccurrences x (nodeT a b c) =
  variableOccurrences x a
  + variableOccurrences x b
  + variableOccurrences x c

------------------------------------------------------------------------
-- Candidate governance.

data SearchTarget : Set where
  unitTarget : SearchTarget
  expTarget : SearchTarget
  logTarget : SearchTarget
  subtractionTarget : SearchTarget
  emlTarget : SearchTarget

data CandidateStatus : Set where
  scoutOnly : CandidateStatus
  symbolicCandidate : CandidateStatus
  certified : CandidateStatus
  refuted : CandidateStatus

record SearchCandidate : Set where
  constructor candidate
  field
    target : SearchTarget
    tree : TernaryExpr
    status : CandidateStatus
    claimedDepth : Nat
    claimedNodeCount : Nat
    depthClaimCorrect :
      claimedDepth ≡ structuralDepthUpperBound tree
    nodeClaimCorrect :
      claimedNodeCount ≡ nodeCount tree

open SearchCandidate public

------------------------------------------------------------------------
-- Exact symbolic certificate language.  Rewrites involving exp/log require a
-- proof of the corresponding branch or nonzero side condition.

data RewriteExpr : Set where
  variableR : Var → RewriteExpr
  oneR : RewriteExpr
  expR logR : RewriteExpr → RewriteExpr
  subR mulR divR : RewriteExpr → RewriteExpr → RewriteExpr

data SideCondition : Set where
  branchAdmissible : RewriteExpr → SideCondition
  principalStrip : RewriteExpr → SideCondition
  nonzero : RewriteExpr → SideCondition

record SideConditionAuthority : Set₁ where
  field
    Valid : SideCondition → Set

open SideConditionAuthority public

data RewriteCertificate
  (A : SideConditionAuthority) :
  RewriteExpr → RewriteExpr → Set where

  rewriteRefl :
    ∀ {x} →
    RewriteCertificate A x x

  rewriteSym :
    ∀ {x y} →
    RewriteCertificate A x y →
    RewriteCertificate A y x

  rewriteTrans :
    ∀ {x y z} →
    RewriteCertificate A x y →
    RewriteCertificate A y z →
    RewriteCertificate A x z

  expCongruence :
    ∀ {x y} →
    RewriteCertificate A x y →
    RewriteCertificate A (expR x) (expR y)

  logCongruence :
    ∀ {x y} →
    RewriteCertificate A x y →
    RewriteCertificate A (logR x) (logR y)

  subCongruence :
    ∀ {a b c d} →
    RewriteCertificate A a b →
    RewriteCertificate A c d →
    RewriteCertificate A (subR a c) (subR b d)

  mulCongruence :
    ∀ {a b c d} →
    RewriteCertificate A a b →
    RewriteCertificate A c d →
    RewriteCertificate A (mulR a c) (mulR b d)

  divCongruence :
    ∀ {a b c d} →
    RewriteCertificate A a b →
    RewriteCertificate A c d →
    RewriteCertificate A (divR a c) (divR b d)

  expLogStep :
    ∀ x →
    Valid A (branchAdmissible x) →
    RewriteCertificate A (expR (logR x)) x

  logExpStep :
    ∀ x →
    Valid A (principalStrip x) →
    RewriteCertificate A (logR (expR x)) x

  cancelMulDivStep :
    ∀ x y →
    Valid A (nonzero y) →
    RewriteCertificate A
      (mulR (divR x y) y)
      x

  cancelDivMulStep :
    ∀ x y →
    Valid A (nonzero y) →
    RewriteCertificate A
      (divR (mulR x y) y)
      x

------------------------------------------------------------------------
-- The external enumerator supplies a normalizer from ternary trees to the
-- exact rewrite language.  Agda accepts promotion only when the returned trace
-- is inhabited.

record CertifiedSearchCandidate
  (A : SideConditionAuthority) : Set₁ where
  field
    candidateData : SearchCandidate
    normalizeTree : TernaryExpr → RewriteExpr
    targetExpression : SearchTarget → RewriteExpr
    certificateTrace :
      RewriteCertificate A
        (normalizeTree (tree candidateData))
        (targetExpression (target candidateData))
    candidateStatusIsCertified :
      status candidateData ≡ certified

open CertifiedSearchCandidate public

record SemanticCounterexample
  (Value : Set)
  (evaluate : RewriteExpr → Value)
  (candidateExpression targetExpression : RewriteExpr) : Set₁ where
  field
    valuesDiffer :
      evaluate candidateExpression ≡ evaluate targetExpression →
      ⊥

------------------------------------------------------------------------
-- The known diagonal unit remains a symbolic candidate until its analytic
-- side conditions are certified for the selected scalar model.

diagonalUnitSearchCandidate : Var → SearchCandidate
diagonalUnitSearchCandidate witness =
  candidate
    unitTarget
    (nodeT (varT witness) (varT witness) (varT witness))
    symbolicCandidate
    (suc zero)
    (suc (suc zero + suc zero + suc zero))
    refl
    refl
