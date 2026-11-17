module DASHI.Foundations.TernaryElementaryExactSearch where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Foundations.ElementarySingleOperator using (Var)
open import DASHI.Foundations.TernaryElementaryOperatorCandidate
  using (TernaryExpr; varT; nodeT)
open import DASHI.Foundations.TernaryElementarySearchCertificate

------------------------------------------------------------------------
-- Canonical variable substitution and renaming.

sameVar : Var → Var → Set
sameVar x y = x ≡ y

renameTernary :
  (Var → Var) →
  TernaryExpr →
  TernaryExpr
renameTernary rename (varT x) = varT (rename x)
renameTernary rename (nodeT a b c) =
  nodeT
    (renameTernary rename a)
    (renameTernary rename b)
    (renameTernary rename c)

substituteTernary :
  (Var → TernaryExpr) →
  TernaryExpr →
  TernaryExpr
substituteTernary substitution (varT x) = substitution x
substituteTernary substitution (nodeT a b c) =
  nodeT
    (substituteTernary substitution a)
    (substituteTernary substitution b)
    (substituteTernary substitution c)

identitySubstitution : Var → TernaryExpr
identitySubstitution = varT

substituteIdentity :
  ∀ tree →
  substituteTernary identitySubstitution tree ≡ tree
substituteIdentity (varT x) = refl
substituteIdentity (nodeT a b c)
  rewrite substituteIdentity a
        | substituteIdentity b
        | substituteIdentity c = refl

composeSubstitution :
  (Var → TernaryExpr) →
  (Var → TernaryExpr) →
  Var →
  TernaryExpr
composeSubstitution outer inner x =
  substituteTernary outer (inner x)

substitutionComposition :
  ∀ outer inner tree →
  substituteTernary outer (substituteTernary inner tree)
  ≡ substituteTernary (composeSubstitution outer inner) tree
substitutionComposition outer inner (varT x) = refl
substitutionComposition outer inner (nodeT a b c)
  rewrite substitutionComposition outer inner a
        | substitutionComposition outer inner b
        | substitutionComposition outer inner c = refl

------------------------------------------------------------------------
-- Proof-carrying structural and semantic representative tables.

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

record Representative
  (Equivalent : TernaryExpr → TernaryExpr → Set)
  (output : List TernaryExpr)
  (inputTree : TernaryExpr)
  : Set₁ where

  field
    representativeTree : TernaryExpr
    representativePresent : representativeTree ∈ output
    representativeCorrect : Equivalent inputTree representativeTree

open Representative public

record ProofCarryingDeduplicator : Set₁ where
  field
    Equivalent : TernaryExpr → TernaryExpr → Set
    reflexive : ∀ tree → Equivalent tree tree
    symmetric : ∀ {a b} → Equivalent a b → Equivalent b a
    transitive : ∀ {a b c} → Equivalent a b → Equivalent b c → Equivalent a c

    deduplicate : List TernaryExpr → List TernaryExpr
    completeRepresentatives :
      ∀ {input tree} →
      tree ∈ input →
      Representative Equivalent (deduplicate input) tree

open ProofCarryingDeduplicator public

record SemanticDeduplicationModel : Set₁ where
  field
    Value : Set
    Environment : Set
    evaluate : Environment → TernaryExpr → Value

  SemanticallyEquivalent : TernaryExpr → TernaryExpr → Set
  SemanticallyEquivalent left right =
    ∀ environment → evaluate environment left ≡ evaluate environment right

open SemanticDeduplicationModel public

semanticReflexive :
  ∀ model tree →
  SemanticallyEquivalent model tree tree
semanticReflexive model tree environment = refl

semanticSymmetric :
  ∀ model {a b} →
  SemanticallyEquivalent model a b →
  SemanticallyEquivalent model b a
semanticSymmetric model equivalence environment
  rewrite equivalence environment = refl

semanticTransitive :
  ∀ model {a b c} →
  SemanticallyEquivalent model a b →
  SemanticallyEquivalent model b c →
  SemanticallyEquivalent model a c
semanticTransitive model left right environment
  rewrite left environment | right environment = refl

------------------------------------------------------------------------
-- Literal enumeration accounting.  Exact cardinality proofs are separated from
-- the list generator so implementations may use lists, vectors, or finite sets.

record EnumerationCardinalityReceipt : Set₁ where
  field
    variables : Nat
    maximumDepth : Nat
    literalCandidateCount : Nat
    recurrenceCount : Nat → Nat

    depthZeroCount : recurrenceCount zero ≡ variables
    successorCount :
      ∀ depth →
      recurrenceCount (suc depth)
      ≡ recurrenceCount depth
        + (recurrenceCount depth
          + recurrenceCount depth
          + recurrenceCount depth)

    literalCountCorrect :
      literalCandidateCount ≡ recurrenceCount maximumDepth

open EnumerationCardinalityReceipt public

------------------------------------------------------------------------
-- External certificate serialization remains data, not authority.  Promotion
-- requires reconstruction of the indexed Agda certificate trace.

record SerializedRewriteStep : Set where
  field
    ruleCode : Nat
    leftNode : Nat
    rightNode : Nat
    sideConditionNode : Nat

open SerializedRewriteStep public

record SerializedCandidateCertificate : Set where
  field
    targetCode : Nat
    treeCode : Nat
    serializedSteps : List SerializedRewriteStep

open SerializedCandidateCertificate public

record CertificateDecoder
  (A : SideConditionAuthority)
  : Set₁ where

  field
    decodeExpression : Nat → RewriteExpr
    decodeTarget : Nat → SearchTarget
    decodeTree : Nat → TernaryExpr

    decodeCertified :
      SerializedCandidateCertificate →
      Σ SearchCandidate
        (λ candidateData →
          status candidateData ≡ certified)

open CertificateDecoder public

------------------------------------------------------------------------
-- Automated rejection boundary: one admissible semantic counterexample refutes
-- a candidate, but never promotes a surviving numerical scout.

record RefutationReceipt
  (Value : Set)
  (evaluate : RewriteExpr → Value)
  : Set₁ where

  field
    rejectedCandidate : SearchCandidate
    candidateExpression : RewriteExpr
    targetExpression : RewriteExpr
    counterexample :
      SemanticCounterexample Value evaluate
        candidateExpression targetExpression
    statusIsRefuted : status rejectedCandidate ≡ refuted

open RefutationReceipt public
