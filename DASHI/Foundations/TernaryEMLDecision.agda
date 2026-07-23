module DASHI.Foundations.TernaryEMLDecision where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)
open import Data.Empty using (⊥)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.TernaryElementaryOperatorCandidate
open import DASHI.Foundations.TernaryElementarySearchCertificate

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record ConcreteTernaryEMLContext : Set₁ where
  field
    Value : Set
    Environment : Set
    WitnessDomain : Value → Set
    SourceDomain : Environment → EMLExpr → Set
    DefinedTernary : Environment → Value → TernaryExpr → Set
    evaluateTernary : Environment → Value → TernaryExpr → Value
    evaluateEML : Environment → EMLExpr → Value

    witnessVariable leftVariable rightVariable : Var
    emlContext : TernaryExpr

    contextAdmissible : ∀ ρ witness →
      WitnessDomain witness →
      SourceDomain ρ (emlE (varE leftVariable) (varE rightVariable)) →
      DefinedTernary ρ witness emlContext

    contextCorrect : ∀ ρ witness witnessOK sourceOK →
      evaluateTernary ρ witness emlContext
      ≡ evaluateEML ρ (emlE (varE leftVariable) (varE rightVariable))

    witnessIndependent : ∀ ρ a b aOK bOK sourceOK →
      evaluateTernary ρ a emlContext
      ≡ evaluateTernary ρ b emlContext

open ConcreteTernaryEMLContext public

record TernaryDomainObstruction : Set₁ where
  field
    Value : Set
    CandidateDomain : Value → Set
    generatedUnit : Value → Value
    validFirstArgument : Value → Set

    diagonalGeneratesUnit : ∀ a → CandidateDomain a → generatedUnit a ≡ generatedUnit a
    generatedUnitCannotBeFirstArgument :
      ∀ a → CandidateDomain a → validFirstArgument (generatedUnit a) → ⊥

open TernaryDomainObstruction public

record FiniteDepthRefutation : Set₁ where
  field
    depthBound : Nat
    candidateAtDepth : TernaryExpr → Set
    representsEML : TernaryExpr → Set
    allCandidatesCovered :
      ∀ t → candidateAtDepth t → structuralDepthUpperBound t ≡ depthBound → Set
    noCandidateRepresentsEML :
      ∀ t → candidateAtDepth t → representsEML t → ⊥

open FiniteDepthRefutation public

data TernaryEMLDecision : Set₁ where
  represented : ConcreteTernaryEMLContext → TernaryEMLDecision
  domainRefuted : TernaryDomainObstruction → TernaryEMLDecision
  finiteDepthRefuted : FiniteDepthRefutation → TernaryEMLDecision

record CertifiedTernaryResearchOutcome : Set₁ where
  field
    outcome : TernaryEMLDecision
    numericalScoutPromotesNothing : Set

open CertifiedTernaryResearchOutcome public
