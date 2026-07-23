module DASHI.Foundations.TernaryEMLDecision where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.TernaryElementaryOperatorCandidate
open import DASHI.Foundations.TernaryElementarySearchCertificate

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

emlSource : Var → Var → ExpLogSubExpr
emlSource left right = subE (expE (varE left)) (logE (varE right))

record ConcreteTernaryEMLContext : Set₁ where
  field
    Value : Set
    Environment : Set
    WitnessDomain : Value → Set
    SourceDomain : Environment → ExpLogSubExpr → Set
    DefinedTernary : Environment → Value → TernaryExpr → Set
    evaluateTernary : Environment → Value → TernaryExpr → Value
    evaluateSource : Environment → ExpLogSubExpr → Value

    witnessVariable leftVariable rightVariable : Var
    emlContext : TernaryExpr

    contextAdmissible : ∀ ρ witness →
      WitnessDomain witness →
      SourceDomain ρ (emlSource leftVariable rightVariable) →
      DefinedTernary ρ witness emlContext

    contextCorrect : ∀ ρ witness →
      (witnessOK : WitnessDomain witness) →
      (sourceOK : SourceDomain ρ (emlSource leftVariable rightVariable)) →
      evaluateTernary ρ witness emlContext
      ≡ evaluateSource ρ (emlSource leftVariable rightVariable)

    witnessIndependent : ∀ ρ a b →
      (aOK : WitnessDomain a) →
      (bOK : WitnessDomain b) →
      (sourceOK : SourceDomain ρ (emlSource leftVariable rightVariable)) →
      evaluateTernary ρ a emlContext
      ≡ evaluateTernary ρ b emlContext

open ConcreteTernaryEMLContext public

record TernaryDomainObstruction : Set₁ where
  field
    Value : Set
    CandidateDomain : Value → Set
    generatedUnit : Value → Value
    unitValue : Value
    validFirstArgument : Value → Set

    diagonalGeneratesUnit :
      ∀ a → CandidateDomain a → generatedUnit a ≡ unitValue

    generatedUnitCannotBeFirstArgument :
      ∀ a → CandidateDomain a → validFirstArgument (generatedUnit a) → ⊥

open TernaryDomainObstruction public

record FiniteDepthRefutation : Set₁ where
  field
    depthBound : Nat
    candidateAtDepth : TernaryExpr → Set
    representsEML : TernaryExpr → Set
    coveredAtBound : TernaryExpr → Set

    coverageSound :
      ∀ t → candidateAtDepth t → coveredAtBound t

    noCandidateRepresentsEML :
      ∀ t → coveredAtBound t → representsEML t → ⊥

open FiniteDepthRefutation public

data TernaryEMLDecision : Set₁ where
  represented : ConcreteTernaryEMLContext → TernaryEMLDecision
  domainRefuted : TernaryDomainObstruction → TernaryEMLDecision
  finiteDepthRefuted : FiniteDepthRefutation → TernaryEMLDecision

record CertifiedTernaryResearchOutcome : Set₁ where
  field
    outcome : TernaryEMLDecision
    NumericalScoutEvidence : Set
    numericalScoutCannotPromote : NumericalScoutEvidence → Set

open CertifiedTernaryResearchOutcome public
