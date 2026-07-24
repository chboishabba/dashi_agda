module DASHI.Foundations.TerminalTernaryEMLInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.TernaryElementaryOperatorCandidate
open import DASHI.Foundations.TernaryEMLDecision

terminalTernaryModel : TernaryModel
terminalTernaryModel =
  record
    { CarrierT = ⊤
    ; ternary = λ _ _ _ → tt
    }

terminalEMLModel : ExpLogSubModel
terminalEMLModel =
  record
    { Carrier = ⊤
    ; one = tt
    ; exp = λ _ → tt
    ; log = λ _ → tt
    ; sub = λ _ _ → tt
    }

terminalTernaryRepresentation :
  TernaryRepresentsEML terminalTernaryModel terminalEMLModel
terminalTernaryRepresentation =
  record
    { embedCarrier = λ _ → tt
    ; translate = translateTerminal
    ; translate-correct = λ ρ ρT agrees t → terminalCorrect ρ ρT t
    }
  where
    translateTerminal : EMLExpr → TernaryExpr
    translateTerminal oneM = varT zero
    translateTerminal (varM x) = varT x
    translateTerminal (emlM s t) =
      nodeT (translateTerminal s) (translateTerminal t) (translateTerminal t)

    terminalCorrect :
      ∀ ρ ρT t →
      evalTernary terminalTernaryModel ρT (translateTerminal t)
      ≡ evalEML terminalEMLModel ρ t
    terminalCorrect ρ ρT oneM = refl
    terminalCorrect ρ ρT (varM x) = refl
    terminalCorrect ρ ρT (emlM s t) = refl

terminalConcreteContext : ConcreteTernaryEMLContext
terminalConcreteContext =
  record
    { Value = ⊤
    ; Environment = ⊤
    ; WitnessDomain = λ _ → ⊤
    ; SourceDomain = λ _ _ → ⊤
    ; DefinedTernary = λ _ _ _ → ⊤
    ; evaluateTernary = λ _ _ _ → tt
    ; evaluateSource = λ _ _ → tt
    ; witnessVariable = zero
    ; leftVariable = suc zero
    ; rightVariable = suc (suc zero)
    ; emlContext = nodeT (varT (suc zero)) (varT (suc (suc zero))) (varT zero)
    ; contextAdmissible = λ _ _ _ _ → tt
    ; contextCorrect = λ _ _ _ _ → refl
    ; witnessIndependent = λ _ _ _ _ _ _ → refl
    }

terminalTernaryDecision : TernaryEMLDecision
terminalTernaryDecision = represented terminalConcreteContext

unitFirstArgumentObstruction :
  ∀ {Value : Set}
    (CandidateDomain : Value → Set)
    (generatedUnit : Value → Value)
    (unitValue : Value)
    (validFirstArgument : Value → Set) →
  (∀ a → CandidateDomain a → generatedUnit a ≡ unitValue) →
  (validFirstArgument unitValue → ⊥) →
  TernaryDomainObstruction
unitFirstArgumentObstruction CandidateDomain generatedUnit unitValue validFirstArgument diagonal unitInvalid =
  record
    { Value = _
    ; CandidateDomain = CandidateDomain
    ; generatedUnit = generatedUnit
    ; unitValue = unitValue
    ; validFirstArgument = validFirstArgument
    ; diagonalGeneratesUnit = diagonal
    ; generatedUnitCannotBeFirstArgument = λ a domain valid →
        unitInvalid (transportValid (diagonal a domain) valid)
    }
  where
    transportValid :
      ∀ {x y} → x ≡ y → validFirstArgument x → validFirstArgument y
    transportValid refl p = p
