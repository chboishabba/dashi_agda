module DASHI.Core.SelfSealingTerminalisationExact where

------------------------------------------------------------------------
-- SELF-SEALING TERMINALISATION
--
-- A terminal classifier is stronger than an idempotent map.  This module
-- separates three independent ingredients:
--   * idempotence,
--   * distinction loss (constructive non-injectivity witness), and
--   * closure of a selected terminal class under declared counterevidence.
--
-- No political/clinical label is privileged by this generic construction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

record IdempotentClassifier (State Class : Set) : Set₁ where
  constructor idempotentClassifier
  field
    classify : State → Class
    reify : Class → State
    idempotent : ∀ state → classify (reify (classify state)) ≡ classify state

open IdempotentClassifier public

record DistinctionLossWitness
    {State Class : Set}
    (classify : State → Class) : Set₁ where
  constructor distinctionLossWitness
  field
    left right : State
    sameClass : classify left ≡ classify right
    genuinelyDistinct : left ≡ right → ⊥

open DistinctionLossWitness public

record CounterevidenceClosure
    (Class Evidence : Set)
    (update : Class → Evidence → Class)
    (Terminal : Class → Set) : Set₁ where
  constructor counterevidenceClosure
  field
    terminalClosed : ∀ {class} → Terminal class → (evidence : Evidence) → Terminal (update class evidence)

open CounterevidenceClosure public

record SelfSealingTerminalisation
    (State Class Evidence : Set)
    (classifier : IdempotentClassifier State Class)
    (update : Class → Evidence → Class)
    (Terminal : Class → Set) : Set₁ where
  constructor selfSealingTerminalisation
  field
    distinctionLoss : DistinctionLossWitness (classify classifier)
    counterevidenceClosed : CounterevidenceClosure Class Evidence update Terminal

open SelfSealingTerminalisation public

------------------------------------------------------------------------
-- Anti-terminalisation / corrective reopening is a genuinely different
-- witness: some declared correcting evidence must leave the terminal region.
------------------------------------------------------------------------

record CorrectiveReopeningWitness
    (Class Evidence : Set)
    (update : Class → Evidence → Class)
    (Terminal : Class → Set) : Set₁ where
  constructor correctiveReopeningWitness
  field
    before : Class
    correctingEvidence : Evidence
    beforeTerminal : Terminal before
    afterNotTerminal : Terminal (update before correctingEvidence) → ⊥

open CorrectiveReopeningWitness public

selfSealingContradictsCorrectiveReopening :
  ∀ {Class Evidence}
    {update : Class → Evidence → Class}
    {Terminal : Class → Set} →
  CounterevidenceClosure Class Evidence update Terminal →
  CorrectiveReopeningWitness Class Evidence update Terminal →
  ⊥
selfSealingContradictsCorrectiveReopening closed reopening =
  afterNotTerminal reopening
    (terminalClosed closed
      (beforeTerminal reopening)
      (correctingEvidence reopening))
