module Ontology.BrainComputer.LogicTlureyQuotientBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import Base369 using (TriTruth)
open import LogicTlurey using (Stage; seed; counter; resonance; overflow; stageTone)
open import Ontology.DNA.TriTruthScanOrderBridge using
  (TriScanOrder; triScanOf)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

overflow≢seed : overflow ≢ seed
overflow≢seed ()

q-stage : Stage → TriTruth
q-stage = stageTone

overflow-seed-collapse : q-stage overflow ≡ q-stage seed
overflow-seed-collapse = refl

stageToneFactorsThroughQuotient :
  (s : Stage) →
  stageTone s ≡ q-stage s
stageToneFactorsThroughQuotient seed      = refl
stageToneFactorsThroughQuotient counter   = refl
stageToneFactorsThroughQuotient resonance = refl
stageToneFactorsThroughQuotient overflow  = refl

stageToTriScan : Stage → TriScanOrder
stageToTriScan s = triScanOf (q-stage s)

stageToTriScan-collapse :
  stageToTriScan overflow ≡ stageToTriScan seed
stageToTriScan-collapse = refl

record StageTriQuotientBridge : Set where
  constructor stageTriQuotientBridge
  field
    quotient : Stage → TriTruth
    collapsedPairDistinct : overflow ≢ seed
    collapsedPairEqual : quotient overflow ≡ quotient seed
    factorization :
      (s : Stage) →
      stageTone s ≡ quotient s

stageTriQuotientBridgeSurface : StageTriQuotientBridge
stageTriQuotientBridgeSurface =
  stageTriQuotientBridge
    q-stage
    overflow≢seed
    overflow-seed-collapse
    stageToneFactorsThroughQuotient
