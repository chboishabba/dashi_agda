module DASHI.Belief.BayesianEvidenceIntegration where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Sketch layer for guarded belief updates:
-- admissibility constrains which hypotheses can absorb evidence,
-- likelihood absorbs observations,
-- MDL-style complexity penalizes overcomplicated explanations.

record WeightStructure {ℓ : Level} : Set (lsuc ℓ) where
  field
    Weight : Set ℓ
    0# 1# : Weight
    _+_ _*_ : Weight → Weight → Weight

open WeightStructure public

record BayesianEvidenceModel
  {ℓh ℓo ℓw : Level}
  (Hypothesis : Set ℓh)
  (Observation : Set ℓo)
  (W : WeightStructure {ℓw})
  : Set (lsuc (ℓh ⊔ ℓo ⊔ ℓw)) where
  open WeightStructure W

  private
    module WS = WeightStructure W
    Weight′ = WeightStructure.Weight W
    _⊕_ = WeightStructure._+_ W
    _⊗_ = WeightStructure._*_ W

  field
    prior : Hypothesis → Weight′
    likelihood : Hypothesis → Observation → Weight′
    complexityPenalty : Hypothesis → Weight′

    -- Guarded transitions / admissibility gate.
    admissible : Hypothesis → Observation → Bool

  boolWeight : Bool → Weight′
  boolWeight true = WS.1#
  boolWeight false = WS.0#

  guardWeight : Hypothesis → Observation → Weight′
  guardWeight h o = boolWeight (admissible h o)

  evidenceFactor : Hypothesis → Observation → Weight′
  evidenceFactor h o =
    guardWeight h o ⊗ likelihood h o

  stepScore : Hypothesis → Observation → Weight′
  stepScore h o =
    (prior h ⊗ evidenceFactor h o) ⊗ complexityPenalty h

open BayesianEvidenceModel public

record SequentialBeliefUpdate
  {ℓh ℓo ℓw : Level}
  (Hypothesis : Set ℓh)
  (Observation : Set ℓo)
  (W : WeightStructure {ℓw})
  : Set (lsuc (ℓh ⊔ ℓo ⊔ ℓw)) where
  open WeightStructure W

  private
    module WS = WeightStructure W
    Weight′ = WeightStructure.Weight W
    _⊗_ = WeightStructure._*_ W

  field
    Model : BayesianEvidenceModel Hypothesis Observation W
    updatePrior : Hypothesis → Weight′ → Weight′

  private
    module M = BayesianEvidenceModel Model

  posteriorStep : Hypothesis → Observation → Weight′
  posteriorStep h o =
    (updatePrior h (M.prior h) ⊗ M.evidenceFactor h o) ⊗ M.complexityPenalty h

  posteriorFrom : Hypothesis → List Observation → Weight′
  posteriorFrom h [] = M.prior h ⊗ M.complexityPenalty h
  posteriorFrom h (o ∷ os) =
    updatePrior h (posteriorFrom h os) ⊗ M.evidenceFactor h o

open SequentialBeliefUpdate public

record CompetingHypotheses
  {ℓh ℓo ℓw : Level}
  (Hypothesis : Set ℓh)
  (Observation : Set ℓo)
  (W : WeightStructure {ℓw})
  : Set (lsuc (ℓh ⊔ ℓo ⊔ ℓw)) where
  open WeightStructure W

  private
    module WS = WeightStructure W
    Weight′ = WeightStructure.Weight W

  field
    Belief : SequentialBeliefUpdate Hypothesis Observation W
    aggregate : List Weight′ → Weight′
    normalize : Weight′ → Weight′ → Weight′

  private
    module B = SequentialBeliefUpdate Belief

  rawPosterior : Hypothesis → List Observation → Weight′
  rawPosterior = B.posteriorFrom

  normalizedPosterior :
    Hypothesis → List Hypothesis → List Observation → Weight′
  normalizedPosterior h hs os =
    normalize (rawPosterior h os) (aggregate (scores hs))
    where
    scores : List Hypothesis → List Weight′
    scores [] = []
    scores (x ∷ xs) = rawPosterior x os ∷ scores xs

open CompetingHypotheses public

-- A small law-shaped seam: contradictory evidence should be able to zero out
-- a hypothesis through the guard, even if its prior is nonzero.
record ContradictionEliminates
  {ℓh ℓo ℓw : Level}
  {Hypothesis : Set ℓh}
  {Observation : Set ℓo}
  {W : WeightStructure {ℓw}}
  (Model : BayesianEvidenceModel Hypothesis Observation W)
  : Set (lsuc (ℓh ⊔ ℓo ⊔ ℓw)) where
  open WeightStructure W

  private
    module WS = WeightStructure W
    module M = BayesianEvidenceModel Model

  field
    guarded-out-zero :
      ∀ h o → M.admissible h o ≡ false → M.evidenceFactor h o ≡ WS.0#

-- Intended composition with existing DASHI layers:
-- 1. ultrametric neighborhoods can shape priors,
-- 2. guarded transitions provide admissibility,
-- 3. MDL provides complexityPenalty,
-- 4. normalized posterior expresses event truth under conflicting evidence.
