module DASHI.Reasoning.GeometricPairedBenchmarkNonCollapseExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- DASHI-authored, finite synthetic counterexample, NOT a reproduction of
-- Sophontic's weights, company model or released ConvergeMini benchmark.
-- Sophontic's public eval description (as read 2026-10-24) motivates the
-- distinction between item correctness and paired load-bearing changes:
-- https://sophontic.ai/evals/ . Original source authorship retained.
-- Reuse on sibling PR #1095: SemanticInterventionEquivarianceExact,
-- GeometricReasoningCandidateSelectionExact and dependent surface/residual.
-- No cross-branch source is silently claimed to have been kernel-imported.
------------------------------------------------------------------------

data Prompt : Set where
  canonical : Prompt
  perturbed : Prompt
  annotatedCanonical : Prompt
  annotatedPerturbed : Prompt

reference : Prompt → Bool
reference canonical = false
reference perturbed = true
reference annotatedCanonical = false
reference annotatedPerturbed = true

-- This deliberately superficial function passes both seen examples.
memorisedPair : Prompt → Bool
memorisedPair canonical = false
memorisedPair perturbed = true
memorisedPair annotatedCanonical = false
memorisedPair annotatedPerturbed = false

factSensitive : Prompt → Bool
factSensitive = reference

flipPremise : Prompt → Prompt
flipPremise canonical = perturbed
flipPremise perturbed = canonical
flipPremise annotatedCanonical = annotatedPerturbed
flipPremise annotatedPerturbed = annotatedCanonical

flipResponse : Bool → Bool
flipResponse false = true
flipResponse true = false

record PairedCorrect (predict : Prompt → Bool) : Set where
  field
    canonicalCorrect : predict canonical ≡ reference canonical
    perturbationCorrect : predict perturbed ≡ reference perturbed

open PairedCorrect public

memorisedPassesPair : PairedCorrect memorisedPair
memorisedPassesPair = record
  { canonicalCorrect = refl
  ; perturbationCorrect = refl
  }

factSensitivePassesPair : PairedCorrect factSensitive
factSensitivePassesPair = record
  { canonicalCorrect = refl
  ; perturbationCorrect = refl
  }

samePairObservation :
  (memorisedPair canonical ≡ factSensitive canonical) ×
  (memorisedPair perturbed ≡ factSensitive perturbed)
samePairObservation = refl , refl

record NuisanceStable (predict : Prompt → Bool) : Set where
  field
    canonicalStable : predict annotatedCanonical ≡ predict canonical
    perturbedStable : predict annotatedPerturbed ≡ predict perturbed

open NuisanceStable public

factSensitiveStable : NuisanceStable factSensitive
factSensitiveStable = record
  { canonicalStable = refl
  ; perturbedStable = refl
  }

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

memorisedNotStable : NuisanceStable memorisedPair → ⊥
memorisedNotStable stability = falseNotTrue (perturbedStable stability)

pairedCorrectDoesNotForceNuisanceStability :
  (∀ predict → PairedCorrect predict → NuisanceStable predict) → ⊥
pairedCorrectDoesNotForceNuisanceStability assertion =
  memorisedNotStable (assertion memorisedPair memorisedPassesPair)

record PremiseFlipEquivariant (predict : Prompt → Bool) : Set where
  field
    commutesWithFlip :
      (prompt : Prompt) →
      predict (flipPremise prompt) ≡ flipResponse (predict prompt)

open PremiseFlipEquivariant public

factSensitiveFlipEquivariant : PremiseFlipEquivariant factSensitive
factSensitiveFlipEquivariant = record
  { commutesWithFlip = λ
      { canonical → refl
      ; perturbed → refl
      ; annotatedCanonical → refl
      ; annotatedPerturbed → refl
      }
  }

memorisedNotFlipEquivariant : PremiseFlipEquivariant memorisedPair → ⊥
memorisedNotFlipEquivariant evidence =
  falseNotTrue (commutesWithFlip evidence annotatedCanonical)

pairedCorrectDoesNotForceActionEquivariance :
  (∀ predict → PairedCorrect predict → PremiseFlipEquivariant predict) → ⊥
pairedCorrectDoesNotForceActionEquivariance assertion =
  memorisedNotFlipEquivariant (assertion memorisedPair memorisedPassesPair)

------------------------------------------------------------------------
-- Exact finite witness, deliberately limited inference:
-- * paired correctness does not imply nuisance stability;
-- * paired correctness does not imply premise-flip equivariance on all inputs;
-- * identical two-item outputs cannot identify a latent geometric mechanism.
-- It does NOT show Sophontic's candidate is wrong or prove factSensitive is
-- geometrically realised in any empirical neural language model.
------------------------------------------------------------------------
