module DASHI.Core.CostedFibreEliminationChoiceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.FibreRefinementExperimentSelectionBidiExact as Fibre
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Cost

------------------------------------------------------------------------
-- COSTED EXPERIMENT CHOICE -> PROOF-BEARING FIBRE ELIMINATION
--
-- Cost and information gain remain separate coordinates.  A selected move must
-- carry both a declared resource cost and an actual compatible-fibre refinement
-- receipt.  Cheapest means cheapest among declared strict refinements only.
------------------------------------------------------------------------

record CostedRefinementCandidate {Hidden Experiment : Set}
    (prior : Bidi.ResidualFibre Hidden) : Set₁ where
  constructor costed-refinement-candidate
  field
    refinement : Fibre.ExperimentRefinementReceipt {Hidden} {Experiment} prior
    move : Cost.InformationMove
    moveExperimentReference : String
    admissibilityReference : String

open CostedRefinementCandidate public

record CheapestStrictFibreElimination {Hidden Experiment : Set}
    (prior : Bidi.ResidualFibre Hidden)
    (Declared : CostedRefinementCandidate {Hidden} {Experiment} prior → Set) : Set₁ where
  constructor cheapest-strict-fibre-elimination
  field
    selected : CostedRefinementCandidate {Hidden} {Experiment} prior
    selectedDeclared : Declared selected
    selectedStrict : Fibre.grade (refinement selected) ≡ Fibre.strictRefinement
    minimal :
      (alternative : CostedRefinementCandidate {Hidden} {Experiment} prior) →
      Declared alternative →
      Fibre.grade (refinement alternative) ≡ Fibre.strictRefinement →
      Cost.cost (move selected) ≤ Cost.cost (move alternative)
    comparisonReference : String

open CheapestStrictFibreElimination public

selectedExperimentEliminatesPriorCandidate :
  ∀ {Hidden Experiment : Set}
    {prior : Bidi.ResidualFibre Hidden}
    {Declared : CostedRefinementCandidate {Hidden} {Experiment} prior → Set} →
  (choice : CheapestStrictFibreElimination prior Declared) →
  Σ Hidden
    (λ hidden →
      prior hidden ×
      ¬ (Fibre.posterior (refinement (selected choice)) hidden))
selectedExperimentEliminatesPriorCandidate choice =
  Fibre.strictReceiptEliminatesPriorCandidate
    (refinement (selected choice))
    (selectedStrict choice)

------------------------------------------------------------------------
-- No-collapse boundaries.
------------------------------------------------------------------------

data CheapestStrictRefinementIsScientificallyBest : Set where
data LowerCostCreatesLargerFibreReduction : Set where
data StrictFibreReductionCreatesDeploymentAuthority : Set where

cheapestStrictDoesNotMeanScientificallyBest :
  CheapestStrictRefinementIsScientificallyBest → ⊥
cheapestStrictDoesNotMeanScientificallyBest ()

lowerCostDoesNotCreateLargerFibreReduction :
  LowerCostCreatesLargerFibreReduction → ⊥
lowerCostDoesNotCreateLargerFibreReduction ()

strictReductionDoesNotCreateDeploymentAuthority :
  StrictFibreReductionCreatesDeploymentAuthority → ⊥
strictReductionDoesNotCreateDeploymentAuthority ()

record CostedFibreEliminationBoundary : Set where
  constructor costed-fibre-elimination-boundary
  field
    selectedMoveCarriesCostAndRefinement : Bool
    strictSelectionCarriesEliminatedCandidate : Bool
    cheapestMeansGloballyBestExperiment : Bool
    costDeterminesInformationGain : Bool
    fibreReductionCreatesAuthority : Bool

canonicalCostedFibreEliminationBoundary : CostedFibreEliminationBoundary
canonicalCostedFibreEliminationBoundary =
  costed-fibre-elimination-boundary true true false false false
