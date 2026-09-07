module DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierNoScalarizationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto

------------------------------------------------------------------------
-- A Pareto frontier is not definitionally a single selected move.
-- DASHI synthesis; no external legal proposition is introduced.
------------------------------------------------------------------------

data ParetoFrontierMustHaveExactlyOneCell : Set where

frontierMultiplicityIsNotAnError : ParetoFrontierMustHaveExactlyOneCell → ⊥
frontierMultiplicityIsNotAnError ()

twoUndominatedCellsExist :
  Pareto.paretoFrontier Pareto.toyPortfolio
  ≡ Pareto.cheapCell ∷ Pareto.highGainCell ∷ []
twoUndominatedCellsExist = Pareto.toyFrontierHasTwoTradeoffs
