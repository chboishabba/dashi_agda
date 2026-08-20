module DASHI.Physics.Closure.NSTriadKNInteriorEpisodeBudgetEquivalenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
--
-- DASHI ANTI-TAIL-CHASING THEOREM
--
-- For every interior adverse episode Round106 proves exactly
--
--   nu integral P_tau = g_tau integral F_tau.
--
-- This file folds that equality over a finite network with common viscosity.
-- Therefore a bound on the total weighted signed episode forcing is EQUIVALENT
-- to the corresponding bound on nu times total adverse production.  Merely
-- renaming the latter as a "signed forcing budget" is not a smaller Clay
-- theorem.
--
-- Progress can only come from substituting the LITERAL Navier--Stokes
-- self/external forcing and proving an independent structural estimate there.
-- This theorem prevents another sequence of frontier wrappers from being
-- counted as mathematical reduction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNSignedPhaseTimeNormalFormRound106Exact as Normal
import DASHI.Physics.Closure.NSTriadKNAdverseEpisodeSignedForcingRound106Exact as Episode

sumInteriorProduction : List Episode.InteriorAdverseSignedForcingEpisode → ℚ
sumInteriorProduction [] = 0ℚ
sumInteriorProduction (E ∷ Es) =
  Normal.integratedCriticalProduction (Episode.cell (Episode.episode E))
  + sumInteriorProduction Es

sumInteriorWeightedForcing :
  List Episode.InteriorAdverseSignedForcingEpisode → ℚ
sumInteriorWeightedForcing [] = 0ℚ
sumInteriorWeightedForcing (E ∷ Es) =
  Normal.normalFormWeight (Episode.cell (Episode.episode E))
    * Normal.integratedForcing (Episode.cell (Episode.episode E))
  + sumInteriorWeightedForcing Es

record CommonViscosityInteriorEpisodes : Set where
  constructor common-viscosity-interior-episodes
  field
    viscosity : ℚ
    episodes : List Episode.InteriorAdverseSignedForcingEpisode
    sameViscosity : (E : Episode.InteriorAdverseSignedForcingEpisode) →
      Normal.viscosity (Episode.cell (Episode.episode E)) ≡ viscosity

open CommonViscosityInteriorEpisodes public

finiteInteriorEpisodeForcingProductionEquality :
  (N : CommonViscosityInteriorEpisodes) →
  viscosity N * sumInteriorProduction (episodes N)
  ≡ sumInteriorWeightedForcing (episodes N)
finiteInteriorEpisodeForcingProductionEquality N = go (episodes N)
  where
  nu = viscosity N

  go : (Es : List Episode.InteriorAdverseSignedForcingEpisode) →
    nu * sumInteriorProduction Es ≡ sumInteriorWeightedForcing Es
  go [] = solve []
  go (E ∷ Es)
    rewrite sym (sameViscosity N E)
          | Episode.interiorEpisodePaidExactlyBySignedForcing E
          | go Es =
    solve
      ( Normal.normalFormWeight (Episode.cell (Episode.episode E))
      ∷ Normal.integratedForcing (Episode.cell (Episode.episode E))
      ∷ sumInteriorWeightedForcing Es ∷ [])

forcingBudgetImpliesProductionBudget :
  (N : CommonViscosityInteriorEpisodes) →
  (budget : ℚ) →
  sumInteriorWeightedForcing (episodes N) ≤ budget →
  viscosity N * sumInteriorProduction (episodes N) ≤ budget
forcingBudgetImpliesProductionBudget N budget forcingBound =
  subst
    (_≤ budget)
    (sym (finiteInteriorEpisodeForcingProductionEquality N))
    forcingBound

productionBudgetImpliesForcingBudget :
  (N : CommonViscosityInteriorEpisodes) →
  (budget : ℚ) →
  viscosity N * sumInteriorProduction (episodes N) ≤ budget →
  sumInteriorWeightedForcing (episodes N) ≤ budget
productionBudgetImpliesForcingBudget N budget productionBound =
  subst
    (_≤ budget)
    (finiteInteriorEpisodeForcingProductionEquality N)
    productionBound

signedInteriorForcingBudgetIsEquivalentToAdverseProductionBudget : Bool
signedInteriorForcingBudgetIsEquivalentToAdverseProductionBudget = true

signedInteriorForcingNameAloneIsIndependentMechanism : Bool
signedInteriorForcingNameAloneIsIndependentMechanism = false

signedInteriorForcingBudgetIsEquivalentToAdverseProductionBudgetIsTrue :
  signedInteriorForcingBudgetIsEquivalentToAdverseProductionBudget ≡ true
signedInteriorForcingBudgetIsEquivalentToAdverseProductionBudgetIsTrue = refl

signedInteriorForcingNameAloneIsIndependentMechanismIsFalse :
  signedInteriorForcingNameAloneIsIndependentMechanism ≡ false
signedInteriorForcingNameAloneIsIndependentMechanismIsFalse = refl
