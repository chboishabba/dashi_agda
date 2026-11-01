module DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierContractExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto

------------------------------------------------------------------------
-- PUBLIC CONTRACT FOR CROSS-DOMAIN SCHEDULERS
--
-- DASHI synthesis. A consumer supplies requirement identity plus independent
-- requiredness, relevance, authority-admissibility, current live-fibre split,
-- cost and certified-gain coordinates. The compiler returns a Pareto frontier.
------------------------------------------------------------------------

record FiniteRequirementParetoContract : Set where
  constructor finite-requirement-pareto-contract
  field
    requirednessSeparateFromSalience : Bool
    requirednessSeparateFromSalienceIsTrue : requirednessSeparateFromSalience ≡ true
    authoritySeparateFromGain : Bool
    authoritySeparateFromGainIsTrue : authoritySeparateFromGain ≡ true
    currentSplitSeparateFromGlobalNeed : Bool
    currentSplitSeparateFromGlobalNeedIsTrue : currentSplitSeparateFromGlobalNeed ≡ true
    frontierMayContainMultipleCells : Bool
    frontierMayContainMultipleCellsIsTrue : frontierMayContainMultipleCells ≡ true
    frontierMembershipDoesNotSatisfyRequirement : Bool
    frontierMembershipDoesNotSatisfyRequirementIsFalse : frontierMembershipDoesNotSatisfyRequirement ≡ false

open FiniteRequirementParetoContract public

canonicalFiniteRequirementParetoContract : FiniteRequirementParetoContract
canonicalFiniteRequirementParetoContract =
  finite-requirement-pareto-contract true refl true refl true refl true refl false refl

multipleFrontierCellsWitnessContract :
  frontierMayContainMultipleCells canonicalFiniteRequirementParetoContract ≡ true
multipleFrontierCellsWitnessContract = refl
