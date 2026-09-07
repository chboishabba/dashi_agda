module DASHI.Cognition.PNF.SensibLawNegligenceDutyGenericParetoFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto

------------------------------------------------------------------------
-- NEGLIGENCE DUTY ADAPTER TO THE GENERIC FINITE REQUIREMENT PARETO FRONTIER
--
-- DASHI synthetic scheduler calibration. Legal-source attribution remains in
-- SensibLawNegligenceDutyWrongTypeSpecializationExact and the climate-duty
-- source owners (Donoghue, Woolcock, Mallonland, Pabai, etc.).
------------------------------------------------------------------------

Cell : Set
Cell = Pareto.RequirementCandidate Climate.DutyIssue

currentForeseeabilityCell : Cell
currentForeseeabilityCell = Pareto.requirement-candidate
  Climate.reasonableForeseeability
  true true true false
  1 0
  "foreseeability remains required, but both current live duty configurations agree it is supported"

currentCorePolicyCell : Cell
currentCorePolicyCell = Pareto.requirement-candidate
  Climate.coreGovernmentPolicy
  true true true true
  2 3
  "core-government-policy classification is the current live duty splitter"

currentStatutoryCoherenceCell : Cell
currentStatutoryCoherenceCell = Pareto.requirement-candidate
  Climate.statutoryCoherence
  true true true false
  3 2
  "statutory coherence remains required but unresolved in both current live duty configurations"

currentDutyPortfolio : List Cell
currentDutyPortfolio =
  currentForeseeabilityCell ∷ currentCorePolicyCell ∷ currentStatutoryCoherenceCell ∷ []

foreseeabilityRequiredButOffCurrentParetoFrontier :
  Pareto.requiredForConsumer currentForeseeabilityCell ≡ true
foreseeabilityRequiredButOffCurrentParetoFrontier = refl

foreseeabilityCurrentFrontierStatus :
  Pareto.onParetoFrontier? currentDutyPortfolio currentForeseeabilityCell ≡ false
foreseeabilityCurrentFrontierStatus = refl

corePolicyIsCurrentParetoQuestion :
  Pareto.onParetoFrontier? currentDutyPortfolio currentCorePolicyCell ≡ true
corePolicyIsCurrentParetoQuestion = refl

currentDutyParetoFrontierIsCorePolicyOnly :
  Pareto.paretoFrontier currentDutyPortfolio ≡ currentCorePolicyCell ∷ []
currentDutyParetoFrontierIsCorePolicyOnly = refl

------------------------------------------------------------------------
-- Post-policy fibre: statutory coherence becomes salient without becoming newly
-- required. Foreseeability and policy remain retained but non-splitting.
------------------------------------------------------------------------

postPolicyForeseeabilityCell : Cell
postPolicyForeseeabilityCell = Pareto.requirement-candidate
  Climate.reasonableForeseeability true true true false 1 0
  "foreseeability retained after policy classification closes"

postPolicyCorePolicyCell : Cell
postPolicyCorePolicyCell = Pareto.requirement-candidate
  Climate.coreGovernmentPolicy true true true false 2 0
  "policy coordinate retained after its collision closes"

postPolicyStatutoryCoherenceCell : Cell
postPolicyStatutoryCoherenceCell = Pareto.requirement-candidate
  Climate.statutoryCoherence true true true true 3 2
  "statutory coherence now splits the refined live duty fibre"

postPolicyPortfolio : List Cell
postPolicyPortfolio =
  postPolicyForeseeabilityCell ∷ postPolicyCorePolicyCell ∷ postPolicyStatutoryCoherenceCell ∷ []

statutoryCoherenceBecomesParetoQuestion :
  Pareto.onParetoFrontier? postPolicyPortfolio postPolicyStatutoryCoherenceCell ≡ true
statutoryCoherenceBecomesParetoQuestion = refl

postPolicyParetoFrontierIsStatutoryCoherenceOnly :
  Pareto.paretoFrontier postPolicyPortfolio ≡ postPolicyStatutoryCoherenceCell ∷ []
postPolicyParetoFrontierIsStatutoryCoherenceOnly = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ParetoQuestionIsDutyHolding : Set where
data OffFrontierDutyCoordinateIsLegallyIrrelevant : Set where

paretoSelectionDoesNotCreateDutyHolding : ParetoQuestionIsDutyHolding → ⊥
paretoSelectionDoesNotCreateDutyHolding ()

offFrontierDoesNotEraseLegalRelevance : OffFrontierDutyCoordinateIsLegallyIrrelevant → ⊥
offFrontierDoesNotEraseLegalRelevance ()
