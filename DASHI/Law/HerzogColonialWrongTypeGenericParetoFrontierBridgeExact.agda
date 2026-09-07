module DASHI.Law.HerzogColonialWrongTypeGenericParetoFrontierBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Law.HerzogColonialWrongTypeElementRequirementExact as Element

------------------------------------------------------------------------
-- HERZOG ADAPTER TO THE GENERIC FINITE REQUIREMENT PARETO FRONTIER
--
-- DASHI synthesis only. Historical/legal source attribution remains owned by
-- the imported Herzog/colonial source modules through Element.
------------------------------------------------------------------------

Cell : Set
Cell = Pareto.RequirementCandidate Element.MechanismRequirementKind

currentAuthorityCell : Cell
currentAuthorityCell = Pareto.requirement-candidate
  Element.requiresAuthorityMeaningErasure
  true true true true
  2 3
  "current authority-meaning recovery: required/relevant/admissible and live-fibre splitting"

currentPowerCell : Cell
currentPowerCell = Pareto.requirement-candidate
  Element.requiresOperationalPrerequisite
  true true true false
  3 2
  "power prerequisite remains required but does not yet split the current live fibre"

currentIncidentCell : Cell
currentIncidentCell = Pareto.requirement-candidate
  Element.requiresSameObjectProjectionPowerIncident
  true true true false
  4 3
  "incident weld remains required but does not yet split the current live fibre"

currentPortfolio : List Cell
currentPortfolio = currentAuthorityCell ∷ currentPowerCell ∷ currentIncidentCell ∷ []

currentAuthorityOnParetoFrontier :
  Pareto.onParetoFrontier? currentPortfolio currentAuthorityCell ≡ true
currentAuthorityOnParetoFrontier = refl

currentPowerOffFrontierButRequired :
  Pareto.onParetoFrontier? currentPortfolio currentPowerCell ≡ false
currentPowerOffFrontierButRequired = refl

currentPowerStillRequired :
  Pareto.requiredForConsumer currentPowerCell ≡ true
currentPowerStillRequired = refl

currentParetoFrontierIsAuthorityOnly :
  Pareto.paretoFrontier currentPortfolio ≡ currentAuthorityCell ∷ []
currentParetoFrontierIsAuthorityOnly = refl

------------------------------------------------------------------------
-- After authority meaning closes, the already-required power coordinate gains
-- current splitting value. Requiredness does not change.
------------------------------------------------------------------------

afterAuthorityAuthorityCell : Cell
afterAuthorityAuthorityCell = Pareto.requirement-candidate
  Element.requiresAuthorityMeaningErasure
  true true true false
  2 0
  "authority meaning retained as required history but no longer a live splitter"

afterAuthorityPowerCell : Cell
afterAuthorityPowerCell = Pareto.requirement-candidate
  Element.requiresOperationalPrerequisite
  true true true true
  3 2
  "power prerequisite now splits the refined live fibre"

afterAuthorityIncidentCell : Cell
afterAuthorityIncidentCell = Pareto.requirement-candidate
  Element.requiresSameObjectProjectionPowerIncident
  true true true false
  4 3
  "incident weld remains required but currently inert"

afterAuthorityPortfolio : List Cell
afterAuthorityPortfolio =
  afterAuthorityAuthorityCell ∷ afterAuthorityPowerCell ∷ afterAuthorityIncidentCell ∷ []

afterAuthorityPowerOnParetoFrontier :
  Pareto.onParetoFrontier? afterAuthorityPortfolio afterAuthorityPowerCell ≡ true
afterAuthorityPowerOnParetoFrontier = refl

afterAuthorityParetoFrontierIsPowerOnly :
  Pareto.paretoFrontier afterAuthorityPortfolio ≡ afterAuthorityPowerCell ∷ []
afterAuthorityParetoFrontierIsPowerOnly = refl

------------------------------------------------------------------------
-- After power prerequisite closes, incident weld becomes the current splitter.
------------------------------------------------------------------------

afterPowerAuthorityCell : Cell
afterPowerAuthorityCell = Pareto.requirement-candidate
  Element.requiresAuthorityMeaningErasure true true true false 2 0
  "closed authority coordinate retained"

afterPowerPowerCell : Cell
afterPowerPowerCell = Pareto.requirement-candidate
  Element.requiresOperationalPrerequisite true true true false 3 0
  "closed power coordinate retained"

afterPowerIncidentCell : Cell
afterPowerIncidentCell = Pareto.requirement-candidate
  Element.requiresSameObjectProjectionPowerIncident true true true true 4 3
  "incident weld is now the live splitter"

afterPowerPortfolio : List Cell
afterPowerPortfolio = afterPowerAuthorityCell ∷ afterPowerPowerCell ∷ afterPowerIncidentCell ∷ []

afterPowerParetoFrontierIsIncidentOnly :
  Pareto.paretoFrontier afterPowerPortfolio ≡ afterPowerIncidentCell ∷ []
afterPowerParetoFrontierIsIncidentOnly = refl

------------------------------------------------------------------------
-- Non-collapse.
------------------------------------------------------------------------

data GenericParetoOrderIsLegalEntailmentOrder : Set where
data OffParetoFrontierMeansRequirementNotNeeded : Set where

genericParetoDoesNotCreateEntailment : GenericParetoOrderIsLegalEntailmentOrder → ⊥
genericParetoDoesNotCreateEntailment ()

offFrontierDoesNotEraseNeed : OffParetoFrontierMeansRequirementNotNeeded → ⊥
offFrontierDoesNotEraseNeed ()
