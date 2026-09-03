module DASHI.Culture.IntellectualReceptionParetoPreferenceAuthorityBoundaryCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Culture.IntellectualReceptionSemanticStabiliserParetoAuthorityCrossPollinationExact as Stabiliser
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Environment.LESResearchCrossPollinationExact as LES

------------------------------------------------------------------------
-- #599 CROSS-POLLINATION
--
-- The environmental Pareto owner already separates front/non-dominance from
-- preference and choice.  The stabiliser lane keeps that separation after the
-- semantic and authority gates: eligibility permits ranking; ranking still does
-- not manufacture a unique preference, authority source, or chosen action.
------------------------------------------------------------------------

paretoPreferenceBoundaryRetained :
  LES.paretoLiteratureDoesNotSupplyStakeholderPreferences
    LES.canonicalLESResearchCrossPollinationBoundary
  ≡ true
paretoPreferenceBoundaryRetained = refl

data ParetoFrontCreatesPreference : Set where
data ParetoFrontCreatesAuthority : Set where
data ParetoFrontChoosesReceptionAction : Set where

paretoFrontDoesNotCreatePreference :
  ParetoFrontCreatesPreference → ⊥
paretoFrontDoesNotCreatePreference ()

paretoFrontDoesNotCreateAuthority :
  ParetoFrontCreatesAuthority → ⊥
paretoFrontDoesNotCreateAuthority ()

paretoFrontDoesNotChooseReceptionAction :
  ParetoFrontChoosesReceptionAction → ⊥
paretoFrontDoesNotChooseReceptionAction ()

-- The hard gate from the stabiliser owner remains upstream of Pareto ranking.
-- This theorem forwards the exact generic receipt rather than creating a
-- second notion of Pareto admissibility.
paretoStillRequiresEligibleGenerator :
  ∀ {selected}
    {costs : MDL.CostHyperfabric Stabiliser.generatorEligibilityProblem} →
  MDL.ParetoAdmissible costs selected →
  MDL.Eligible Stabiliser.generatorEligibilityProblem selected
paretoStillRequiresEligibleGenerator =
  Stabiliser.paretoEligibilityGateRetained

record IntellectualReceptionParetoPreferenceAuthorityBoundary : Set where
  constructor intellectual-reception-pareto-preference-authority-boundary
  field
    semanticAndAuthorityEligibilityPrecedesPareto : Bool
    paretoFrontCreatesPreference : Bool
    paretoFrontCreatesAuthority : Bool
    paretoFrontAutomaticallyChoosesReceptionAction : Bool
    sourceAttributionBoundarySurvives : Bool

canonicalIntellectualReceptionParetoPreferenceAuthorityBoundary :
  IntellectualReceptionParetoPreferenceAuthorityBoundary
canonicalIntellectualReceptionParetoPreferenceAuthorityBoundary =
  intellectual-reception-pareto-preference-authority-boundary
    true false false false true
