module DASHI.Governance.GovernanceRoleParetoSymmetryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.ParetoSymmetryQuotientAdmissionExact as ParetoSym
import DASHI.Governance.CorrectiveReachabilityEquivariance as Corrective

------------------------------------------------------------------------
-- GOVERNANCE ROLE / PARETO SYMMETRY BRIDGE
--
-- A role swap is admitted as a search-space quotient only when it is already a
-- Pareto-order automorphism: eligibility and every declared cost axis survive.
-- Governance additionally requires corresponding corrective access.  This is
-- same-rule symmetry, not equal material state or equal policy outcome.
------------------------------------------------------------------------

record GovernanceRoleParetoSymmetry
    {problem : MDL.ConsumerMDLProblem}
    (costs : MDL.CostHyperfabric problem) : Set₁ where
  field
    paretoSymmetry : ParetoSym.ParetoOrderAutomorphism costs
    correctivePair : Corrective.CanonicalCorrectivePair
    correctiveEquivariance :
      Corrective.CanonicalRoleEquivariantCorrectiveAccess correctivePair

    realiseModel :
      MDL.Model problem → Corrective.State correctivePair
    representative roleImage : MDL.Model problem
    roleImageIsMapped :
      ParetoSym.mapModel paretoSymmetry representative ≡ roleImage
    representativeStartsInside :
      realiseModel representative ≡ Corrective.insideSuppressed correctivePair
    roleImageStartsOutside :
      realiseModel roleImage ≡ Corrective.outsideSuppressed correctivePair

open GovernanceRoleParetoSymmetry public

roleSymmetryMapsWeakDominance :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    (symmetry : GovernanceRoleParetoSymmetry costs)
    {left right : MDL.Model problem} →
  MDL.WeaklyDominates costs left right →
  MDL.WeaklyDominates costs
    (ParetoSym.mapModel (paretoSymmetry symmetry) left)
    (ParetoSym.mapModel (paretoSymmetry symmetry) right)
roleSymmetryMapsWeakDominance symmetry =
  ParetoSym.mapsWeakDominance (paretoSymmetry symmetry)

correctiveAsymmetryRefutesGovernanceRoleSymmetry :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    (symmetry : GovernanceRoleParetoSymmetry costs) →
  Corrective.CanonicalAsymmetricCorrectiveAccess
    (correctivePair symmetry) →
  ⊥
correctiveAsymmetryRefutesGovernanceRoleSymmetry symmetry witness =
  Corrective.canonicalRoleEquivarianceRefutesAsymmetry
    (correctiveEquivariance symmetry)
    witness

------------------------------------------------------------------------
-- A carrier permutation / role-label swap is insufficient by itself.  Search
-- quotienting requires the stronger semantic/Pareto automorphism above.
------------------------------------------------------------------------

data BareRoleSwapAutomaticallyParetoAdmissible : Set where

bareRoleSwapDoesNotAuthoriseParetoQuotient :
  BareRoleSwapAutomaticallyParetoAdmissible → ⊥
bareRoleSwapDoesNotAuthoriseParetoQuotient ()

record GovernanceRoleParetoSymmetryBoundary : Set where
  constructor governance-role-pareto-symmetry-boundary
  field
    eligibilityMustBePreserved : Bool
    everyDeclaredCostMustBePreserved : Bool
    correctiveAccessMustBeRoleEquivariant : Bool
    sameRuleForcesSameMaterialOutcome : Bool
    bareIdentityLabelSwapIsEnough : Bool
    symmetryCreatesUniqueParetoOptimum : Bool

canonicalGovernanceRoleParetoSymmetryBoundary :
  GovernanceRoleParetoSymmetryBoundary
canonicalGovernanceRoleParetoSymmetryBoundary =
  governance-role-pareto-symmetry-boundary
    true true true false false false
