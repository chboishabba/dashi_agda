module DASHI.Architecture.PlanningArchitectureRealisationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- PLANNING <-> ARCHITECTURE REALISATION
--
-- Planning constrains admissible transformations; architecture supplies a
-- spatial realisation.  Planning admissibility, physical feasibility, code
-- compliance, environmental admissibility and viability are independent proof
-- obligations rather than one Boolean `valid`.
------------------------------------------------------------------------

record PlanningArchitectureInterface : Set₁ where
  field
    Plan   : Set
    Design : Set

    PlanAdmits            : Plan → Design → Set
    PhysicallyFeasible    : Design → Set
    CodeCompliant         : Design → Set
    EnvironmentAdmissible : Design → Set
    EconomicallyViable    : Design → Set
    SociallyDesired       : Design → Set

record FullyAdmissibleRealisation
    (interface : PlanningArchitectureInterface)
    (plan : PlanningArchitectureInterface.Plan interface)
    (design : PlanningArchitectureInterface.Design interface) : Set where
  field
    planningAdmissible :
      PlanningArchitectureInterface.PlanAdmits interface plan design
    physicallyFeasible :
      PlanningArchitectureInterface.PhysicallyFeasible interface design
    codeCompliant :
      PlanningArchitectureInterface.CodeCompliant interface design
    environmentallyAdmissible :
      PlanningArchitectureInterface.EnvironmentAdmissible interface design
    economicallyViable :
      PlanningArchitectureInterface.EconomicallyViable interface design

data Plan : Set where
  nominalPlan : Plan

data Design : Set where
  paperDesign buildableDesign : Design

Admits : Plan → Design → Set
Admits nominalPlan paperDesign = ⊤
Admits nominalPlan buildableDesign = ⊤

Physical : Design → Set
Physical paperDesign = ⊥
Physical buildableDesign = ⊤

Code : Design → Set
Code _ = ⊤

Environmental : Design → Set
Environmental _ = ⊤

Viable : Design → Set
Viable _ = ⊤

Desired : Design → Set
Desired _ = ⊤

interface : PlanningArchitectureInterface
interface =
  record
    { Plan = Plan
    ; Design = Design
    ; PlanAdmits = Admits
    ; PhysicallyFeasible = Physical
    ; CodeCompliant = Code
    ; EnvironmentAdmissible = Environmental
    ; EconomicallyViable = Viable
    ; SociallyDesired = Desired
    }

planningAdmissibilityDoesNotImplyPhysicalRealisability :
  PlanningArchitectureInterface.PlanAdmits interface nominalPlan paperDesign ×
  (PlanningArchitectureInterface.PhysicallyFeasible
      interface paperDesign → ⊥)
planningAdmissibilityDoesNotImplyPhysicalRealisability =
  tt , (λ feasible → feasible)

architectureCanExposePlanLevelInfeasibility :
  (PlanningArchitectureInterface.PhysicallyFeasible
      interface paperDesign → ⊥)
architectureCanExposePlanLevelInfeasibility feasible = feasible
