module DASHI.Core.TypedDependencyCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Typed dependency core.
--
-- An inhabited carrier only records that a term exists.  A dependency
-- witness records the source, target, relation, provenance and scope under
-- which the term may be used.  Boolean projections are deliberately lossy.
------------------------------------------------------------------------

data DependencyLayer : Set where
  logicalLayer relationalLayer operationalLayer epistemicLayer : DependencyLayer
  temporalLayer provenanceLayer authorityLayer topologicalLayer : DependencyLayer

data DependencyDisposition : Set where
  requiredDependency optionalDependency forbiddenDependency : DependencyDisposition

record DependencyWitness
    {Source Target : Set}
    (Depends : Source → Target → Set) : Set where
  constructor dependencyWitness
  field
    source : Source
    target : Target
    dependency : Depends source target
    layer : DependencyLayer
    disposition : DependencyDisposition
    provenance : String
    scope : String

open DependencyWitness public

forgetDependencyToBool :
  ∀ {Source Target : Set}
    {Depends : Source → Target → Set} →
  DependencyWitness Depends →
  Bool
forgetDependencyToBool witness = true

record DependencyFamily (Index : Set) : Set₁ where
  field
    Requirement : Index → Set
    requirementLabel : Index → String
    requirementProvenance : Index → String

open DependencyFamily public

record FamilyWitness
    {Index : Set}
    (family : DependencyFamily Index)
    (index : Index) : Set where
  field
    witness : Requirement family index
    witnessReceipt : String

open FamilyWitness public

------------------------------------------------------------------------
-- Actions are not made admissible merely because an action constructor is
-- inhabited.  Preconditions and postconditions are indexed by state/action.
------------------------------------------------------------------------

record DependentActionSystem (State Action : Set) : Set₁ where
  field
    Precondition : State → Action → Set
    Postcondition : State → Action → State → Set
    actionLabel : Action → String

open DependentActionSystem public

record AdmissibleAction
    {State Action : Set}
    (system : DependentActionSystem State Action)
    (before : State)
    (action : Action) : Set where
  field
    precondition : Precondition system before action
    after : State
    postcondition : Postcondition system before action after
    dependencyReceipt : String

open AdmissibleAction public

------------------------------------------------------------------------
-- Irreducible ternary dependency.
--
-- The joint support is inhabited while each declared pair-support type is
-- refuted.  This is a relational/hypergraphic result, not topology.
------------------------------------------------------------------------

record IrreducibleTernaryDependency
    (A B C Joint AB AC BC : Set) : Set where
  field
    leftWitness : A
    middleWitness : B
    rightWitness : C
    jointSupport : Joint
    noLeftMiddleSupport : ¬ AB
    noLeftRightSupport : ¬ AC
    noMiddleRightSupport : ¬ BC
    dependencyReceipt : String

open IrreducibleTernaryDependency public

record DependencyUpgradeBoundary : Set where
  field
    witnessCarriesMoreThanBoolean : Bool
    booleanProjectionAvailable : Bool
    booleanProjectionReconstructsWitness : Bool
    inhabitanceAloneProvesRelation : Bool
    inhabitanceAloneProvesAuthority : Bool
    boundaryNote : String

canonicalDependencyUpgradeBoundary : DependencyUpgradeBoundary
canonicalDependencyUpgradeBoundary = record
  { witnessCarriesMoreThanBoolean = true
  ; booleanProjectionAvailable = true
  ; booleanProjectionReconstructsWitness = false
  ; inhabitanceAloneProvesRelation = false
  ; inhabitanceAloneProvesAuthority = false
  ; boundaryNote =
      "Typed dependencies retain indexed preconditions, relations, provenance and scope; forgetting to Bool is one-way and non-authoritative."
  }
