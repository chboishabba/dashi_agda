module DASHI.Core.RecursiveScaleTransitionExact where

open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- Recursive scale transition.
--
-- This owner refines the informal equation
--
--   S_(n+1) = F_n(S_n)
--
-- into three typed stages:
--
--   dynamics -> persistent/invariant classification -> realisation
--
-- The final realisation is witness-mediated.  A persistent lower-scale
-- structure is therefore not definitionally the next-scale semantic object.
------------------------------------------------------------------------

record SituatedLowerState
  (State Environment History : Set) : Set where
  constructor situatedLowerState
  field
    state : State
    environment : Environment
    history : History

open SituatedLowerState public

data PersistentRole : Set where
  orbitClass : PersistentRole
  invariantSet : PersistentRole
  metastableClass : PersistentRole
  resonanceClass : PersistentRole
  symmetrySector : PersistentRole
  quotientClass : PersistentRole
  attractorClass : PersistentRole

------------------------------------------------------------------------
-- The generic D/A/Q carrier.
------------------------------------------------------------------------

record RecursiveScaleTransition
  (State Environment History Trajectory Persistent Next : Set) : Set₁ where
  field
    dynamics : SituatedLowerState State Environment History → Trajectory
    classifyPersistent : Trajectory → Persistent
    persistentRole : Persistent → PersistentRole

    -- Q_n / realisation boundary.  This relation is intentionally not a total
    -- function Persistent -> Next: a later witness must pay the semantic weld.
    RealisesNext : Persistent → Next → Set

open RecursiveScaleTransition public

------------------------------------------------------------------------
-- A concrete execution witness keeps the three stages visible and pays the
-- realisation relation for one lower-scale state.
------------------------------------------------------------------------

record ScaleTransitionWitness
  {State Environment History Trajectory Persistent Next : Set}
  (transition : RecursiveScaleTransition
    State Environment History Trajectory Persistent Next)
  (lower : SituatedLowerState State Environment History) : Set where
  constructor scaleTransitionWitness
  field
    trajectory : Trajectory
    trajectoryIsDynamics : trajectory ≡ dynamics transition lower
    persistent : Persistent
    persistentIsClassification :
      persistent ≡ classifyPersistent transition trajectory
    next : Next
    nextRealisesPersistent : RealisesNext transition persistent next

open ScaleTransitionWitness public

realiseNextObject :
  {State Environment History Trajectory Persistent Next : Set}
  {transition : RecursiveScaleTransition
    State Environment History Trajectory Persistent Next}
  {lower : SituatedLowerState State Environment History} →
  ScaleTransitionWitness transition lower →
  Next
realiseNextObject witness = ScaleTransitionWitness.next witness

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

record RecursiveScaleTransitionBoundary : Set₁ where
  field
    persistenceIsNotNextIdentityByDefinition : Set
    persistenceIsNotRequiredToBeFixedPoint : Set
    persistenceIsNotRequiredToBeAttractor : Set
    environmentRemainsExplicit : Set
    historyRemainsExplicit : Set
    noUniversalPhysicalF : Set

open RecursiveScaleTransitionBoundary public

-- Finite witnesses that the persistence vocabulary is broader than attractors.
persistenceNeedNotBeAttractor : PersistentRole
persistenceNeedNotBeAttractor = orbitClass

persistenceMayBeMetastable : PersistentRole
persistenceMayBeMetastable = metastableClass

persistenceMayBeResonant : PersistentRole
persistenceMayBeResonant = resonanceClass
