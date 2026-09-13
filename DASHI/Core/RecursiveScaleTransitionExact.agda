module DASHI.Core.RecursiveScaleTransitionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)

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
  orbitClass
  invariantSet
  metastableClass
  resonanceClass
  symmetrySector
  quotientClass
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

    -- Q_n / realisation boundary.  The next-scale object is not obtained by
    -- identifying it with Persistent; a witness must relate the two.
    RealisesNext : Persistent → Next → Set
    realiseNextObject : (p : Persistent) → Σ Next (RealisesNext p)

open RecursiveScaleTransition public

------------------------------------------------------------------------
-- A concrete execution witness keeps the three stages visible.
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
