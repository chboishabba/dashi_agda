module DASHI.Physics.QuantumVacuum.CasimirCycleAccounting where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.QuantumVacuum.ExtractionPhysicsSurface as Surface

------------------------------------------------------------------------
-- A finite accounting model for a tunable Casimir cycle.
--
-- `inwardWork` is the work available from the strong-force stroke.
-- Every mechanism needed to return to the initial state is charged to the
-- same cycle.  A positive result is represented constructively by a margin.
------------------------------------------------------------------------

record CasimirCycle : Set where
  constructor mkCasimirCycle
  field
    inwardWork    : Nat
    switchingCost : Nat
    resetWork     : Nat
    dissipation   : Nat

cycleCost : CasimirCycle → Nat
cycleCost c =
  CasimirCycle.switchingCost c +
  (CasimirCycle.resetWork c + CasimirCycle.dissipation c)

record PositiveCycle (c : CasimirCycle) : Set where
  constructor mkPositiveCycle
  field
    margin : Nat
    closesWithMargin :
      CasimirCycle.inwardWork c ≡ suc (cycleCost c + margin)

-- A continuous machine claim requires both a positive, fully charged cycle
-- and an independently replicated physical implementation.

record ContinuousCasimirClosure (c : CasimirCycle) : Set where
  constructor mkContinuousCasimirClosure
  field
    positiveCycle : PositiveCycle c
    switchingMechanismObserved : Bool
    resetMechanismObserved     : Bool
    replicationObserved        : Bool
    switchingClosed : switchingMechanismObserved ≡ true
    resetClosed     : resetMechanismObserved ≡ true
    replicationClosed : replicationObserved ≡ true

continuousClosureToExtractionClaim :
  (c : CasimirCycle) → ContinuousCasimirClosure c → Surface.ExtractionClaim
continuousClosureToExtractionClaim c closure =
  Surface.mkExtractionClaim
    Surface.tunableCasimirCycle
    Surface.continuous
    Surface.closedEngineeringCycle
    true
    true
    true
    true
    true

continuousClosurePromotes :
  (c : CasimirCycle) → (closure : ContinuousCasimirClosure c) →
  Surface.promotable? (continuousClosureToExtractionClaim c closure) ≡ true
continuousClosurePromotes c closure = refl

------------------------------------------------------------------------
-- One-shot relaxation is weaker than a cycle.
------------------------------------------------------------------------

record TransientCasimirWork : Set where
  constructor mkTransientCasimirWork
  field
    releasedWork : Nat
    stressObserved : Bool
    stressClosed : stressObserved ≡ true

transientWorkDoesNotSupplyResetAccounting :
  (t : TransientCasimirWork) →
  Surface.promotable?
    (Surface.mkExtractionClaim
      Surface.casimirRelaxation
      Surface.transient
      Surface.preliminaryExperiment
      true true false false false)
  ≡ false
transientWorkDoesNotSupplyResetAccounting t = refl

-- The exact missing data can be exposed as a product rather than hidden in a
-- generic "not verified" marker.

CasimirCycleOpenObligations : CasimirCycle → Set
CasimirCycleOpenObligations c =
  PositiveCycle c ×
  (Surface.PromotionWitness
    (Surface.mkExtractionClaim
      Surface.tunableCasimirCycle
      Surface.continuous
      Surface.closedEngineeringCycle
      true true true true true))
