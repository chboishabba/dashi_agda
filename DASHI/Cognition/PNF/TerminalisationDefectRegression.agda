module DASHI.Cognition.PNF.TerminalisationDefectRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ProvenanceBearingQuotient as Quotient
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

------------------------------------------------------------------------
-- 1. Hidden depth phase.
--
-- Two states have the same current coarse observation.  The same tick action
-- is admissible from both, but phase-dependent refinement makes the next coarse
-- observations differ.  Forgetting phase is therefore not dynamically safe for
-- this consumer.
------------------------------------------------------------------------

record PhaseState : Set where
  constructor phaseState
  field
    visible : Bool
    phase : Wheel.DepthWheelPhase

open PhaseState public

data PhaseAction : Set where tickPhase : PhaseAction

phaseStep : PhaseState → PhaseState
phaseStep (phaseState value Wheel.phase-0) = phaseState true Wheel.phase-1
phaseStep (phaseState value Wheel.phase-1) = phaseState false Wheel.phase-2
phaseStep (phaseState value Wheel.phase-2) =
  phaseState value Wheel.phase-0

phaseSystem : Dependency.DependentActionSystem PhaseState PhaseAction
phaseSystem = record
  { Precondition = λ state action → ⊤
  ; Postcondition = λ before action after → after ≡ phaseStep before
  ; actionLabel = λ action → "depth-wheel tick"
  }

phaseAdmissible :
  (state : PhaseState) →
  Dependency.AdmissibleAction phaseSystem state tickPhase
phaseAdmissible state = record
  { precondition = tt
  ; after = phaseStep state
  ; postcondition = refl
  ; dependencyReceipt = "phase-dependent refinement step"
  }

phaseExecution :
  (state : PhaseState) →
  Reachability.Executes
    phaseSystem (tickPhase ∷ []) state (phaseStep state)
phaseExecution state =
  Reachability.executesCons (phaseAdmissible state) Reachability.executesNil

phaseProjection : PhaseState → Bool
phaseProjection = visible

depthPhaseTerminalisationDefect :
  Dynamic.TerminalisationDefect phaseSystem phaseProjection
depthPhaseTerminalisationDefect =
  Dynamic.terminalisationDefect
    (tickPhase ∷ [])
    (phaseState false Wheel.phase-0)
    (phaseState false Wheel.phase-1)
    (phaseState true Wheel.phase-1)
    (phaseState false Wheel.phase-2)
    refl
    (phaseExecution (phaseState false Wheel.phase-0))
    (phaseExecution (phaseState false Wheel.phase-1))
    trueNotFalse

------------------------------------------------------------------------
-- 2. Extinction/action projection.
--
-- MemoryFibre already proves extinction retains the remembered EventPNF while
-- setting actionWeight to zero.  Here an action-sensitive downstream consumer
-- initially sees the same neutral outcome for a reinforced and extinguished
-- memory, then the same probe action exposes the hidden action-weight
-- distinction.  The remembered PNF itself is not erased.
------------------------------------------------------------------------

record ActionShadowState : Set where
  constructor actionShadowState
  field
    memory : Memory.MemoryFibre
    actionOutcome : Bool

open ActionShadowState public

data ActionProbe : Set where probeAction : ActionProbe

positiveNat : Nat → Bool
positiveNat zero = false
positiveNat (suc n) = true

probeStep : ActionShadowState → ActionShadowState
probeStep state =
  actionShadowState
    (memory state)
    (positiveNat (Memory.actionWeight (memory state)))

actionProbeSystem :
  Dependency.DependentActionSystem ActionShadowState ActionProbe
actionProbeSystem = record
  { Precondition = λ state action → ⊤
  ; Postcondition = λ before action after → after ≡ probeStep before
  ; actionLabel = λ action → "action projection probe"
  }

probeAdmissible :
  (state : ActionShadowState) →
  Dependency.AdmissibleAction actionProbeSystem state probeAction
probeAdmissible state = record
  { precondition = tt
  ; after = probeStep state
  ; postcondition = refl
  ; dependencyReceipt = "probe current action projection"
  }

probeExecution :
  (state : ActionShadowState) →
  Reachability.Executes
    actionProbeSystem (probeAction ∷ []) state (probeStep state)
probeExecution state =
  Reachability.executesCons (probeAdmissible state) Reachability.executesNil

actionProjection : ActionShadowState → Bool
actionProjection = actionOutcome

extinctionRetainsRememberedPNF :
  (raw : Memory.MemoryFibre) →
  Memory.rememberedEvent (Memory.extinguishActionDominance raw)
  ≡ Memory.rememberedEvent raw
extinctionRetainsRememberedPNF = Memory.extinctionPreservesRememberedEvent

extinctionActionTerminalisationDefect :
  (raw : Memory.MemoryFibre) →
  (n : Nat) →
  Memory.actionWeight raw ≡ suc n →
  Dynamic.TerminalisationDefect actionProbeSystem actionProjection
extinctionActionTerminalisationDefect raw n positive
  rewrite positive =
  Dynamic.terminalisationDefect
    (probeAction ∷ [])
    (actionShadowState raw false)
    (actionShadowState (Memory.extinguishActionDominance raw) false)
    (actionShadowState raw true)
    (actionShadowState (Memory.extinguishActionDominance raw) false)
    refl
    (probeExecution (actionShadowState raw false))
    (probeExecution
      (actionShadowState (Memory.extinguishActionDominance raw) false))
    trueNotFalse

------------------------------------------------------------------------
-- 3. Residual-bearing PNF-style quotient.
--
-- The fine carrier has a visible bit and a retained residual bit.  Projection
-- forgets the residual, while the canonical quotient receipt reconstructs it
-- exactly.  A later admissible action can expose that residual, giving a direct
-- witness that projection without the receipt is dynamically unsafe.
------------------------------------------------------------------------

ResidualState : Set
ResidualState = Bool × Bool

residualCore : Fibre.FibreRestrictionCore
residualCore = Fibre.fibreRestrictionCore
  ResidualState
  Bool
  ⊤
  proj₁
  (λ surface → Bool)
  (λ evidence surface → ⊤)
  true
  false

residualQuotient : Quotient.ProvenanceBearingQuotient residualCore
residualQuotient = Quotient.provenanceBearingQuotient
  Bool
  proj₂
  (λ surface residual → surface , residual)
  (λ state → refl)

data ResidualAction : Set where exposeResidual : ResidualAction

residualStep : ResidualState → ResidualState
residualStep (visible , residual) = residual , residual

residualSystem :
  Dependency.DependentActionSystem ResidualState ResidualAction
residualSystem = record
  { Precondition = λ state action → ⊤
  ; Postcondition = λ before action after → after ≡ residualStep before
  ; actionLabel = λ action → "expose retained residual"
  }

residualAdmissible :
  (state : ResidualState) →
  Dependency.AdmissibleAction residualSystem state exposeResidual
residualAdmissible state = record
  { precondition = tt
  ; after = residualStep state
  ; postcondition = refl
  ; dependencyReceipt = "residual reopening/exposure"
  }

residualExecution :
  (state : ResidualState) →
  Reachability.Executes
    residualSystem (exposeResidual ∷ []) state (residualStep state)
residualExecution state =
  Reachability.executesCons
    (residualAdmissible state)
    Reachability.executesNil

residualProjection : ResidualState → Bool
residualProjection = proj₁

residualProjectionTerminalisationDefect :
  Dynamic.TerminalisationDefect residualSystem residualProjection
residualProjectionTerminalisationDefect =
  Dynamic.terminalisationDefect
    (exposeResidual ∷ [])
    (false , true)
    (false , false)
    (true , true)
    (false , false)
    refl
    (residualExecution (false , true))
    (residualExecution (false , false))
    trueNotFalse
