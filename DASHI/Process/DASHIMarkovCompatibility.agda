module DASHI.Process.DASHIMarkovCompatibility where

open import DASHI.Core.Prelude

-- Native DASHI lane state. This is intentionally structural: probability,
-- stationarity, and stochastic kernels are optional downstream projections.
record DASHIState : Set₁ where
  field
    Carrier           : Set
    carrierValue      : Carrier
    ResidualSurface   : Set
    residualValue     : ResidualSurface
    ObligationSurface : Set
    obligations       : ObligationSurface
    AuthoritySurface  : Set
    authorities       : AuthoritySurface
    BoundarySurface   : Set
    boundary          : BoundarySurface
    PromotionSurface  : Set
    promotionStatus   : PromotionSurface

record DASHITransition (Input : Set) : Set₁ where
  field
    step : DASHIState → Input → DASHIState

-- Markov within DASHI: history is admissibly replaced by the current typed
-- state for the next transition surface.
record Sufficiency (History : Set) : Set₁ where
  field
    extract         : History → DASHIState
    NextFromHistory : History → Set
    NextFromState   : DASHIState → Set
    sufficient      :
      (h : History) → NextFromHistory h ≡ NextFromState (extract h)

record DASHIMarkovLike (History Input : Set) : Set₁ where
  field
    transition  : DASHITransition Input
    sufficiency : Sufficiency History

-- Multiscale state: a lane may build its present state by joining horizon
-- slices before asking for sufficiency.
record JoinedMultiscaleState (Horizon : Set) : Set₁ where
  field
    slice : Horizon → DASHIState
    join  : (Horizon → DASHIState) → DASHIState
    joinedState : DASHIState
    joinedState≡ : joinedState ≡ join slice

-- Compatibility projection into ordinary Markov-language consumers.
record MarkovCompatibility (Input : Set) : Set₁ where
  field
    State          : Set
    transition     : DASHITransition Input
    projectedStep  : State → Input → State
    embed          : DASHIState → State
    observable     : State → Set
    kernelOptional : State → Input → State → Set
    preservesStep  :
      (σ : DASHIState) (x : Input) →
      embed (DASHITransition.step transition σ x) ≡
      projectedStep (embed σ) x

data DASHIMarkovCompatibilityStatus : Set where
  nativeTransitionSurfaceOnlyNoPromotion : DASHIMarkovCompatibilityStatus
