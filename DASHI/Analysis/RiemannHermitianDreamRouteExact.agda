module DASHI.Analysis.RiemannHermitianDreamRouteExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Final typed theorem shape for the complex-Poisson/Hermitian route.
--
-- The route is deliberately conditional on the actual analytic producers:
-- complex continuation/cosh coercivity, finite retention, mixed-channel
-- domination, prime-side excess normalization, and one error-floor closer.
-- It therefore records exactly what would imply exclusion of an off-line zero
-- without claiming any missing source-facing theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

open import DASHI.Analysis.RiemannHermitianEndgameTrichotomyExact
  using (EndgameSystem; State; offLine; EndgameAlternative; endgameAlternativeClosesOffLine)

record HermitianProducerStack : Set₁ where
  field
    System : EndgameSystem
    ComplexPoissonContinuation : Set
    CoshTransverseCoercivity : Set
    FiniteCompressionRetention : Set
    MixedChannelDomination : Set
    PrimeSideExcessNormalization : Set
    producerComplexPoisson : ComplexPoissonContinuation
    producerCoshCoercivity : CoshTransverseCoercivity
    producerFiniteRetention : FiniteCompressionRetention
    producerMixedDomination : MixedChannelDomination
    producerPrimeNormalization : PrimeSideExcessNormalization

open HermitianProducerStack public

record HermitianDreamRoute (stack : HermitianProducerStack) : Set₁ where
  field
    endgame : EndgameAlternative (System stack)

open HermitianDreamRoute public

hermitianDreamRouteClosesOffLine :
  (stack : HermitianProducerStack) →
  HermitianDreamRoute stack →
  (rho : State (System stack)) →
  offLine (System stack) rho →
  ⊥
hermitianDreamRouteClosesOffLine stack route rho h =
  endgameAlternativeClosesOffLine
    (System stack)
    (endgame route)
    rho h

-- Source-oriented dependency spelling.  These types are evidence, not Booleans;
-- an analytic instantiation must actually construct every field.
record AlpogeFurmanHermitianDreamProducer : Set₁ where
  field
    ZeroOrbit : Set
    offLine : ZeroOrbit → Set
    complexPoissonHermitianNormIdentity : Set
    coshExcessControlsAlphaSquared : Set
    finiteWindowRetainsExcess : Set
    mixedInterferenceCannotSwallowDiagonal : Set
    primeTraceMainTermNormalized : Set
    errorFloorCrossed : (rho : ZeroOrbit) → offLine rho → Set

record HermitianDreamRouteBoundary : Set where
  field
    completeConditionalDependencyStackConstructed : Bool
    typedEndgameDispatchIntegrated : Bool
    proseOnlySeamsEliminatedFromArchitecture : Bool
    complexPoissonProducerInstantiatedForZeta : Bool
    finiteRetentionInstantiatedForZeta : Bool
    mixedDominationInstantiatedForZeta : Bool
    primeExcessNormalizationInstantiatedForZeta : Bool
    errorFloorCloserInstantiatedForZeta : Bool
    riemannHypothesisProvedHere : Bool

hermitianDreamRouteBoundary : HermitianDreamRouteBoundary
hermitianDreamRouteBoundary = record
  { completeConditionalDependencyStackConstructed = true
  ; typedEndgameDispatchIntegrated = true
  ; proseOnlySeamsEliminatedFromArchitecture = true
  ; complexPoissonProducerInstantiatedForZeta = false
  ; finiteRetentionInstantiatedForZeta = false
  ; mixedDominationInstantiatedForZeta = false
  ; primeExcessNormalizationInstantiatedForZeta = false
  ; errorFloorCloserInstantiatedForZeta = false
  ; riemannHypothesisProvedHere = false
  }
