module DASHI.Analysis.RiemannHermitianDreamRouteExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Final typed theorem shape for the complex-Poisson/Hermitian route.
--
-- The route is deliberately conditional on the actual analytic producers:
-- complex continuation/cosh coercivity, finite retention, mixed-channel
-- domination, prime-side excess normalization, and one error-floor closer.
-- It records exactly what would imply exclusion of an off-line zero without
-- claiming any missing source-facing theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

open import DASHI.Analysis.RiemannHermitianEndgameTrichotomyExact
  using (EndgameSystem; State; offLine; EndgameAlternative; endgameAlternativeClosesOffLine)
open import DASHI.Analysis.RiemannHermitianExcessDetectabilityAssemblyExact
  using
    ( HermitianExcessDetectabilityAssembly
    ; hermitianExcessDetectabilityContradiction
    )

------------------------------------------------------------------------
-- Generic endgame dispatch.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Source-shaped proof-relevant route.
--
-- This is stronger than merely packaging producer receipts beside an abstract
-- closer.  An off-line zero must actually be mapped to the normalized retained
-- excess/error/pair-gap assembly consumed by the contradiction theorem.
------------------------------------------------------------------------

record AlpogeFurmanHermitianDreamProducer : Set₁ where
  field
    ZeroOrbit : Set
    offLine : ZeroOrbit → Set

    ComplexPoissonHermitianNormIdentity : Set
    CoshExcessControlsAlphaSquared : Set
    FiniteWindowRetainsExcess : Set
    MixedInterferenceCannotSwallowDiagonal : Set
    PrimeTraceMainTermNormalized : Set

    complexPoissonHermitianNormIdentity :
      ComplexPoissonHermitianNormIdentity
    coshExcessControlsAlphaSquared :
      CoshExcessControlsAlphaSquared
    finiteWindowRetainsExcess :
      FiniteWindowRetainsExcess
    mixedInterferenceCannotSwallowDiagonal :
      MixedInterferenceCannotSwallowDiagonal
    primeTraceMainTermNormalized :
      PrimeTraceMainTermNormalized

    detectabilityAssembly :
      (rho : ZeroOrbit) →
      offLine rho →
      HermitianExcessDetectabilityAssembly

open AlpogeFurmanHermitianDreamProducer public

alpogeFurmanHermitianDreamExcludesOffLine :
  (p : AlpogeFurmanHermitianDreamProducer) →
  (rho : ZeroOrbit p) →
  offLine p rho →
  ⊥
alpogeFurmanHermitianDreamExcludesOffLine p rho h =
  hermitianExcessDetectabilityContradiction
    (detectabilityAssembly p rho h)

------------------------------------------------------------------------
-- Alternative error-floor closers can still be exposed separately.  The
-- source-shaped producer above is the canonical final socket once one of
-- localization / higher moments / arithmetic rigidity has manufactured the
-- strict pair-above-error assembly.
------------------------------------------------------------------------

record HermitianDreamRouteBoundary : Set where
  field
    completeConditionalDependencyStackConstructed : Bool
    typedEndgameDispatchIntegrated : Bool
    proofRelevantDetectabilityAssemblyIntegrated : Bool
    sourceShapedOffLineContradictionClosed : Bool
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
  ; proofRelevantDetectabilityAssemblyIntegrated = true
  ; sourceShapedOffLineContradictionClosed = true
  ; proseOnlySeamsEliminatedFromArchitecture = true
  ; complexPoissonProducerInstantiatedForZeta = false
  ; finiteRetentionInstantiatedForZeta = false
  ; mixedDominationInstantiatedForZeta = false
  ; primeExcessNormalizationInstantiatedForZeta = false
  ; errorFloorCloserInstantiatedForZeta = false
  ; riemannHypothesisProvedHere = false
  }
