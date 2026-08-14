module DASHI.Cognition.PNF.OrientedZeroCanonicalFutureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.OrientedZeroFutureQuotientExact as Wave
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- CANONICAL FUTURE-LANGUAGE WITNESS FOR ORIENTED ZERO
------------------------------------------------------------------------

data Action : Set where
  tick : Action

record ExactWavePost
    (before : Wave.Wave4)
    (action : Action)
    (after : Wave.Wave4) : Set where
  constructor exactWavePost
  field
    afterIsWaveStep : after ≡ Wave.waveStep before

open ExactWavePost public

waveSystem : Dependency.DependentActionSystem Wave.Wave4 Action
waveSystem = record
  { Precondition = λ state action → ⊤
  ; Postcondition = ExactWavePost
  ; actionLabel = λ action → "advance oriented wave phase"
  }

admissibleTick :
  (state : Wave.Wave4) →
  Dependency.AdmissibleAction waveSystem state tick
admissibleTick state = record
  { precondition = tt
  ; after = Wave.waveStep state
  ; postcondition = exactWavePost refl
  ; dependencyReceipt = "deterministic signed-zero wave step"
  }

negativeZeroTickObservation :
  Future.FutureObservation
    waveSystem Wave.scalar Wave.negativeZero
    (tick ∷ []) Wave.scalarZero
negativeZeroTickObservation =
  Future.futureObservation
    Wave.positiveZero
    (Reachability.executesCons (admissibleTick Wave.negativeZero) Reachability.executesNil)
    refl

positiveZeroCannotTickToScalarZero :
  Future.FutureObservation
    waveSystem Wave.scalar Wave.positiveZero
    (tick ∷ []) Wave.scalarZero → ⊥
positiveZeroCannotTickToScalarZero
  (Future.futureObservation after
    (Reachability.executesCons admissible Reachability.executesNil)
    observationProof)
  with afterIsWaveStep (Dependency.postcondition admissible)
... | refl = impossible observationProof
  where
    impossible : Wave.positive ≡ Wave.scalarZero → ⊥
    impossible ()

negativeZeroNotCanonicalFutureEquivalentPositiveZero :
  Future.FutureObservationEquivalent
    waveSystem Wave.scalar Wave.negativeZero Wave.positiveZero → ⊥
negativeZeroNotCanonicalFutureEquivalentPositiveZero equivalent =
  positiveZeroCannotTickToScalarZero
    (Future.forward
      (Future.sameFutureLanguage equivalent (tick ∷ []) Wave.scalarZero)
      negativeZeroTickObservation)

scalarProjectionHasCanonicalDynamicDefect :
  Wave.scalar Wave.negativeZero ≡ Wave.scalar Wave.positiveZero
  × (Future.FutureObservationEquivalent
      waveSystem Wave.scalar Wave.negativeZero Wave.positiveZero → ⊥)
scalarProjectionHasCanonicalDynamicDefect =
  refl , negativeZeroNotCanonicalFutureEquivalentPositiveZero

------------------------------------------------------------------------
-- Signed zero therefore supplies an exact, physically motivated instance of
-- the generic PNF principle: equal present scalar value does not imply equal
-- admissible future language.
------------------------------------------------------------------------
