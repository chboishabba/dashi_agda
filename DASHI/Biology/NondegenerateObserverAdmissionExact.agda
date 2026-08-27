module DASHI.Biology.NondegenerateObserverAdmissionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Ported theorem shape from the supplied Aristotle archive:
--   Lean/Spine/Observer.lean
--
-- A map alone is not enough to inherit an observer theorem.  The observed
-- channel must have a nonzero common/anchoring component and non-flat
-- transverse variation.  This finite Nat-valued owner keeps that admission
-- criterion explicit.

natDistance : Nat → Nat → Nat
natDistance a b = (a ∸ b) + (b ∸ a)

record TripleSignal : Set where
  constructor tripleSignal
  field
    first : Nat
    second : Nat
    third : Nat

open TripleSignal public

signalMass : TripleSignal → Nat
signalMass s = first s + second s + third s

signalVariation : TripleSignal → Nat
signalVariation s =
  natDistance (first s) (second s)
  + natDistance (second s) (third s)
  + natDistance (third s) (first s)

observedAreaCode : TripleSignal → TripleSignal → Nat
observedAreaCode read channel = signalMass read * signalVariation channel

flatSignal : Nat → TripleSignal
flatSignal n = tripleSignal n n n

flatSignalHasZeroVariation :
  (n : Nat) → signalVariation (flatSignal n) ≡ 0
flatSignalHasZeroVariation n = refl

degenerateObserverAreaZero :
  (read : TripleSignal) (n : Nat) →
  observedAreaCode read (flatSignal n) ≡ 0
degenerateObserverAreaZero read n = refl

record NondegenerateFiniteObserver : Set where
  constructor nondegenerateFiniteObserver
  field
    read : TripleSignal
    channel : TripleSignal
    readMass : Nat
    channelVariation : Nat
    readMassCertificate : signalMass read ≡ readMass
    variationCertificate : signalVariation channel ≡ channelVariation

open NondegenerateFiniteObserver public

canonicalObserver : NondegenerateFiniteObserver
canonicalObserver =
  nondegenerateFiniteObserver
    (tripleSignal 1 1 1)
    (tripleSignal 0 1 2)
    3
    4
    refl
    refl

canonicalObserverAreaIsTwelve :
  observedAreaCode (read canonicalObserver) (channel canonicalObserver) ≡ 12
canonicalObserverAreaIsTwelve = refl

canonicalReadMassNonzero :
  readMass canonicalObserver ≡ 3
canonicalReadMassNonzero = refl

canonicalChannelVariationNonzero :
  channelVariation canonicalObserver ≡ 4
canonicalChannelVariationNonzero = refl

------------------------------------------------------------------------
-- Admission classes used by cross-domain bridges.

data ObserverAdmission : Set where
  degenerateObserver : ObserverAdmission
  informativeObserver : ObserverAdmission

classifyObserver : TripleSignal → TripleSignal → ObserverAdmission
classifyObserver read channel with signalMass read | signalVariation channel
... | zero | v = degenerateObserver
... | suc m | zero = degenerateObserver
... | suc m | suc v = informativeObserver

canonicalObserverIsInformative :
  classifyObserver (read canonicalObserver) (channel canonicalObserver)
  ≡ informativeObserver
canonicalObserverIsInformative = refl

flatObserverIsDegenerate :
  classifyObserver (tripleSignal 1 1 1) (flatSignal 2)
  ≡ degenerateObserver
flatObserverIsDegenerate = refl

record ObserverAdmissionBoundary : Set where
  constructor observerAdmissionBoundary
  field
    existenceOfMapImpliesInformativeObservation : Bool
    existenceOfMapImpliesInformativeObservationIsFalse :
      existenceOfMapImpliesInformativeObservation ≡ false

    zeroVariationCarriesIndependentRelationalInformation : Bool
    zeroVariationCarriesIndependentRelationalInformationIsFalse :
      zeroVariationCarriesIndependentRelationalInformation ≡ false

canonicalObserverAdmissionBoundary : ObserverAdmissionBoundary
canonicalObserverAdmissionBoundary =
  observerAdmissionBoundary false refl false refl
