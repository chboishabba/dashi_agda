module DASHI.Physics.Closure.NSGalerkinSameObjectExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jean Leray,
-- "Sur le mouvement d'un liquide visqueux emplissant l'espace",
-- Acta Mathematica 63 (1934), 193--248.
-- No DOI is assigned in the original source used here.
--
-- Wojciech S. Ozański; Benjamin C. Pooley,
-- "Leray's Fundamental Work on the Navier--Stokes Equations: A Modern
-- Review of 'Sur le mouvement d'un liquide visqueux emplissant l'espace'",
-- in Partial Differential Equations in Fluid Mechanics, 2018.
-- DOI: 10.1017/9781108610575.007.
--
-- DASHI CONTRIBUTION
--
-- Give the finite Galerkin lane literal same-object semantics.  The stored
-- coefficient function is no longer an arbitrary field of the state record.
-- It is the output of a representation-preserving physical-source -> encoded
-- state -> coefficient-function chain.  Positive and negative Fourier lookup,
-- cutoff retention and the elementary cyclic triad cancellation are then
-- definitions or exact rational identities of that same produced object.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Physics.Common.PhysicalProducerMaturityExact as Producer

record CanonicalGalerkinState (Mode : Set) : Set₁ where
  field
    PhysicalState EncodedState : Set
    physicalState : PhysicalState

    encode : PhysicalState → EncodedState
    decodeCoefficients : EncodedState → Mode → ℚ

    RepresentsEncoding : PhysicalState → EncodedState → Set
    RepresentsCoefficients : EncodedState → (Mode → ℚ) → Set

    producerChain :
      Producer.SameCarrierSameObject
        physicalState encode decodeCoefficients
        RepresentsEncoding RepresentsCoefficients

    negateMode : Mode → Mode
    retained : Mode → Bool
open CanonicalGalerkinState public

encodedState :
  ∀ {Mode} (state : CanonicalGalerkinState Mode) →
  EncodedState state
encodedState state =
  Producer.intermediate (producerChain state)

coefficient :
  ∀ {Mode} → CanonicalGalerkinState Mode → Mode → ℚ
coefficient state =
  Producer.output (producerChain state)

physicalStateRepresentsEncoding :
  ∀ {Mode} (state : CanonicalGalerkinState Mode) →
  RepresentsEncoding state
    (physicalState state) (encodedState state)
physicalStateRepresentsEncoding state =
  Producer.sourceRepresentsIntermediate (producerChain state)

encodingRepresentsCoefficientFunction :
  ∀ {Mode} (state : CanonicalGalerkinState Mode) →
  RepresentsCoefficients state
    (encodedState state) (coefficient state)
encodingRepresentsCoefficientFunction state =
  Producer.intermediateRepresentsOutput (producerChain state)

coefficientIsLiteralProducerComposite :
  ∀ {Mode} (state : CanonicalGalerkinState Mode) →
  coefficient state
  ≡ decodeCoefficients state (encode state (physicalState state))
coefficientIsLiteralProducerComposite state =
  Producer.sameCarrierCompositeExact (producerChain state)

ifRetained : Bool → ℚ → ℚ
ifRetained true value = value
ifRetained false value = 0ℚ

velocityAtPositive :
  ∀ {Mode} → CanonicalGalerkinState Mode → Mode → ℚ
velocityAtPositive state mode = coefficient state mode

velocityAtNegative :
  ∀ {Mode} → CanonicalGalerkinState Mode → Mode → ℚ
velocityAtNegative state mode =
  coefficient state (negateMode state mode)

retainedVelocity :
  ∀ {Mode} → CanonicalGalerkinState Mode → Mode → ℚ
retainedVelocity state mode with retained state mode
... | true = coefficient state mode
... | false = 0ℚ

velocityAtPositiveExact :
  ∀ {Mode} (state : CanonicalGalerkinState Mode) mode →
  velocityAtPositive state mode ≡ coefficient state mode
velocityAtPositiveExact state mode = refl

velocityAtNegativeExact :
  ∀ {Mode} (state : CanonicalGalerkinState Mode) mode →
  velocityAtNegative state mode
  ≡ coefficient state (negateMode state mode)
velocityAtNegativeExact state mode = refl

retainedModesExact :
  ∀ {Mode} (state : CanonicalGalerkinState Mode) mode →
  retainedVelocity state mode
  ≡ ifRetained (retained state mode) (coefficient state mode)
retainedModesExact state mode with retained state mode
... | true = refl
... | false = refl

retainedPositiveLookupExact :
  ∀ {Mode} (state : CanonicalGalerkinState Mode) mode →
  retainedVelocity state mode
  ≡ ifRetained (retained state mode) (velocityAtPositive state mode)
retainedPositiveLookupExact state mode with retained state mode
... | true = refl
... | false = refl

cyclicTriadTransfer : ℚ → ℚ → ℚ → ℚ
cyclicTriadTransfer first second third =
  (first - second) + (second - third) + (third - first)

actualTriadCancellationExact :
  ∀ first second third →
  cyclicTriadTransfer first second third ≡ 0ℚ
actualTriadCancellationExact first second third =
  ℚRing.solve-∀ first second third
