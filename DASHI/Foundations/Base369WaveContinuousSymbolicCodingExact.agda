module DASHI.Foundations.Base369WaveContinuousSymbolicCodingExact where

------------------------------------------------------------------------
-- MATHEMATICAL BACKGROUND
--
-- Ingrid Daubechies, "Ten Lectures on Wavelets", CBMS-NSF Regional
-- Conference Series in Applied Mathematics 61, SIAM, 1992.
-- DOI: 10.1137/1.9781611970104.
--
-- DASHI CONTRIBUTION
--
-- Balanced ternary is used here as a symbolic/address observer on an arbitrary
-- carrier.  The exact carrier value is retained in the fibre, so discretising
-- an address does not assert that the underlying wave, field, amplitude, phase,
-- operator, or continuous state is itself discrete.  The same construction is
-- parameterised over arbitrary odd signed alphabets and multiresolution
-- coefficient carriers.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Data.Fin.Base using (Fin)

open import Base369 using
  ( TriTruth
  ; tri-low
  ; tri-mid
  ; tri-high
  )
open import DASHI.Foundations.SSPTritCarrier using (SSPTrit)
open import DASHI.Foundations.Base369LayeredAttractorAndCoarseFineExact using
  ( CoarseFine11
  ; coarseFine11
  ; coarse1
  ; fine10
  )

------------------------------------------------------------------------
-- Exact symbolic coding of an arbitrary carrier.
------------------------------------------------------------------------

record SymbolicCoding (Carrier : Set) : Set₁ where
  constructor symbolicCoding
  field
    quantize : Carrier → SSPTrit

open SymbolicCoding public

record EncodedState
  {Carrier : Set}
  (coding : SymbolicCoding Carrier) : Set where
  constructor encodedState
  field
    exactState : Carrier
    symbolicState : SSPTrit
    symbolicStateCorrect : symbolicState ≡ quantize coding exactState

open EncodedState public

encode :
  {Carrier : Set} →
  (coding : SymbolicCoding Carrier) →
  Carrier → EncodedState coding
encode coding x = encodedState x (quantize coding x) refl

decode :
  {Carrier : Set} →
  {coding : SymbolicCoding Carrier} →
  EncodedState coding → Carrier
decode = exactState

decodeAfterEncode :
  {Carrier : Set} →
  (coding : SymbolicCoding Carrier) →
  (x : Carrier) →
  decode (encode coding x) ≡ x
decodeAfterEncode coding x = refl

-- The exact reconstruction theorem is the key non-flattening result: a trit is
-- an observer coordinate, not a replacement for the carrier state.

------------------------------------------------------------------------
-- Symbolic itineraries of arbitrary dynamics.
------------------------------------------------------------------------

record SymbolicFlow (State : Set) : Set₁ where
  constructor symbolicFlow
  field
    coding : SymbolicCoding State
    evolve : State → State

open SymbolicFlow public

stepEncoded :
  {State : Set} →
  (flow : SymbolicFlow State) →
  State → EncodedState (coding flow)
stepEncoded flow x = encode (coding flow) (evolve flow x)

stepEncodingRetainsExactState :
  {State : Set} →
  (flow : SymbolicFlow State) →
  (x : State) →
  decode (stepEncoded flow x) ≡ evolve flow x
stepEncodingRetainsExactState flow x = refl

------------------------------------------------------------------------
-- Multiresolution/wave-like coefficient cells.
------------------------------------------------------------------------

record MultiresolutionAddress (Scale Position : Set) : Set where
  constructor multiresolutionAddress
  field
    scale : Scale
    position : Position
    orientation : SSPTrit

open MultiresolutionAddress public

record CoefficientCell
  (Scale Position Coefficient : Set)
  (quantizeCoefficient : Coefficient → SSPTrit) : Set where
  constructor coefficientCell
  field
    coefficientScale : Scale
    coefficientPosition : Position
    exactCoefficient : Coefficient
    coefficientAddress : MultiresolutionAddress Scale Position
    addressExact :
      coefficientAddress
      ≡ multiresolutionAddress
          coefficientScale
          coefficientPosition
          (quantizeCoefficient exactCoefficient)

open CoefficientCell public

makeCoefficientCell :
  {Scale Position Coefficient : Set} →
  (quantizeCoefficient : Coefficient → SSPTrit) →
  Scale → Position → Coefficient →
  CoefficientCell Scale Position Coefficient quantizeCoefficient
makeCoefficientCell quantizeCoefficient j k coefficient =
  coefficientCell
    j
    k
    coefficient
    (multiresolutionAddress j k (quantizeCoefficient coefficient))
    refl

coefficientValueSurvivesAddressing :
  {Scale Position Coefficient : Set} →
  {quantizeCoefficient : Coefficient → SSPTrit} →
  (cell : CoefficientCell Scale Position Coefficient quantizeCoefficient) →
  exactCoefficient cell ≡ exactCoefficient cell
coefficientValueSurvivesAddressing cell = refl

------------------------------------------------------------------------
-- Structural 1+10 coarse/fine observation admits coarse/fine disagreement.
------------------------------------------------------------------------

coarsePositiveFineAdverse : CoarseFine11 TriTruth TriTruth
coarsePositiveFineAdverse = coarseFine11 tri-high (λ _ → tri-low)

coarsePositiveFineAdverseHasPositiveCoarse :
  coarse1 coarsePositiveFineAdverse ≡ tri-high
coarsePositiveFineAdverseHasPositiveCoarse = refl

coarsePositiveFineAdverseHasAdverseFine :
  (i : Fin 10) → fine10 coarsePositiveFineAdverse i ≡ tri-low
coarsePositiveFineAdverseHasAdverseFine i = refl

-- Consequently there is no theorem in this module that a positive coarse
-- observation forces positive fine observations.

------------------------------------------------------------------------
-- Generic balanced odd alphabets: m negative magnitudes, one zero, m positive
-- magnitudes.  The finite carrier has 2m+1 symbolic slots without imposing any
-- finiteness condition on the fibre carried at each slot.
------------------------------------------------------------------------

data BalancedOddDigit (m : Nat) : Set where
  negativeDigit : Fin m → BalancedOddDigit m
  zeroDigit : BalancedOddDigit m
  positiveDigit : Fin m → BalancedOddDigit m

balancedOddSymbolCount : Nat → Nat
balancedOddSymbolCount m = m + suc m

balancedTernarySymbolCount : balancedOddSymbolCount 1 ≡ 3
balancedTernarySymbolCount = refl

balancedQuinarySymbolCount : balancedOddSymbolCount 2 ≡ 5
balancedQuinarySymbolCount = refl

balancedNonarySymbolCount : balancedOddSymbolCount 4 ≡ 9
balancedNonarySymbolCount = refl

record OddAddressedFibre
  (m : Nat)
  (Fibre : BalancedOddDigit m → Set) : Set₁ where
  constructor oddAddressedFibre
  field
    oddAddress : BalancedOddDigit m
    oddPayload : Fibre oddAddress

open OddAddressedFibre public

------------------------------------------------------------------------
-- A richer continuous/wave implementation can instantiate Carrier,
-- Coefficient, Scale and Position with reals, complex amplitudes, fields,
-- distributions or operator spaces.  The theorems above need no assumption
-- that those payloads are finite or discrete.
------------------------------------------------------------------------
