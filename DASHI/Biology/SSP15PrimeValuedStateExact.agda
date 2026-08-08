module DASHI.Biology.SSP15PrimeValuedStateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem",
-- Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups",
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Separate an Ogg prime valuation from the internal five-by-three
-- symmetry-phase state.  A prime does not equal an internal lane: each prime
-- indexes a fibre containing every internal mode/phase choice together with
-- explicit residual geometry.  This makes examples such as (71,A1,0) and
-- (71,A2,-1) real typed values without manufacturing a canonical bijection.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; proj₂)

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Quotient
import DASHI.Biology.SSP15ComplementPhaseProjectorExact as Internal
import DASHI.Biology.SSP15JCoarseFineIntegratedExact as Integrated
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as D4
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

data ResidualGeometryKind : Set where
  noResidual : ResidualGeometryKind
  witnessResidual : ResidualGeometryKind
  relationResidual : ResidualGeometryKind
  triadicResidual : ResidualGeometryKind
  counterframeResidual : ResidualGeometryKind
  binaryFiveInterfaceResidual : ResidualGeometryKind
  unresolvedResidualGeometry : ResidualGeometryKind

record PrimeValuedSSP15State
    (prime : Lane.MonsterPrimeLane) : Set₁ where
  constructor prime-valued-ssp15-state
  field
    primeReading : Integrated.PrimeSpecificSSP15Reading prime
    internalLane : Internal.SSP15InternalLane
    residualGeometry : ResidualGeometryKind

open PrimeValuedSSP15State public

primeValue : ∀ {prime} → PrimeValuedSSP15State prime → Nat
primeValue {prime} state = Lane.monsterPrimeLaneToNat prime

internalMode :
  ∀ {prime} → PrimeValuedSSP15State prime → Quotient.ComplementMode5
internalMode state = proj₁ (internalLane state)

internalPhase :
  ∀ {prime} → PrimeValuedSSP15State prime → Internal.BalancedPhase
internalPhase state = proj₂ (internalLane state)

internalIrrepName :
  ∀ {prime} → PrimeValuedSSP15State prime → D4.D4IrrepKind
internalIrrepName state = Internal.modeToD4Irrep (internalMode state)

attachInternalLane :
  (prime : Lane.MonsterPrimeLane) →
  Internal.SSP15InternalLane →
  ResidualGeometryKind →
  PrimeValuedSSP15State prime
attachInternalLane prime lane residual =
  prime-valued-ssp15-state
    (Integrated.primeSpecificSSP15Reading prime)
    lane residual

primeValuationDoesNotRestrictInternalLane :
  (prime : Lane.MonsterPrimeLane) →
  (lane : Internal.SSP15InternalLane) →
  (residual : ResidualGeometryKind) →
  internalLane (attachInternalLane prime lane residual) ≡ lane
primeValuationDoesNotRestrictInternalLane prime lane residual = refl

p71A1Neutral : PrimeValuedSSP15State Lane.p71
p71A1Neutral =
  attachInternalLane Lane.p71
    (Quotient.mode09 , Harmonic.zeroTrit)
    binaryFiveInterfaceResidual

p71A2Counterposed : PrimeValuedSSP15State Lane.p71
p71A2Counterposed =
  attachInternalLane Lane.p71
    (Quotient.mode18 , Harmonic.negativeTrit)
    binaryFiveInterfaceResidual

p71A1NeutralValueIs71 : primeValue p71A1Neutral ≡ 71
p71A1NeutralValueIs71 = refl

p71A1NeutralIrrepNameIsA1 : internalIrrepName p71A1Neutral ≡ D4.A1
p71A1NeutralIrrepNameIsA1 = refl

p71A1NeutralPhaseIsZero :
  internalPhase p71A1Neutral ≡ Harmonic.zeroTrit
p71A1NeutralPhaseIsZero = refl

p71A2CounterposedIrrepNameIsA2 :
  internalIrrepName p71A2Counterposed ≡ D4.A2
p71A2CounterposedIrrepNameIsA2 = refl

p71A2CounterposedPhaseIsNegative :
  internalPhase p71A2Counterposed ≡ Harmonic.negativeTrit
p71A2CounterposedPhaseIsNegative = refl

p71ExamplesHaveSamePrimeDifferentInternalMode :
  internalMode p71A1Neutral ≡ internalMode p71A2Counterposed → ⊥
p71ExamplesHaveSamePrimeDifferentInternalMode ()

reversePrimeValuedPhase :
  ∀ {prime} → PrimeValuedSSP15State prime → PrimeValuedSSP15State prime
reversePrimeValuedPhase
  (prime-valued-ssp15-state reading lane residual) =
  prime-valued-ssp15-state reading (Internal.reverseLane lane) residual

reversePrimeValuedPhaseInvolutive :
  ∀ {prime} →
  (state : PrimeValuedSSP15State prime) →
  reversePrimeValuedPhase (reversePrimeValuedPhase state) ≡ state
reversePrimeValuedPhaseInvolutive
  (prime-valued-ssp15-state reading lane residual)
  rewrite Internal.reverseLaneInvolutive lane = refl

reversePhasePreservesPrimeValue :
  ∀ {prime} →
  (state : PrimeValuedSSP15State prime) →
  primeValue (reversePrimeValuedPhase state) ≡ primeValue state
reversePhasePreservesPrimeValue state = refl

record SSP15PrimeValuedStateBoundary : Set₁ where
  constructor ssp15-prime-valued-state-boundary
  field
    everyPrimeAcceptsEveryInternalLane :
      (prime : Lane.MonsterPrimeLane) →
      (lane : Internal.SSP15InternalLane) →
      (residual : ResidualGeometryKind) →
      internalLane (attachInternalLane prime lane residual) ≡ lane
    p71InternalModesAreDistinct :
      internalMode p71A1Neutral ≡ internalMode p71A2Counterposed → ⊥
    phaseReversalIsInvolutive :
      ∀ {prime} →
      (state : PrimeValuedSSP15State prime) →
      reversePrimeValuedPhase (reversePrimeValuedPhase state) ≡ state
    phaseReversalPreservesPrime :
      ∀ {prime} →
      (state : PrimeValuedSSP15State prime) →
      primeValue (reversePrimeValuedPhase state) ≡ primeValue state
    equalPrimeAndInternalCardinalitySuppliesCanonicalBijection : Bool
    equalPrimeAndInternalCardinalitySuppliesCanonicalBijectionIsFalse :
      equalPrimeAndInternalCardinalitySuppliesCanonicalBijection ≡ false

canonicalSSP15PrimeValuedStateBoundary : SSP15PrimeValuedStateBoundary
canonicalSSP15PrimeValuedStateBoundary =
  ssp15-prime-valued-state-boundary
    primeValuationDoesNotRestrictInternalLane
    p71ExamplesHaveSamePrimeDifferentInternalMode
    reversePrimeValuedPhaseInvolutive
    reversePhasePreservesPrimeValue
    false refl
