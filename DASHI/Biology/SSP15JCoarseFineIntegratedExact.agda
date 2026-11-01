module DASHI.Biology.SSP15JCoarseFineIntegratedExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves",
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem",
-- Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Replace the old lane-independent Stage-5 reading by a prime-specific object
-- combining the exact p = 9q+r address, its typed nine-observer entry, the
-- existing 9 x 3^9 j-coarse/j-fine scale, and the shared evaluation map at j.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_; _*_)

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.JCoarseFineEvaluationFibreExact as J
import DASHI.Biology.JFineCoarseRelativeScaleExact as Scale
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Quotient
import DASHI.Biology.OggPrimeNonaryAddressExact as Address
import DASHI.Biology.SSP15ComplementPhaseProjectorExact as Internal
import DASHI.Biology.SSP15NineObserverAtlasExact as Atlas
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

record PrimeSpecificSSP15Reading
    (prime : Lane.MonsterPrimeLane) : Set₁ where
  constructor prime-specific-ssp15-reading
  field
    nonaryAddress : Address.NonaryOggAddress prime
    nineObserver : Atlas.SSP15NineAtlasEntry prime
    jCoarseScale : Nat
    jFineScale : Nat
    jAbsoluteScale : Nat
    jCoarseScaleExact : jCoarseScale ≡ Scale.jCoarseFrequency
    jFineScaleExact : jFineScale ≡ Scale.jFineFrequency
    jAbsoluteScaleExact : jAbsoluteScale ≡ Scale.jAbsoluteFineFrequency
    jAbsoluteFactors : jAbsoluteScale ≡ jCoarseScale * jFineScale
    finiteJEvaluation : J.PointedCoarseFineEvaluation

open PrimeSpecificSSP15Reading public

primeSpecificSSP15Reading :
  (prime : Lane.MonsterPrimeLane) → PrimeSpecificSSP15Reading prime
primeSpecificSSP15Reading prime =
  prime-specific-ssp15-reading
    (Address.nonaryOggAddress prime)
    (Atlas.ssp15NineAtlas prime)
    Scale.jCoarseFrequency
    Scale.jFineFrequency
    Scale.jAbsoluteFineFrequency
    refl refl refl
    Scale.jAbsoluteFineIsCoarseTimesJFine
    J.canonicalJCoarseFineEvaluation

primeSpecificAddressReconstructsValue :
  (prime : Lane.MonsterPrimeLane) →
  Lane.monsterPrimeLaneToNat prime
  ≡ Address.coarseSheets (nonaryAddress (primeSpecificSSP15Reading prime)) * 9
    + Address.remainder (nonaryAddress (primeSpecificSSP15Reading prime))
primeSpecificAddressReconstructsValue prime =
  Address.addressExact (nonaryAddress (primeSpecificSSP15Reading prime))

primeSpecificObserverValueMatchesPrime :
  (prime : Lane.MonsterPrimeLane) →
  Atlas.observedValue (nineObserver (primeSpecificSSP15Reading prime))
  ≡ Lane.monsterPrimeLaneToNat prime
primeSpecificObserverValueMatchesPrime prime =
  Atlas.observedValueIsPrimeLane
    (nineObserver (primeSpecificSSP15Reading prime))

-- Every prime reading shares one j-evaluation map; no prime-specific
-- surjectivity is claimed.
sharedJEvaluationIsSurjective :
  (fine : Harmonic.FineFrequency) → J.JFineEvaluationFibre fine
sharedJEvaluationIsSurjective = J.jEvaluationIsSurjective

seventyOneCoarseSheetsAreSeven :
  Address.coarseSheets
    (nonaryAddress (primeSpecificSSP15Reading Lane.p71)) ≡ 7
seventyOneCoarseSheetsAreSeven = refl

seventyOneFineStateIsEight :
  Address.fineState
    (nonaryAddress (primeSpecificSSP15Reading Lane.p71)) ≡ Quotient.d8
seventyOneFineStateIsEight = refl

seventyOneModeIsWitnessResidual :
  Address.complementMode
    (nonaryAddress (primeSpecificSSP15Reading Lane.p71))
  ≡ Quotient.mode18
seventyOneModeIsWitnessResidual = refl

seventyOneOrientationIsCounter :
  Address.binaryOrientation
    (nonaryAddress (primeSpecificSSP15Reading Lane.p71))
  ≡ Quotient.counterPhase
seventyOneOrientationIsCounter = refl

seventyOneRemovesBinaryFiveInterface : 71 + 5 * 2 ≡ 81
seventyOneRemovesBinaryFiveInterface =
  Address.seventyOneRemovesCompleteBinaryFiveInterface

record OggInternalLaneBijection : Set where
  field
    forward : Lane.MonsterPrimeLane → Internal.SSP15InternalLane
    backward : Internal.SSP15InternalLane → Lane.MonsterPrimeLane
    backwardAfterForward :
      (prime : Lane.MonsterPrimeLane) → backward (forward prime) ≡ prime
    forwardAfterBackward :
      (lane : Internal.SSP15InternalLane) → forward (backward lane) ≡ lane

record SSP15JCoarseFineBoundary : Set₁ where
  constructor ssp15-j-coarse-fine-boundary
  field
    everyPrimeAddressReconstructs :
      (prime : Lane.MonsterPrimeLane) →
      Lane.monsterPrimeLaneToNat prime
      ≡ Address.coarseSheets
          (nonaryAddress (primeSpecificSSP15Reading prime)) * 9
        + Address.remainder
          (nonaryAddress (primeSpecificSSP15Reading prime))
    everyObserverValueMatchesPrime :
      (prime : Lane.MonsterPrimeLane) →
      Atlas.observedValue (nineObserver (primeSpecificSSP15Reading prime))
      ≡ Lane.monsterPrimeLaneToNat prime
    sharedJEvaluationSection :
      (fine : Harmonic.FineFrequency) → J.JFineEvaluationFibre fine
    canonicalOggInternalLaneBijectionConstructed : Bool
    canonicalOggInternalLaneBijectionConstructedIsFalse :
      canonicalOggInternalLaneBijectionConstructed ≡ false
    finiteModelProvesSupersingularJTheorem : Bool
    finiteModelProvesSupersingularJTheoremIsFalse :
      finiteModelProvesSupersingularJTheorem ≡ false

canonicalSSP15JCoarseFineBoundary : SSP15JCoarseFineBoundary
canonicalSSP15JCoarseFineBoundary =
  ssp15-j-coarse-fine-boundary
    primeSpecificAddressReconstructsValue
    primeSpecificObserverValueMatchesPrime
    sharedJEvaluationIsSurjective
    false refl
    false refl
