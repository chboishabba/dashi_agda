module DASHI.Physics.Closure.ShiftContractTriadic3CycleInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Vec using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Algebra.Trit using (Trit; neg; pos; zer)
open import Ontology.GodelLattice as GL using (Vec15)

open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractParametricTriadicFamily
  using (width3)
open import DASHI.Physics.Closure.ShiftContractStateFamily as SCSF
  using
    ( Cyclic3ShiftContractStateFamily
    )
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using
    ( ShiftContractState
    ; shiftContractStateTransportedPrimeEmbedding
    )
open import DASHI.Physics.Closure.ShiftContractTriadicFamily as STF
  using (TriadicIndex; i0; i1; i2; triadicCycle; triadicNext)

------------------------------------------------------------------------
-- First concrete balanced triadic 3-cycle on the live 4-trit carrier.
--
-- Keep the head fixed at `pos` and rotate the balanced tail block
-- `(pos , zer , neg)` cyclically:
--   (pos , zer , neg)
--   (zer , neg , pos)
--   (neg , pos , zer)
--
-- This is the smallest same-carrier balanced cycle that is genuinely
-- non-pairwise and uses the real `ShiftContractState` constructors directly.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

embedBalancedTail :
  Trit → Trit → Trit → ShiftContractState
embedBalancedTail t1 t2 t3 = pos ∷ t1 ∷ t2 ∷ t3 ∷ []

x0 : ShiftContractState
x0 = embedBalancedTail pos zer neg

x1 : ShiftContractState
x1 = embedBalancedTail zer neg pos

x2 : ShiftContractState
x2 = embedBalancedTail neg pos zer

cycleGen : TriadicIndex → ShiftContractState
cycleGen i0 = x0
cycleGen i1 = x1
cycleGen i2 = x2

rotateTail3 : ShiftContractState → ShiftContractState
rotateTail3 (h ∷ t1 ∷ t2 ∷ t3 ∷ []) = h ∷ t2 ∷ t3 ∷ t1 ∷ []

cyc0 : rotateTail3 x0 ≡ x1
cyc0 = refl

cyc1 : rotateTail3 x1 ≡ x2
cyc1 = refl

cyc2 : rotateTail3 x2 ≡ x0
cyc2 = refl

rotate3-id-on-cycle : ∀ i → rotateTail3 (rotateTail3 (rotateTail3 (cycleGen i))) ≡ cycleGen i
rotate3-id-on-cycle i0 = refl
rotate3-id-on-cycle i1 = refl
rotate3-id-on-cycle i2 = refl

balancedPrimeDistinct01 :
  shiftContractStateTransportedPrimeEmbedding x0
    ≢
  shiftContractStateTransportedPrimeEmbedding x1
balancedPrimeDistinct01 eq with cong GL.Vec15.e3 eq
... | ()

balancedPrimeDistinct02 :
  shiftContractStateTransportedPrimeEmbedding x0
    ≢
  shiftContractStateTransportedPrimeEmbedding x2
balancedPrimeDistinct02 eq with cong GL.Vec15.e5 eq
... | ()

balancedPrimeDistinct12 :
  shiftContractStateTransportedPrimeEmbedding x1
    ≢
  shiftContractStateTransportedPrimeEmbedding x2
balancedPrimeDistinct12 eq with cong GL.Vec15.e3 eq
... | ()

balancedπ-constant :
  ∀ i j →
  π-mdl-max (cycleGen i) ≡ π-mdl-max (cycleGen j)
balancedπ-constant i0 i0 = refl
balancedπ-constant i0 i1 = refl
balancedπ-constant i0 i2 = refl
balancedπ-constant i1 i0 = refl
balancedπ-constant i1 i1 = refl
balancedπ-constant i1 i2 = refl
balancedπ-constant i2 i0 = refl
balancedπ-constant i2 i1 = refl
balancedπ-constant i2 i2 = refl

canonicalBalancedTriadic3Cycle : Cyclic3ShiftContractStateFamily
canonicalBalancedTriadic3Cycle =
  record
    { supportClass = width3
    ; gen = cycleGen
    ; sameπ = balancedπ-constant
    ; cycle3 = triadicCycle
    ; primeSplit01 = balancedPrimeDistinct01
    ; primeSplit02 = balancedPrimeDistinct02
    ; primeSplit12 = balancedPrimeDistinct12
    }
