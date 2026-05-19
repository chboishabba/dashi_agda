module DASHI.Physics.Closure.ShiftContractDenseTriadicFamily where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Vec using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Algebra.Trit using (pos; zer)
open import Ontology.GodelLattice as GL using (Vec15)

open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using
    ( ShiftContractState
    ; shiftContractStateTransportedPrimeEmbedding
    )
open import DASHI.Physics.Closure.ShiftContractTriadicFamily as STF
  using (TriadicIndex; i0; i1; i2; triadicNext; triadicCycle)

------------------------------------------------------------------------
-- A denser explicit triadic family on the same carrier.
--
-- Keep the coarse head fixed at `pos` and rotate the single zero across the
-- tail.  This lifts the positive explicit-source story from support width two
-- to support width three without changing the observable surface.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

dense0 : ShiftContractState
dense0 = pos ∷ pos ∷ pos ∷ zer ∷ []

dense1 : ShiftContractState
dense1 = pos ∷ pos ∷ zer ∷ pos ∷ []

dense2 : ShiftContractState
dense2 = pos ∷ zer ∷ pos ∷ pos ∷ []

denseGen : TriadicIndex → ShiftContractState
denseGen i0 = dense0
denseGen i1 = dense1
denseGen i2 = dense2

dense-π-mdl-max-constant :
  ∀ i j →
  π-mdl-max (denseGen i) ≡ π-mdl-max (denseGen j)
dense-π-mdl-max-constant i0 i0 = refl
dense-π-mdl-max-constant i0 i1 = refl
dense-π-mdl-max-constant i0 i2 = refl
dense-π-mdl-max-constant i1 i0 = refl
dense-π-mdl-max-constant i1 i1 = refl
dense-π-mdl-max-constant i1 i2 = refl
dense-π-mdl-max-constant i2 i0 = refl
dense-π-mdl-max-constant i2 i1 = refl
dense-π-mdl-max-constant i2 i2 = refl

densePrimeDistinct01 :
  shiftContractStateTransportedPrimeEmbedding dense0
    ≢
  shiftContractStateTransportedPrimeEmbedding dense1
densePrimeDistinct01 eq with cong GL.Vec15.e5 eq
... | ()

densePrimeDistinct02 :
  shiftContractStateTransportedPrimeEmbedding dense0
    ≢
  shiftContractStateTransportedPrimeEmbedding dense2
densePrimeDistinct02 eq with cong GL.Vec15.e3 eq
... | ()

densePrimeDistinct12 :
  shiftContractStateTransportedPrimeEmbedding dense1
    ≢
  shiftContractStateTransportedPrimeEmbedding dense2
densePrimeDistinct12 eq with cong GL.Vec15.e3 eq
... | ()

record ShiftContractDenseTriadicFamily : Set₁ where
  field
    gen : TriadicIndex → ShiftContractState
    sameSurface :
      ∀ i j →
      π-mdl-max (gen i) ≡ π-mdl-max (gen j)
    cycle3 :
      ∀ i →
      triadicNext (triadicNext (triadicNext i)) ≡ i
    primeSplit01 :
      shiftContractStateTransportedPrimeEmbedding (gen i0)
        ≢
      shiftContractStateTransportedPrimeEmbedding (gen i1)
    primeSplit02 :
      shiftContractStateTransportedPrimeEmbedding (gen i0)
        ≢
      shiftContractStateTransportedPrimeEmbedding (gen i2)
    primeSplit12 :
      shiftContractStateTransportedPrimeEmbedding (gen i1)
        ≢
      shiftContractStateTransportedPrimeEmbedding (gen i2)

canonicalShiftContractDenseTriadicFamily :
  ShiftContractDenseTriadicFamily
canonicalShiftContractDenseTriadicFamily =
  record
    { gen = denseGen
    ; sameSurface = dense-π-mdl-max-constant
    ; cycle3 = triadicCycle
    ; primeSplit01 = densePrimeDistinct01
    ; primeSplit02 = densePrimeDistinct02
    ; primeSplit12 = densePrimeDistinct12
    }

open ShiftContractDenseTriadicFamily public
