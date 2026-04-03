module DASHI.Physics.Closure.ShiftContractAnchoredTriadicFamily where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Vec using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (cong; sym)

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
  using (TriadicIndex; i0; i1; i2; triadicNext)

------------------------------------------------------------------------
-- A broader-support triadic family on the same carrier.
--
-- Unlike the first one-hot triad, these states keep the coarse head fixed at
-- `pos` and rotate a second active tail coordinate.  This is still a genuine
-- same-`π-mdl-max` family, but it now uses support width two rather than one.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

anchored0 : ShiftContractState
anchored0 = pos ∷ pos ∷ zer ∷ zer ∷ []

anchored1 : ShiftContractState
anchored1 = pos ∷ zer ∷ pos ∷ zer ∷ []

anchored2 : ShiftContractState
anchored2 = pos ∷ zer ∷ zer ∷ pos ∷ []

anchoredGen : TriadicIndex → ShiftContractState
anchoredGen i0 = anchored0
anchoredGen i1 = anchored1
anchoredGen i2 = anchored2

anchored-π-mdl-max-constant :
  ∀ i j →
  π-mdl-max (anchoredGen i) ≡ π-mdl-max (anchoredGen j)
anchored-π-mdl-max-constant i0 i0 = refl
anchored-π-mdl-max-constant i0 i1 = refl
anchored-π-mdl-max-constant i0 i2 = refl
anchored-π-mdl-max-constant i1 i0 = refl
anchored-π-mdl-max-constant i1 i1 = refl
anchored-π-mdl-max-constant i1 i2 = refl
anchored-π-mdl-max-constant i2 i0 = refl
anchored-π-mdl-max-constant i2 i1 = refl
anchored-π-mdl-max-constant i2 i2 = refl

anchoredPrimeDistinct01 :
  shiftContractStateTransportedPrimeEmbedding anchored0
    ≢
  shiftContractStateTransportedPrimeEmbedding anchored1
anchoredPrimeDistinct01 eq with cong GL.Vec15.e3 eq
... | ()

anchoredPrimeDistinct02 :
  shiftContractStateTransportedPrimeEmbedding anchored0
    ≢
  shiftContractStateTransportedPrimeEmbedding anchored2
anchoredPrimeDistinct02 eq with cong GL.Vec15.e3 eq
... | ()

anchoredPrimeDistinct12 :
  shiftContractStateTransportedPrimeEmbedding anchored1
    ≢
  shiftContractStateTransportedPrimeEmbedding anchored2
anchoredPrimeDistinct12 eq with cong GL.Vec15.e5 eq
... | ()

record ShiftContractAnchoredTriadicFamily : Set₁ where
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

canonicalShiftContractAnchoredTriadicFamily :
  ShiftContractAnchoredTriadicFamily
canonicalShiftContractAnchoredTriadicFamily =
  record
    { gen = anchoredGen
    ; sameSurface = anchored-π-mdl-max-constant
    ; cycle3 = STF.triadicCycle
    ; primeSplit01 = anchoredPrimeDistinct01
    ; primeSplit02 = anchoredPrimeDistinct02
    ; primeSplit12 = anchoredPrimeDistinct12
    }

open ShiftContractAnchoredTriadicFamily public
