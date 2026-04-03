module DASHI.Physics.Closure.ShiftContractTriadicFamily where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import Ontology.GodelLattice as GL using (Vec15)

open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (MdlLevelCoarseObservable; π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractMdlLevelExplicitStateSearchAudit as ES
  using (oneHot0; oneHot1; oneHot2)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using
    ( ShiftContractState
    ; shiftContractStateTransportedPrimeEmbedding
    )

------------------------------------------------------------------------
-- First same-carrier triadic family on ShiftContractState.
--
-- The bounded explicit-state audit already exposed the three one-hot states,
-- but only as members of the search pool.  This module packages them as an
-- actual triadic family witness:
-- - all three states lie in the same `π-mdl-max` fibre;
-- - their transported prime images are pairwise distinct.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

data TriadicIndex : Set where
  i0 i1 i2 : TriadicIndex

triadicGen : TriadicIndex → ShiftContractState
triadicGen i0 = oneHot0
triadicGen i1 = oneHot1
triadicGen i2 = oneHot2

triadicNext : TriadicIndex → TriadicIndex
triadicNext i0 = i1
triadicNext i1 = i2
triadicNext i2 = i0

triadicCycle : ∀ i → triadicNext (triadicNext (triadicNext i)) ≡ i
triadicCycle i0 = refl
triadicCycle i1 = refl
triadicCycle i2 = refl

triadic-π-mdl-max-constant :
  ∀ i j →
  π-mdl-max (triadicGen i) ≡ π-mdl-max (triadicGen j)
triadic-π-mdl-max-constant i0 i0 = refl
triadic-π-mdl-max-constant i0 i1 = refl
triadic-π-mdl-max-constant i0 i2 = refl
triadic-π-mdl-max-constant i1 i0 = refl
triadic-π-mdl-max-constant i1 i1 = refl
triadic-π-mdl-max-constant i1 i2 = refl
triadic-π-mdl-max-constant i2 i0 = refl
triadic-π-mdl-max-constant i2 i1 = refl
triadic-π-mdl-max-constant i2 i2 = refl

primeImageDistinct01 :
  shiftContractStateTransportedPrimeEmbedding oneHot0
    ≢
  shiftContractStateTransportedPrimeEmbedding oneHot1
primeImageDistinct01 eq with cong GL.Vec15.e2 eq
... | ()

primeImageDistinct02 :
  shiftContractStateTransportedPrimeEmbedding oneHot0
    ≢
  shiftContractStateTransportedPrimeEmbedding oneHot2
primeImageDistinct02 eq with cong GL.Vec15.e2 eq
... | ()

primeImageDistinct12 :
  shiftContractStateTransportedPrimeEmbedding oneHot1
    ≢
  shiftContractStateTransportedPrimeEmbedding oneHot2
primeImageDistinct12 eq with cong GL.Vec15.e3 eq
... | ()

triadicPrimeImageDistinct :
  ∀ i j →
  i ≢ j →
  shiftContractStateTransportedPrimeEmbedding (triadicGen i)
    ≢
  shiftContractStateTransportedPrimeEmbedding (triadicGen j)
triadicPrimeImageDistinct i0 i0 i≢j = ⊥-elim (i≢j refl)
  where
  ⊥-elim : ⊥ → _
  ⊥-elim ()
triadicPrimeImageDistinct i0 i1 _ = primeImageDistinct01
triadicPrimeImageDistinct i0 i2 _ = primeImageDistinct02
triadicPrimeImageDistinct i1 i0 i≢j = λ eq → primeImageDistinct01 (sym eq)
triadicPrimeImageDistinct i1 i1 i≢j = ⊥-elim (i≢j refl)
  where
  ⊥-elim : ⊥ → _
  ⊥-elim ()
triadicPrimeImageDistinct i1 i2 _ = primeImageDistinct12
triadicPrimeImageDistinct i2 i0 i≢j = λ eq → primeImageDistinct02 (sym eq)
triadicPrimeImageDistinct i2 i1 i≢j = λ eq → primeImageDistinct12 (sym eq)
triadicPrimeImageDistinct i2 i2 i≢j = ⊥-elim (i≢j refl)
  where
  ⊥-elim : ⊥ → _
  ⊥-elim ()

record ShiftContractTriadicFamily : Set₁ where
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

canonicalShiftContractTriadicFamily : ShiftContractTriadicFamily
canonicalShiftContractTriadicFamily =
  record
    { gen = triadicGen
    ; sameSurface = triadic-π-mdl-max-constant
    ; cycle3 = triadicCycle
    ; primeSplit01 = primeImageDistinct01
    ; primeSplit02 = primeImageDistinct02
    ; primeSplit12 = primeImageDistinct12
    }

open ShiftContractTriadicFamily public
