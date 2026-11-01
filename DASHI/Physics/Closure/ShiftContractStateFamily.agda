module DASHI.Physics.Closure.ShiftContractStateFamily where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)
open import Ontology.GodelLattice using (FactorVec)

open import DASHI.Physics.Closure.ShiftContractAnchoredTriadicFamily as SATF
  using
    ( anchored-π-mdl-max-constant
    ; anchoredGen
    ; anchoredPrimeDistinct01
    ; anchoredPrimeDistinct02
    ; anchoredPrimeDistinct12
    )
open import DASHI.Physics.Closure.ShiftContractDenseTriadicFamily as SDTF
  using
    ( dense-π-mdl-max-constant
    ; denseGen
    ; densePrimeDistinct01
    ; densePrimeDistinct02
    ; densePrimeDistinct12
    )
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (MdlLevelCoarseObservable; π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractParametricTriadicFamily as SPTF
  using (SupportWidth; width1; width2; width3)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using
    ( ShiftContractState
    ; shiftContractStateTransportedPrimeEmbedding
    )
open import DASHI.Physics.Closure.ShiftContractTriadicFamily as STF
  using
    ( TriadicIndex
    ; i0
    ; i1
    ; i2
    ; primeImageDistinct01
    ; primeImageDistinct02
    ; primeImageDistinct12
    ; triadic-π-mdl-max-constant
    ; triadicCycle
    ; triadicGen
    ; triadicNext
    )

------------------------------------------------------------------------
-- Normalized same-carrier family surface for the noncanonical seam.
--
-- This does not introduce abstract placeholders.  It packages the live
-- `ShiftContractState` carrier, the current normalized coarse surface
-- `π-mdl-max`, and the transported prime image already used throughout the
-- noncanonical audits and family modules.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

PrimeImage : Set
PrimeImage = FactorVec

primeImage : ShiftContractState → PrimeImage
primeImage = shiftContractStateTransportedPrimeEmbedding

record ShiftContractStateFamily (Index : Set) : Set₁ where
  field
    gen : Index → ShiftContractState
    sameπ :
      ∀ i j →
      π-mdl-max (gen i) ≡ π-mdl-max (gen j)
    supportWidth : Nat
    nontrivialPrimeImage :
      Σ Index
        (λ i →
          Σ Index
            (λ j →
              primeImage (gen i)
                ≢
              primeImage (gen j)))

record Cyclic3ShiftContractStateFamily : Set₁ where
  field
    supportClass : SupportWidth
    gen : TriadicIndex → ShiftContractState
    sameπ :
      ∀ i j →
      π-mdl-max (gen i) ≡ π-mdl-max (gen j)
    cycle3 :
      ∀ i →
      triadicNext (triadicNext (triadicNext i)) ≡ i
    primeSplit01 :
      primeImage (gen i0) ≢ primeImage (gen i1)
    primeSplit02 :
      primeImage (gen i0) ≢ primeImage (gen i2)
    primeSplit12 :
      primeImage (gen i1) ≢ primeImage (gen i2)

cyclic3SupportWidth : Cyclic3ShiftContractStateFamily → Nat
cyclic3SupportWidth f with Cyclic3ShiftContractStateFamily.supportClass f
... | width1 = 1
... | width2 = 2
... | width3 = 3

cyclic3AsFamily :
  Cyclic3ShiftContractStateFamily →
  ShiftContractStateFamily TriadicIndex
cyclic3AsFamily f =
  record
    { gen = Cyclic3ShiftContractStateFamily.gen f
    ; sameπ = Cyclic3ShiftContractStateFamily.sameπ f
    ; supportWidth = cyclic3SupportWidth f
    ; nontrivialPrimeImage = i0 , (i1 , Cyclic3ShiftContractStateFamily.primeSplit01 f)
    }

canonicalOneHotCyclic3Family : Cyclic3ShiftContractStateFamily
canonicalOneHotCyclic3Family =
  record
    { supportClass = width1
    ; gen = triadicGen
    ; sameπ = triadic-π-mdl-max-constant
    ; cycle3 = triadicCycle
    ; primeSplit01 = primeImageDistinct01
    ; primeSplit02 = primeImageDistinct02
    ; primeSplit12 = primeImageDistinct12
    }

canonicalAnchoredCyclic3Family : Cyclic3ShiftContractStateFamily
canonicalAnchoredCyclic3Family =
  record
    { supportClass = width2
    ; gen = anchoredGen
    ; sameπ = anchored-π-mdl-max-constant
    ; cycle3 = triadicCycle
    ; primeSplit01 = anchoredPrimeDistinct01
    ; primeSplit02 = anchoredPrimeDistinct02
    ; primeSplit12 = anchoredPrimeDistinct12
    }

canonicalDenseCyclic3Family : Cyclic3ShiftContractStateFamily
canonicalDenseCyclic3Family =
  record
    { supportClass = width3
    ; gen = denseGen
    ; sameπ = dense-π-mdl-max-constant
    ; cycle3 = triadicCycle
    ; primeSplit01 = densePrimeDistinct01
    ; primeSplit02 = densePrimeDistinct02
    ; primeSplit12 = densePrimeDistinct12
    }

canonicalCyclic3FamilyAt :
  SupportWidth → Cyclic3ShiftContractStateFamily
canonicalCyclic3FamilyAt width1 = canonicalOneHotCyclic3Family
canonicalCyclic3FamilyAt width2 = canonicalAnchoredCyclic3Family
canonicalCyclic3FamilyAt width3 = canonicalDenseCyclic3Family

canonicalFamilyAt :
  SupportWidth → ShiftContractStateFamily TriadicIndex
canonicalFamilyAt w = cyclic3AsFamily (canonicalCyclic3FamilyAt w)

record ShiftContractStateFamilySchema : Set₂ where
  field
    coarseSurface : ShiftContractState → MdlLevelCoarseObservable
    primeSurface : ShiftContractState → PrimeImage
    cyclicAt : SupportWidth → Cyclic3ShiftContractStateFamily

canonicalShiftContractStateFamilySchema :
  ShiftContractStateFamilySchema
canonicalShiftContractStateFamilySchema =
  record
    { coarseSurface = π-mdl-max
    ; primeSurface = primeImage
    ; cyclicAt = canonicalCyclic3FamilyAt
    }

open ShiftContractStateFamily public
open Cyclic3ShiftContractStateFamily public
open ShiftContractStateFamilySchema public
