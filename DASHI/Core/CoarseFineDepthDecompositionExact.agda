module DASHI.Core.CoarseFineDepthDecompositionExact where

------------------------------------------------------------------------
-- COARSE / RELATIVE-FINE / ABSOLUTE DECOMPOSITION
--
-- BACKGROUND SOURCES
--
-- Ingrid Daubechies,
-- "Ten Lectures on Wavelets", SIAM, 1992.
-- DOI: 10.1137/1.9781611970104.
-- Used only as standard multiresolution-analysis background for separating
-- coarse and finer resolution coordinates.
--
-- Donald E. Knuth,
-- "The Art of Computer Programming, Volume 2: Seminumerical Algorithms",
-- 3rd ed., Addison-Wesley, 1997. ISBN 9780201896848.
-- Used as standard positional/radix background.
--
-- DASHI CONTRIBUTION
--
-- Several historically distinct constructions in the repository reconstruct
-- an absolute address from a carried/coarse component plus a relative/fresh
-- component.  This owner captures only that additive theorem shape.  It does
-- not identify decimal place values, triadic harmonic depth, stage semantics,
-- wavelet scale, or J data.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

record CoarseFineDecomposition : Set where
  constructor coarse-fine-decomposition
  field
    coarseComponent : Nat
    relativeFineComponent : Nat
    absoluteComponent : Nat
    reconstruction :
      absoluteComponent ≡ coarseComponent + relativeFineComponent

open CoarseFineDecomposition public

swapComponents : CoarseFineDecomposition → CoarseFineDecomposition
swapComponents decomposition =
  coarse-fine-decomposition
    (relativeFineComponent decomposition)
    (coarseComponent decomposition)
    (absoluteComponent decomposition)
    (swapProof decomposition)
  where
  swapProof :
    (d : CoarseFineDecomposition) →
    absoluteComponent d
    ≡ relativeFineComponent d + coarseComponent d
  swapProof (coarse-fine-decomposition 0 fine absolute proof) = proof
  swapProof (coarse-fine-decomposition (Nat.suc coarse) fine absolute proof) =
    trans proof (+-comm (Nat.suc coarse) fine)

  open import Data.Nat.Properties using (+-comm)
  open import Agda.Builtin.Nat as Nat using (Nat; zero; suc)

record CoarseFineDecompositionBoundary : Set where
  constructor coarse-fine-decomposition-boundary
  field
    sameAbsoluteValueImpliesSameSemanticRole : Bool
    sameAbsoluteValueImpliesSameSemanticRoleIsFalse :
      sameAbsoluteValueImpliesSameSemanticRole ≡ false
    additiveDecompositionImpliesPhysicalScaleLaw : Bool
    additiveDecompositionImpliesPhysicalScaleLawIsFalse :
      additiveDecompositionImpliesPhysicalScaleLaw ≡ false

canonicalCoarseFineDecompositionBoundary :
  CoarseFineDecompositionBoundary
canonicalCoarseFineDecompositionBoundary =
  coarse-fine-decomposition-boundary false refl false refl
