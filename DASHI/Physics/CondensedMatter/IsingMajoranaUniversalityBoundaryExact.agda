module DASHI.Physics.CondensedMatter.IsingMajoranaUniversalityBoundaryExact where

------------------------------------------------------------------------
-- ATTRIBUTION
--
-- EXTERNAL SOURCE:
-- Eric C. Rowell, "Braids, Motions and Topological Quantum Computing",
-- arXiv:2208.11762v1 (2022), surveys that Ising anyons / Majorana zero
-- modes have finite braid-group image and are not universal by braiding
-- alone.  Extra resources such as measurement-assisted or non-topological
-- operations are needed for universal computation.
--
-- This file records that SOURCE CLAIM as a typed promotion boundary.
-- It does not derive the density/non-density theorem from first principles.
------------------------------------------------------------------------

open import Data.Empty using (⊥)

data CanonicalIsingBraidingAloneUniversal : Set where

canonicalIsingBraidingAloneNotUniversal :
  CanonicalIsingBraidingAloneUniversal →
  ⊥
canonicalIsingBraidingAloneNotUniversal ()

record IsingMajoranaUniversalitySourceClaim : Set₁ where
  field
    BraidingAloneUniversal : Set
    notUniversalByBraidingAlone :
      BraidingAloneUniversal → ⊥

open IsingMajoranaUniversalitySourceClaim public

canonicalIsingMajoranaUniversalitySourceClaim :
  IsingMajoranaUniversalitySourceClaim
canonicalIsingMajoranaUniversalitySourceClaim =
  record
    { BraidingAloneUniversal =
        CanonicalIsingBraidingAloneUniversal
    ; notUniversalByBraidingAlone =
        canonicalIsingBraidingAloneNotUniversal
    }

record UniversalCompletionResource : Set₁ where
  field
    Resource : Set
    resourceWitness : Resource

-- No canonical inhabitant is supplied: the concrete completion resource is
-- a separate engineering/experimental/computational obligation.
