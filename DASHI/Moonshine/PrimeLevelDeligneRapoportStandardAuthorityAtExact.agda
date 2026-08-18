module DASHI.Moonshine.PrimeLevelDeligneRapoportStandardAuthorityAtExact where

------------------------------------------------------------------------
-- PRIME-PINNED STANDARD AUTHORITY
--
-- Strengthen PrimeLevelDeligneRapoportStandardAuthority by tying the internal
-- prime carried by the source-facing Frobenius/special-fibre object to the
-- externally requested prime p.  Without this equality, an imported witness
-- "at p" could logically be a witness for a different prime.
--
-- Sources and DOI authority are exactly those recorded in
-- PrimeLevelDeligneRapoportStandardAuthority:
--   Deligne--Rapoport DOI 10.1007/978-3-540-37855-6_4;
--   Treneer DOI 10.1186/s40687-017-0115-z;
--   Hartshorne DOI 10.1007/978-1-4757-3849-0.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR

record PublishedPrimeLevelAuthorityAt (p : Nat) : Set₁ where
  field
    authority : Selector.PrimeLevelFrickeSpecialFibreAuthority
    authorityPrimeIsRequestedPrime :
      DR.prime (Selector.supersingularFrobenius authority) ≡ p

open PublishedPrimeLevelAuthorityAt public

postulate
  publishedPrimeLevelAuthorityAt :
    (p : Nat) → Prime p → 5 ≤ p → PublishedPrimeLevelAuthorityAt p

record PrimePinnedAuthorityBoundary : Set where
  field
    internalPrimeExplicitlyPinned : Bool
    selectorConclusionPostulated : Bool

canonicalPrimePinnedAuthorityBoundary : PrimePinnedAuthorityBoundary
canonicalPrimePinnedAuthorityBoundary = record
  { internalPrimeExplicitlyPinned = true
  ; selectorConclusionPostulated = false
  }
