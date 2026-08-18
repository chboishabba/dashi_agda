module DASHI.Moonshine.DuncanOnoMonsterSupersingularStandardAuthority where

------------------------------------------------------------------------
-- STANDARD IMPORTED MOONSHINE / SUPERSINGULAR AUTHORITY
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- SOURCE ROLE
-- Duncan--Ono state Ogg's coincidence in the form:
--
--   a prime p divides the order of the Monster
--     iff
--   all supersingular j-invariants in characteristic p are defined over F_p.
--
-- Their paper then relates the supersingular sets to order-p McKay--Thompson
-- functions.  DASHI imports only the prime-divisor / supersingular-rationality
-- equivalence here.
--
-- IMPORTANT AUTHORITY BOUNDARY
-- * Monster membership is Nat divisibility of the actual published group order
--   from MonsterOrderDivisibilityExact, not the repository's SSP15 lane table.
-- * The geometric right-hand side is the ACTUAL prime-pinned coarse Frobenius
--   carrier from PublishedPrimeLevelFrickeSelectorPinnedExact.
-- * The genus-zero equivalence is NOT postulated here; it is derived later from
--   the independent Deligne--Rapoport/Fricke theorem chain.
-- * p=2,3 are kept outside this particular bridge because the published
--   prime-level Fricke authority currently has the explicit hypothesis p>=5.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke

postulate
  duncanOnoMonsterPrimeIffCoarseSupersingularFullyFixed :
    (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
    Monster.PrimeDividesMonsterOrder p
    ↔ Fricke.PublishedFrobeniusFullyFixed p prime ge5

record DuncanOnoMonsterSupersingularStandardAuthorityBoundary : Set where
  field
    duncanOnoEquivalenceImported : Bool
    actualMonsterOrderDivisibilityUsed : Bool
    actualCoarseFrobeniusCarrierUsed : Bool
    finiteMonsterPrimeLaneTableUsed : Bool
    frickeGenusZeroPostulated : Bool
    primesTwoAndThreeHandledHere : Bool

canonicalDuncanOnoMonsterSupersingularStandardAuthorityBoundary :
  DuncanOnoMonsterSupersingularStandardAuthorityBoundary
canonicalDuncanOnoMonsterSupersingularStandardAuthorityBoundary = record
  { duncanOnoEquivalenceImported = true
  ; actualMonsterOrderDivisibilityUsed = true
  ; actualCoarseFrobeniusCarrierUsed = true
  ; finiteMonsterPrimeLaneTableUsed = false
  ; frickeGenusZeroPostulated = false
  ; primesTwoAndThreeHandledHere = false
  }
