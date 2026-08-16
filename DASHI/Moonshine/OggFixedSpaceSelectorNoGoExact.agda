module DASHI.Moonshine.OggFixedSpaceSelectorNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires", Seminaire Delange-Pisot-Poitou,
-- 1974/75, exp. 7.  No DOI assigned.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Turn the first representation-reduction control collision into a no-go
-- theorem.  Any proposed Ogg selector that factors only through the pair
--
--   (dim V_j^C2, dim V_j^C3)
--
-- receives the same input at j=4 (dimension 9, non-Ogg control) and j=5
-- (dimension 11, Ogg).  It therefore cannot output different classifications
-- at those two dimensions.
--
-- This is deliberately a negative theorem: it rules out a too-small proposed
-- invariant and forces the downstream search toward richer branching spectra.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Moonshine.SO3CyclicFixedSpaceScanExact as Scan

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

FixedPairSelector : Set
FixedPairSelector = (Nat × Nat) → Bool

fixedPairSelectorCannotSeparateNineAndEleven :
  (selector : FixedPairSelector) →
  selector (Scan.fixedPair 4) ≡ false →
  selector (Scan.fixedPair 5) ≡ true →
  ⊥
fixedPairSelectorCannotSeparateNineAndEleven selector class9 class11 =
  falseNotTrue
    (trans
      (sym class9)
      (trans
        (cong selector Scan.j4AndJ5FixedPairsCoincide)
        class11))

------------------------------------------------------------------------
-- Benchmark labels are kept outside the representation producer.  They are
-- test labels, not premises of fixedPair or the SO(3) scan.
------------------------------------------------------------------------

dimension9ExpectedOggStatus : Bool
dimension9ExpectedOggStatus = false

dimension11ExpectedOggStatus : Bool
dimension11ExpectedOggStatus = true

expectedStatusesDiffer :
  dimension9ExpectedOggStatus ≡ dimension11ExpectedOggStatus → ⊥
expectedStatusesDiffer ()
