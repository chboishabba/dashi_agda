module DASHI.Physics.Gravity.KSW668BraneBulkRationalNullComparatorExact where

------------------------------------------------------------------------
-- KSW/KK/brane bulk shortcut rational null-path benchmark.
--
-- ORIGINAL SCIENTIFIC SOURCE:
-- Robert R. Caldwell and David Langlois,
-- "Shortcuts in the fifth dimension", Physics Letters B 511 (2001)
-- 129-135, DOI 10.1016/S0370-2693(01)00631-1.
--
-- This lemma is OUR simpler *piecewise linear, non-smooth test-brane*
-- geometric discriminator, NOT their AdS cosmological Einstein solution.
--
-- 5D ambient Minkowski metric in t,X,Y,u,v, signature (-++++):
--   two brane segments (X,Y):
--      A=(0,0) -> M=(3,4) -> B=(6,0).
--   each segment spatial length=5 (3^2+4^2=5^2).
--   brane-confined null path duration=5+5=10 (c=1).
--   ambient straight null chord duration=6.
--   both endpoints are the SAME A,B on the SAME embedded brane.
--   shortcut saves 4 ambient time-units without locally superluminal
--   motion, because embedded intrinsic distance exceeds the chord.
--
-- The source's smooth cylindrical brane, induced metric, extrinsic
-- curvature, and static-warp no-shortcut are symbolically checked by
-- scripts/ksw668_brane_bulk_shortcut_same_metric.py, NOT this Agda Nat
-- module. Dynamical brane stress, Israel junction, signal/receiver and
-- experiment remain OPEN. No CTC or physical FTL is inferred.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

firstLegNullPythagoras :
  3 * 3 + 4 * 4 ≡ 5 * 5
firstLegNullPythagoras = refl

secondLegNullPythagoras :
  3 * 3 + 4 * 4 ≡ 5 * 5
secondLegNullPythagoras = refl

branelightTravel : Nat
branelightTravel = 5 + 5

bulkNullChordTravel : Nat
bulkNullChordTravel = 3 + 3

sameSourceDestinationCoordinate :
  3 + 3 ≡ 6
sameSourceDestinationCoordinate = refl

braneTimeIsTen : branelightTravel ≡ 10
braneTimeIsTen = refl

bulkTimeIsSix : bulkNullChordTravel ≡ 6
bulkTimeIsSix = refl

ambientNullArrivalSavesFour :
  bulkNullChordTravel + 4 ≡ branelightTravel
ambientNullArrivalSavesFour = refl

noIntrinsicAmbientEqualLengthHere :
  branelightTravel ≡ bulkNullChordTravel → ⊥
noIntrinsicAmbientEqualLengthHere ()

-- The null right-triangle witnesses apply to the ambient metric,
-- NOT to Euclidean distances treated as spacetime intervals.

sourceNullFirstLegDurationSquared :
  5 * 5 ≡ 3 * 3 + 4 * 4
sourceNullFirstLegDurationSquared = refl

sourceNullChordDurationSquared :
  6 * 6 ≡ (3 + 3) * (3 + 3)
sourceNullChordDurationSquared = refl

-- No proof here claims this kinked brane is a stationary Nambu-Goto
-- or Israel-Einstein solution. That is the next, genuinely physical cut.
