module DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitSummedIntervalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud,
-- "Introduction to Interval Analysis", SIAM, 2009.
-- DOI: 10.1137/1.9780898717716.
--
-- DASHI CONTRIBUTION
--
-- Preserve cancellations at orbit level.  Instead of forcing each of the 240
-- regular cells to carry a separately useful lower bound, fold an arbitrary
-- rational cell contribution into the four exact geometric orbit buckets
-- proved in BalabanClayT4HypercubicOrbitGeometryExact.
--
-- The theorem below is an exact finite identity:
--
--   sum_(240 regular cells) f(B)
--     = S_1(f) + S_2(f) + S_3(f) + S_4(f),
--
-- where S_m is the joint sum over cells with exactly m outer coordinates.
-- Interval arithmetic may therefore enclose S_m AS A WHOLE, retaining any
-- cancellation internal to the orbit, before the four certified lower bounds
-- are combined.  No one-loop positivity or per-cell sign hypothesis occurs in
-- this finite reduction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Orbit
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

record FiveOrbitSums : Set where
  constructor orbitSums
  field
    infraredSum oneOuterSum twoOuterSum threeOuterSum fourOuterSum : ℚ
open FiveOrbitSums public

zeroOrbitSums : FiveOrbitSums
zeroOrbitSums = orbitSums 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ

insertOrbitValue : Orbit.OrbitClass → ℚ → FiveOrbitSums → FiveOrbitSums
insertOrbitValue Orbit.infrared value sums =
  orbitSums
    (value + infraredSum sums)
    (oneOuterSum sums)
    (twoOuterSum sums)
    (threeOuterSum sums)
    (fourOuterSum sums)
insertOrbitValue Orbit.oneOuter value sums =
  orbitSums
    (infraredSum sums)
    (value + oneOuterSum sums)
    (twoOuterSum sums)
    (threeOuterSum sums)
    (fourOuterSum sums)
insertOrbitValue Orbit.twoOuter value sums =
  orbitSums
    (infraredSum sums)
    (oneOuterSum sums)
    (value + twoOuterSum sums)
    (threeOuterSum sums)
    (fourOuterSum sums)
insertOrbitValue Orbit.threeOuter value sums =
  orbitSums
    (infraredSum sums)
    (oneOuterSum sums)
    (twoOuterSum sums)
    (value + threeOuterSum sums)
    (fourOuterSum sums)
insertOrbitValue Orbit.fourOuter value sums =
  orbitSums
    (infraredSum sums)
    (oneOuterSum sums)
    (twoOuterSum sums)
    (threeOuterSum sums)
    (value + fourOuterSum sums)

bucketTotal : FiveOrbitSums → ℚ
bucketTotal sums =
  infraredSum sums
  + oneOuterSum sums
  + twoOuterSum sums
  + threeOuterSum sums
  + fourOuterSum sums

regularBucketTotal : FiveOrbitSums → ℚ
regularBucketTotal sums =
  oneOuterSum sums
  + twoOuterSum sums
  + threeOuterSum sums
  + fourOuterSum sums

insertOrbitValuePreservesTotal :
  ∀ orbit value sums →
  bucketTotal (insertOrbitValue orbit value sums)
  ≡ value + bucketTotal sums
insertOrbitValuePreservesTotal Orbit.infrared value sums =
  ℚRing.solve-∀ value
    (infraredSum sums) (oneOuterSum sums) (twoOuterSum sums)
    (threeOuterSum sums) (fourOuterSum sums)
insertOrbitValuePreservesTotal Orbit.oneOuter value sums =
  ℚRing.solve-∀ value
    (infraredSum sums) (oneOuterSum sums) (twoOuterSum sums)
    (threeOuterSum sums) (fourOuterSum sums)
insertOrbitValuePreservesTotal Orbit.twoOuter value sums =
  ℚRing.solve-∀ value
    (infraredSum sums) (oneOuterSum sums) (twoOuterSum sums)
    (threeOuterSum sums) (fourOuterSum sums)
insertOrbitValuePreservesTotal Orbit.threeOuter value sums =
  ℚRing.solve-∀ value
    (infraredSum sums) (oneOuterSum sums) (twoOuterSum sums)
    (threeOuterSum sums) (fourOuterSum sums)
insertOrbitValuePreservesTotal Orbit.fourOuter value sums =
  ℚRing.solve-∀ value
    (infraredSum sums) (oneOuterSum sums) (twoOuterSum sums)
    (threeOuterSum sums) (fourOuterSum sums)

foldOrbitSums :
  List Grid.GridCell4 → (Grid.GridCell4 → ℚ) → FiveOrbitSums
foldOrbitSums [] contribution = zeroOrbitSums
foldOrbitSums (cell ∷ cells) contribution =
  insertOrbitValue (Orbit.orbitClass cell) (contribution cell)
    (foldOrbitSums cells contribution)

sumEqualsOrbitBucketTotal :
  ∀ cells contribution →
  Sums.sumRational cells contribution
  ≡ bucketTotal (foldOrbitSums cells contribution)
sumEqualsOrbitBucketTotal [] contribution = refl
sumEqualsOrbitBucketTotal (cell ∷ cells) contribution =
  trans
    (cong (contribution cell +_)
      (sumEqualsOrbitBucketTotal cells contribution))
    (sym
      (insertOrbitValuePreservesTotal
        (Orbit.orbitClass cell)
        (contribution cell)
        (foldOrbitSums cells contribution)))

regularOrbitSums :
  (Grid.GridCell4 → ℚ) → FiveOrbitSums
regularOrbitSums contribution =
  foldOrbitSums Grid.regularGridCells contribution

regularGridHasNoInfraredBucket :
  ∀ contribution →
  infraredSum (regularOrbitSums contribution) ≡ 0ℚ
regularGridHasNoInfraredBucket contribution = refl

bucketTotalWithoutInfrared :
  ∀ sums →
  infraredSum sums ≡ 0ℚ →
  bucketTotal sums ≡ regularBucketTotal sums
bucketTotalWithoutInfrared sums infraredZero
  rewrite infraredZero =
  ℚRing.solve-∀
    (oneOuterSum sums) (twoOuterSum sums)
    (threeOuterSum sums) (fourOuterSum sums)

regularCellSumEqualsFourOrbitSums :
  ∀ contribution →
  Sums.sumRational Grid.regularGridCells contribution
  ≡ regularBucketTotal (regularOrbitSums contribution)
regularCellSumEqualsFourOrbitSums contribution =
  trans
    (sumEqualsOrbitBucketTotal Grid.regularGridCells contribution)
    (bucketTotalWithoutInfrared
      (regularOrbitSums contribution)
      (regularGridHasNoInfraredBucket contribution))

-- Source-facing names for the four joint quantities that the physical interval
-- evaluator should enclose.  These are sums, not representative-box receipts.
oneOuterOrbitSum twoOuterOrbitSum threeOuterOrbitSum fourOuterOrbitSum :
  (Grid.GridCell4 → ℚ) → ℚ
oneOuterOrbitSum contribution = oneOuterSum (regularOrbitSums contribution)
twoOuterOrbitSum contribution = twoOuterSum (regularOrbitSums contribution)
threeOuterOrbitSum contribution = threeOuterSum (regularOrbitSums contribution)
fourOuterOrbitSum contribution = fourOuterSum (regularOrbitSums contribution)

regularCellSumAsFourJointOrbitSums :
  ∀ contribution →
  Sums.sumRational Grid.regularGridCells contribution
  ≡ oneOuterOrbitSum contribution
    + twoOuterOrbitSum contribution
    + threeOuterOrbitSum contribution
    + fourOuterOrbitSum contribution
regularCellSumAsFourJointOrbitSums = regularCellSumEqualsFourOrbitSums

orbitSummedFiniteRepartitionLevel : ProofLevel
orbitSummedFiniteRepartitionLevel = machineChecked

orbitSummedCancellationPreservationLevel : ProofLevel
orbitSummedCancellationPreservationLevel = machineChecked

-- The remaining physical theorem is to construct the actual Wilson/ghost/Haar
-- contribution function (or, better, the four joint orbit expressions) and
-- enclose these four sums in Bishop/rational interval semantics.
literalWilsonGhostHaarOrbitExpressionInputsLevel : ProofLevel
literalWilsonGhostHaarOrbitExpressionInputsLevel = conditional
