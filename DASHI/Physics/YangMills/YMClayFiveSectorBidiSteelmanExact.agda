{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayFiveSectorBidiSteelmanExact where

-- GOLDEN FINITE CORE OF THE 2/3/4E/(3,1)/5 DIMENSIONAL BIDI STEELMAN.
--
-- (1) Exact ten-plane-to-six-plane-to-three-plane-to-one-plane
--     curvature-accounting on a nonnegative finite coefficient carrier.
--     Each reduction preserves the lower-dimensional terms but leaves
--     the cross-fibre terms explicitly visible.
-- (2) The only way the normalized parent sum can equal its projected
--     sum is for the discarded nonnegative cross-fibre sum to vanish.
-- (3) An actual nonzero cross-fibre fixture refutes naive equality.
-- (4) Conditional matched-observable transport composes, but requires
--     selected sector-specific comparison proofs.
-- (5) The physical 3+1 result is re-used from the existing same-metric
--     TSFV/KK certificate, never constructed from a dimension tag.
--
-- This finite counting is NOT a proof of continuous compact Haar,
-- Yang--Mills continuum existence, OS reconstruction, KK truncation,
-- stochastic 3D equilibrium, antigravity, or a Clay mass gap.
--
-- REUSE/PROVENANCE:
-- DASHI native six-plane YM/plaquette and source-normalized Wilson owners
-- (especially the Voyager PR #1444 and Route-S PR #1440);
-- DASHI TSFVKKSameMetricTransportExact (Lorentz PR #1460);
-- DASHI YMClayVoyagerDimensionSignatureForkExact.
-- Original continuum YM, KK, OS, Balaban and 2D/3D results remain
-- attributed to their authors in Docs/physics.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Empty using (⊥)

import DASHI.Physics.YangMills.YMClayVoyagerDimensionSignatureForkExact as Dim
import DASHI.Physics.Foundations.Lorentz31DirectionalProbeExact as Lorentz
import DASHI.Physics.Foundations.TSFVKKSameMetricTransportExact as SameMetric

------------------------------------------------------------------------
-- A dimensionally nested finite gauge-curvature accounting experiment.
--
-- Axes 0,1,2,3,4 are labels for EUCLIDEAN directions of a five-axis
-- test. "2D/3D/4D" below means selecting its first 2/3/4 axes.
-- This is NOT the selected 5D KK spacetime/action or physical Wick map.
-- Each coefficient can stand for a nonnegative local Wilson deficit,
-- subject to an independent actual-source interpretation.
------------------------------------------------------------------------

record TenPlaneWeights : Set where
  constructor tenPlaneWeights
  field
    f01 f02 f03 f04 : Nat
    f12 f13 f14 : Nat
    f23 f24 f34 : Nat

open TenPlaneWeights public

twoPlane : TenPlaneWeights → Nat
twoPlane w = f01 w

threeCross : TenPlaneWeights → Nat
threeCross w = f02 w + f12 w

threePlane : TenPlaneWeights → Nat
threePlane w = twoPlane w + threeCross w

fourCross : TenPlaneWeights → Nat
fourCross w = (f03 w + f13 w) + f23 w

fourPlane : TenPlaneWeights → Nat
fourPlane w = threePlane w + fourCross w

fiveCross : TenPlaneWeights → Nat
fiveCross w = ((f04 w + f14 w) + f24 w) + f34 w

fivePlane : TenPlaneWeights → Nat
fivePlane w = fourPlane w + fiveCross w

threeToTwoExact :
  (w : TenPlaneWeights) →
  threePlane w ≡ twoPlane w + threeCross w
threeToTwoExact w = refl

fourToThreeExact :
  (w : TenPlaneWeights) →
  fourPlane w ≡ threePlane w + fourCross w
fourToThreeExact w = refl

fiveToFourExact :
  (w : TenPlaneWeights) →
  fivePlane w ≡ fourPlane w + fiveCross w
fiveToFourExact w = refl

------------------------------------------------------------------------
-- Actual algebraic obstruction, without assuming a missing scalar away.
-- A+cross=A forces cross=0 on this nonnegative Nat carrier.
------------------------------------------------------------------------

predNat : Nat → Nat
predNat zero = zero
predNat (suc n) = n

sumEqualsBaseForcesZeroCross :
  (base cross : Nat) →
  base + cross ≡ base →
  cross ≡ zero
sumEqualsBaseForcesZeroCross zero cross same = same
sumEqualsBaseForcesZeroCross (suc base) cross same =
  sumEqualsBaseForcesZeroCross base cross (cong predNat same)

fiveMatchesFourForcesCrossZero :
  (w : TenPlaneWeights) →
  fivePlane w ≡ fourPlane w →
  fiveCross w ≡ zero
fiveMatchesFourForcesCrossZero w same =
  sumEqualsBaseForcesZeroCross (fourPlane w) (fiveCross w) same

fourMatchesThreeForcesCrossZero :
  (w : TenPlaneWeights) →
  fourPlane w ≡ threePlane w →
  fourCross w ≡ zero
fourMatchesThreeForcesCrossZero w same =
  sumEqualsBaseForcesZeroCross (threePlane w) (fourCross w) same

threeMatchesTwoForcesCrossZero :
  (w : TenPlaneWeights) →
  threePlane w ≡ twoPlane w →
  threeCross w ≡ zero
threeMatchesTwoForcesCrossZero w same =
  sumEqualsBaseForcesZeroCross (twoPlane w) (threeCross w) same

-- One nonzero 5D fifth-axis curvature coefficient, all others zero.
-- Every 2D/3D/4D projection has zero, while the five-axis sum is one.
fiveFibreCounterexample : TenPlaneWeights
fiveFibreCounterexample =
  tenPlaneWeights
    zero zero zero (suc zero)
    zero zero zero
    zero zero zero

fiveCounterexampleProjectedFourZero :
  fourPlane fiveFibreCounterexample ≡ zero
fiveCounterexampleProjectedFourZero = refl

fiveCounterexampleFullOne :
  fivePlane fiveFibreCounterexample ≡ suc zero
fiveCounterexampleFullOne = refl

fiveDoesNotAutomaticallyMatchFour :
  fivePlane fiveFibreCounterexample
    ≡ fourPlane fiveFibreCounterexample →
  ⊥
fiveDoesNotAutomaticallyMatchFour ()

------------------------------------------------------------------------
-- Sector-indexed BIDI. The observer matches only the chosen states.
-- No equality between arbitrary 2D, 3D, 4D, 5D observables is assumed.
-- This is a proof that independently warranted adjacent matches compose,
-- not a claim those physical matches have been supplied.
------------------------------------------------------------------------

record MatchedEuclideanGaugeTower : Set₁ where
  field
    State5 State4 State3 State2 Observable : Set
    selected5 : State5
    reduce54 : State5 → State4
    reduce43 : State4 → State3
    reduce32 : State3 → State2
    read5 : State5 → Observable
    read4 : State4 → Observable
    read3 : State3 → Observable
    read2 : State2 → Observable

    matched54 :
      read5 selected5 ≡ read4 (reduce54 selected5)
    matched43 :
      read4 (reduce54 selected5)
      ≡ read3 (reduce43 (reduce54 selected5))
    matched32 :
      read3 (reduce43 (reduce54 selected5))
      ≡ read2 (reduce32 (reduce43 (reduce54 selected5)))

open MatchedEuclideanGaugeTower public

matchedFiveToTwo :
  (tower : MatchedEuclideanGaugeTower) →
  read5 tower (selected5 tower)
  ≡ read2 tower
      (reduce32 tower
        (reduce43 tower (reduce54 tower (selected5 tower))))
matchedFiveToTwo tower =
  trans (matched54 tower)
    (trans (matched43 tower) (matched32 tower))

-- The selected physical Lorentz metric is NOT a Euclidean dimension
-- reduction. Import its conditional original time-arrow metric theorem
-- from the already selected KK/TSFV same-source witness.
selectedLorentzian31FromSameMetric :
  (w : SameMetric.SameMetricTSFVKK) →
  Lorentz.actualAxisCounts
    (DASHI.Physics.YangMills.YMClayLorentz31DirectionalKKHodgeExact.SameSourceKKYMContinuation.signatureSigns
       (SameMetric.kkSource w))
  ≡ Lorentz.signature 3 1
selectedLorentzian31FromSameMetric =
  SameMetric.sameMetricKKSignatureFromTSFV

-- Dimension-coupling classifications remain the Voyager source's data.
fourDimensionalCouplingIsMarginal :
  Dim.ymTwiceCouplingDimension Dim.four ≡ Dim.zero
fourDimensionalCouplingIsMarginal = Dim.fourDimensionalMarginal

fiveDimensionalGaugeLatticeIsNotKK :
  Dim.creutzFiveEuclideanLattice ≡ Dim.kkFourLorentzPlusCircle → ⊥
fiveDimensionalGaugeLatticeIsNotKK = Dim.creutzIsNotKK
