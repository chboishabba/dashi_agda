module DASHI.Physics.YangMills.BalabanReducedGhostOperatorMatrixExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Nicholas J. Higham,
-- "Functions of Matrices: Theory and Computation", SIAM, 2008.
-- DOI: 10.1137/1.9780898717778.
--
-- DASHI CONTRIBUTION
--
-- Turn an actual reduced ghost operator into its concrete coordinate matrix on
-- the 3 x 256 redundant-labelled basis from
-- `BalabanReducedGhostExplicitTraceCarrierExact`.  The three anchor labels are
-- zero basis vectors, so this is an executable representation of the genuine
-- 3 x 255 = 765 reduced carrier.
--
-- The matrix trace over the Cartesian coordinate list is proved equal to the
-- direct reduced ghost trace.  This is the same-object bridge needed to feed
-- physical ghost Taylor coefficients into the finite matrix trace-log jet.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Product; pair; map; _++_; cartesian)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as Gauge
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanFiniteRationalMatrixTraceCyclicExact as Matrix
import DASHI.Physics.YangMills.BalabanReducedGhostExplicitTraceCarrierExact as Trace

sumAppend :
  ∀ {A : Set} (left right : List A) (term : A → ℚ) →
  Sums.sumRational (left ++ right) term
  ≡ Sums.sumRational left term + Sums.sumRational right term
sumAppend [] right term = refl
sumAppend (value ∷ values) right term
  rewrite sumAppend values right term = refl

sumMap :
  ∀ {A B : Set} (function : A → B) (values : List A) (term : B → ℚ) →
  Sums.sumRational (map function values) term
  ≡ Sums.sumRational values (λ value → term (function value))
sumMap function [] term = refl
sumMap function (value ∷ values) term
  rewrite sumMap function values term = refl

sumCartesian :
  ∀ {A B : Set} (left : List A) (right : List B)
    (term : Product A B → ℚ) →
  Sums.sumRational (cartesian left right) term
  ≡ Sums.sumRational left
      (λ first → Sums.sumRational right (λ second → term (pair first second)))
sumCartesian [] right term = refl
sumCartesian (value ∷ values) right term =
  trans
    (sumAppend
      (map (λ second → pair value second) right)
      (cartesian values right) term)
    (trans
      (cong₂ _+_
        (sumMap (λ second → pair value second) right term)
        (sumCartesian values right term))
      refl)

basisFromCoordinate :
  Block.PhysicalBlockL Path4.side4 →
  Gauge.GaugeCoordinate4 → Gauge.GaugeCoordinate4 → ℚ
basisFromCoordinate anchor (pair colour site) =
  Trace.reducedGhostBasisSource anchor colour site

reducedGhostOperatorMatrix :
  Block.PhysicalBlockL Path4.side4 →
  Trace.GhostLinearMap → Matrix.Matrix Gauge.GaugeCoordinate4
reducedGhostOperatorMatrix anchor operator row column =
  operator (basisFromCoordinate anchor column) row

reducedGhostMatrixTraceEqualsDirectTrace :
  ∀ anchor operator →
  Matrix.matrixTrace Gauge.flatGaugeCoordinates
    (reducedGhostOperatorMatrix anchor operator)
  ≡ Trace.reducedGhostTrace anchor operator
reducedGhostMatrixTraceEqualsDirectTrace anchor operator =
  sumCartesian
    Coordinates.lieCoordinates3
    (Block.physicalBlockSites Path4.side4)
    (λ coordinate →
      reducedGhostOperatorMatrix anchor operator coordinate coordinate)

reducedGhostOperatorMatrixLevel : ProofLevel
reducedGhostOperatorMatrixLevel = machineChecked

reducedGhostMatrixTraceSameObjectLevel : ProofLevel
reducedGhostMatrixTraceSameObjectLevel = machineChecked
