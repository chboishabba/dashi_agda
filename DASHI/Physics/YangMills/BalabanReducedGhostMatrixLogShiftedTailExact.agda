module DASHI.Physics.YangMills.BalabanReducedGhostMatrixLogShiftedTailExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Nicholas J. Higham,
-- "Functions of Matrices: Theory and Computation", SIAM, 2008.
-- DOI: 10.1137/1.9780898717778.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- DASHI CONTRIBUTION
--
-- Round61 already proves on the SAME literal anchored reduced ghost kernel R
--
--     rowMass(R) <= 1/5
--
-- and bounds every finite degree-five-and-higher log tail by 1/2500.
-- Uniform boundedness is not yet a constructive convergence statement.  This
-- file strengthens it to an explicit shifted-tail modulus.
--
-- If Tail_0 is any finite degree >=5 log tail with coefficients in [0,1],
-- define recursively
--
--     Tail_(m+1)(c) = R Tail_m(shift c).
--
-- Tail_m therefore starts m powers later.  Row-mass submultiplicativity gives
--
--     rowMass(Tail_m)
--       <= (1/5)^m * [(1/5)^5 sum_{j=0}^N (1/5)^j]
--       <= (1/5)^m / 2500.
--
-- This is the finite Cauchy modulus needed before passing the matrix-log
-- partial sums to a constructive limit: arbitrarily late finite tails are
-- uniformly geometrically small.  No infinite-series completion, determinant
-- identity, or physical continuum limit is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanFiniteRationalMatrixTraceCyclicExact as Matrix
import DASHI.Physics.YangMills.BalabanReducedGhostNeumannRowContractionExact as Neumann
import DASHI.Physics.YangMills.BalabanReducedGhostMatrixLogFifthTailExact as Tail
import DASHI.Physics.YangMills.BalabanReducedGhostPhysicalMatrixLogFifthTailExact as PhysicalTail
import DASHI.Physics.YangMills.BalabanReducedGhostAnchoredRelativeContractionExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

------------------------------------------------------------------------
-- A degree shift is literal left multiplication by R together with shifting
-- the coefficient stream.  Starting at zero recovers the existing fifth tail.
------------------------------------------------------------------------

shiftedFifthTail :
  ∀ {Index : Set} →
  List Index → Matrix.Matrix Index → Tail.LogTailCoefficients →
  Nat → Nat → Matrix.Matrix Index
shiftedFifthTail indices matrix coefficients zero length =
  Tail.finiteFifthTail indices matrix coefficients length
shiftedFifthTail indices matrix coefficients (suc start) length =
  Matrix.matrixProduct indices matrix
    (shiftedFifthTail indices matrix (Tail.shiftCoefficients coefficients) start length)

startFactor : Nat → ℚ
startFactor start = Neumann.rationalPower Tail.oneFifth start

shiftedMajorant : Nat → Nat → ℚ
shiftedMajorant start length =
  startFactor start * Tail.geometricMajorant length

shiftedCap : Nat → ℚ
shiftedCap start = startFactor start * Tail.fifthTailCap

startFactorNonnegative : ∀ start → 0ℚ ≤ startFactor start
startFactorNonnegative start =
  Neumann.powerNonnegative Tail.oneFifth start Tail.oneFifthNonnegative

shiftedMajorantNonnegative : ∀ start length →
  0ℚ ≤ shiftedMajorant start length
shiftedMajorantNonnegative start length =
  let
    leftNN = startFactorNonnegative start
    rightNN = Tail.geometricMajorantNonnegative length
  in
  ℚP.nonNegative⁻¹ (shiftedMajorant start length)

------------------------------------------------------------------------
-- Exact geometric row bound for every shifted finite tail.
------------------------------------------------------------------------

shiftedFifthTailRowBound :
  ∀ {Index : Set}
    (indices : List Index)
    (matrix : Matrix.Matrix Index)
    (coefficients : Tail.LogTailCoefficients)
    start length →
  Neumann.UniformRowBound indices matrix Tail.oneFifth →
  Neumann.UniformRowBound indices
    (shiftedFifthTail indices matrix coefficients start length)
    (shiftedMajorant start length)
shiftedFifthTailRowBound
    indices matrix coefficients zero length matrixRows =
  Tail.finiteFifthTailRowBound indices matrix coefficients length matrixRows
shiftedFifthTailRowBound
    indices matrix coefficients (suc start) length matrixRows row =
  let
    rest = shiftedFifthTail
      indices matrix (Tail.shiftCoefficients coefficients) start length

    restRows :
      Neumann.UniformRowBound indices rest (shiftedMajorant start length)
    restRows = shiftedFifthTailRowBound
      indices matrix (Tail.shiftCoefficients coefficients) start length matrixRows

    productRows :
      Neumann.UniformRowBound indices
        (Matrix.matrixProduct indices matrix rest)
        (Tail.oneFifth * shiftedMajorant start length)
    productRows =
      Neumann.productRowMassBound
        indices matrix rest
        Tail.oneFifth (shiftedMajorant start length)
        (shiftedMajorantNonnegative start length)
        matrixRows restRows
  in
  productRows row

------------------------------------------------------------------------
-- The existing 1/2500 fifth-tail cap scales by exactly (1/5)^m.
------------------------------------------------------------------------

shiftedMajorantBelowCap : ∀ start length →
  shiftedMajorant start length ≤ shiftedCap start
shiftedMajorantBelowCap start length =
  Norm.scaleNonnegative
    (startFactor start)
    (startFactorNonnegative start)
    (Tail.geometricMajorantBelowFifthTailCap length)

shiftedFifthTailUniformCap :
  ∀ {Index : Set}
    (indices : List Index)
    (matrix : Matrix.Matrix Index)
    (coefficients : Tail.LogTailCoefficients)
    start length →
  Neumann.UniformRowBound indices matrix Tail.oneFifth →
  Neumann.UniformRowBound indices
    (shiftedFifthTail indices matrix coefficients start length)
    (shiftedCap start)
shiftedFifthTailUniformCap
    indices matrix coefficients start length matrixRows row =
  ℚP.≤-trans
    (shiftedFifthTailRowBound
      indices matrix coefficients start length matrixRows row)
    (shiftedMajorantBelowCap start length)

------------------------------------------------------------------------
-- Source-native physical specialization: the SAME anchored reduced FP kernel
-- from Round61 inherits the geometric shifted-tail modulus.
------------------------------------------------------------------------

physicalReducedGhostShiftedTailCap :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ anchor (coefficients : Tail.LogTailCoefficients) start length →
  Neumann.UniformRowBound
    Physical.gaugeRows
    (shiftedFifthTail
      Physical.gaugeRows
      (Physical.anchoredRelativeKernel background anchor)
      coefficients start length)
    (shiftedCap start)
physicalReducedGhostShiftedTailCap
    background radius anchor coefficients start length =
  shiftedFifthTailUniformCap
    Physical.gaugeRows
    (Physical.anchoredRelativeKernel background anchor)
    coefficients start length
    (PhysicalTail.physicalAnchoredRelativeRowsBelowOneFifth
      background radius anchor)

shiftedCapStep : ∀ start →
  shiftedCap (suc start) ≡ Tail.oneFifth * shiftedCap start
shiftedCapStep start = refl

reducedGhostShiftedMatrixLogTailLevel : ProofLevel
reducedGhostShiftedMatrixLogTailLevel = machineChecked

physicalReducedGhostConstructiveCauchyMajorantLevel : ProofLevel
physicalReducedGhostConstructiveCauchyMajorantLevel = machineChecked

-- What remains for a literal log-det identity is now a representation theorem:
-- map these finite matrix-log partial sums into the repository's complete
-- Bishop-real matrix/function carrier and identify its constructive limit with
-- the principal matrix logarithm / reduced determinant ratio.  The finite
-- Cauchy modulus itself is no longer an analytic producer.
