module DASHI.Physics.YangMills.BalabanP0PhysicalReducedGhostFiniteLogTailWeldExact where

-- PAID P0.2 subgate: exact original anchored reduced FP source
-- matrix R_A, its signed degree-5 matrix log tail, AND the
-- shifted-tail geometric decay are all certified simultaneously.
--
-- Reuses the actual 765-dimensional reduced ghost carrier and its
-- physical anchored row-mass contraction <= 104601/524288 < 1/5.
-- Signed fifth log tail uniformly <= 1/2500 for every finite cutoff.
-- Shifted terms uniformly <= (1/5)^m / 2500, and the trace of
-- the signed tail has the exact source recursion.
--
-- This is a TRUE producer from the selected physical reduced matrix
-- rather than a generic uninhabited remainder interface.
--
-- REMAINS OPEN: that actual Bishop background path equals the finite
-- rational fourth-order jet with O(g^5) remainder; representation
-- of the completed finite log series as principal log det; Fourier
-- one-loop momentum measure and beta tensor match.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (_*_; _-_)
import DASHI.Physics.YangMills.BalabanFiniteRationalMatrixTraceCyclicExact as Matrix
import DASHI.Physics.YangMills.BalabanReducedGhostAnchoredRelativeContractionExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanReducedGhostNeumannRowContractionExact as Neumann
import DASHI.Physics.YangMills.BalabanReducedGhostMatrixLogFifthTailExact as Tail
import DASHI.Physics.YangMills.BalabanReducedGhostPhysicalMatrixLogFifthTailExact as PhysicalTail
import DASHI.Physics.YangMills.BalabanReducedGhostSignedMatrixLogTailExact as Signed
import DASHI.Physics.YangMills.BalabanReducedGhostMatrixLogShiftedTailExact as Shifted
import DASHI.Physics.YangMills.BalabanReducedGhostSignedTraceTailExact as SignedTrace

physicalSignedAndShiftedFifthTails :
  ∀ background →
  Relaxed.RelaxedInverseLinkRadius background →
  ∀ anchor (coefficients : Tail.LogTailCoefficients) exponent start length →
  (Neumann.UniformRowBound
    Physical.gaugeRows
    (Signed.signedFifthTail Physical.gaugeRows
      (Physical.anchoredRelativeKernel background anchor)
      coefficients exponent)
    Tail.fifthTailCap)
  ×
  (Neumann.UniformRowBound
    Physical.gaugeRows
    (Shifted.shiftedFifthTail Physical.gaugeRows
      (Physical.anchoredRelativeKernel background anchor)
      coefficients start length)
    (Shifted.shiftedCap start))
physicalSignedAndShiftedFifthTails
  background radius anchor coefficients exponent start length =
  (Signed.signedFifthTailUniformCap
     Physical.gaugeRows
     (Physical.anchoredRelativeKernel background anchor)
     coefficients exponent
     (PhysicalTail.physicalAnchoredRelativeRowsBelowOneFifth
       background radius anchor))
  ,
  (Shifted.physicalReducedGhostShiftedTailCap
     background radius anchor coefficients start length)

physicalSignedTraceTailOneStep :
  ∀ background anchor (coefficients : Tail.LogTailCoefficients) exponent →
  SignedTrace.signedTailTrace
    Physical.gaugeRows
    (Physical.anchoredRelativeKernel background anchor)
    coefficients (suc exponent)
  ≡
    Tail.coefficient coefficients zero *
      Matrix.matrixTrace Physical.gaugeRows
        (Tail.fifthPower
          Physical.gaugeRows
          (Physical.anchoredRelativeKernel background anchor))
    -
      Matrix.matrixTrace Physical.gaugeRows
        (Matrix.matrixProduct Physical.gaugeRows
          (Physical.anchoredRelativeKernel background anchor)
          (Signed.signedFifthTail
            Physical.gaugeRows
            (Physical.anchoredRelativeKernel background anchor)
            (Tail.shiftCoefficients coefficients) exponent))
physicalSignedTraceTailOneStep background anchor coefficients exponent =
  SignedTrace.signedTailTraceSucExact
    Physical.gaugeRows
    (Physical.anchoredRelativeKernel background anchor)
    coefficients exponent

-- The finite-tail and trace identities are fully source-produced
-- under the genuine RelativeInverseLinkRadius of the native carrier.
-- They do not warrant marking physicalReducedGhostBishopFifthOrderRemainderLevel
-- as kernel accepted: physical Bishop path, matrix functional calculus
-- and background-to-momentum identification remain independent.
