module DASHI.Physics.YangMills.BalabanReducedGhostSignedTraceTailExact where

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
-- Ph. Boucaud, J. P. Leroy, A. Le Yaouanc, J. Micheli, O. Pene and
-- J. Rodriguez-Quintero,
-- "Large momentum behavior of the ghost propagator in SU(3) lattice gauge
-- theory with Wilson action", Physical Review D 72 (2005), 114503.
-- DOI: 10.1103/PhysRevD.72.114503.
--
-- SOURCE ROLE BOUNDARY
--
-- Boucaud et al. supply lattice-gauge precedent for constructing/computing the
-- discretized Faddeev-Popov operator and ghost propagator.  The exact finite
-- trace-log algebra below is instead justified internally plus Higham/Horn-
-- Johnson functional calculus; no numerical lattice-QCD computation is used as
-- a determinant identity.
--
-- DASHI CONTRIBUTION
--
-- Close the finite same-object seam between the signed matrix-log tail and its
-- trace.  The Round61 tail is an actual alternating matrix recursion, not an
-- unsigned majorant.  Finite trace linearity therefore gives exactly
--
--   tr(c_0 R^5) = c_0 tr(R^5),
--
--   tr(T_{N+1})
--     = c_0 tr(R^5) - tr(R T_N(shift c)).
--
-- This is the algebraic representation needed before constructive completion.
-- No determinant identity or infinite-dimensional Fredholm machinery is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; _-_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteRationalMatrixTraceCyclicExact as Matrix
import DASHI.Physics.YangMills.BalabanReducedGhostNeumannRowContractionExact as Neumann
import DASHI.Physics.YangMills.BalabanReducedGhostMatrixLogFifthTailExact as Tail
import DASHI.Physics.YangMills.BalabanReducedGhostSignedMatrixLogTailExact as Signed

matrixTraceScaleExact :
  ∀ {Index : Set} (indices : List Index) scalar
    (matrix : Matrix.Matrix Index) →
  Matrix.matrixTrace indices (Neumann.scaleMatrix scalar matrix)
  ≡ scalar * Matrix.matrixTrace indices matrix
matrixTraceScaleExact indices scalar matrix =
  Sums.sumRationalScale scalar indices (λ index → matrix index index)

matrixTraceSubtractExact :
  ∀ {Index : Set} (indices : List Index)
    (left right : Matrix.Matrix Index) →
  Matrix.matrixTrace indices (Signed.matrixSubtract left right)
  ≡ Matrix.matrixTrace indices left - Matrix.matrixTrace indices right
matrixTraceSubtractExact indices left right =
  Fubini.sumRationalSubtract indices
    (λ index → left index index)
    (λ index → right index index)

signedTailTrace :
  ∀ {Index : Set} →
  List Index → Matrix.Matrix Index → Tail.LogTailCoefficients → Nat → ℚ
signedTailTrace indices matrix coefficients exponent =
  Matrix.matrixTrace indices
    (Signed.signedFifthTail indices matrix coefficients exponent)

signedTailTraceZeroExact :
  ∀ {Index : Set} (indices : List Index)
    (matrix : Matrix.Matrix Index)
    (coefficients : Tail.LogTailCoefficients) →
  signedTailTrace indices matrix coefficients zero
  ≡ Tail.coefficient coefficients zero
      * Matrix.matrixTrace indices (Tail.fifthPower indices matrix)
signedTailTraceZeroExact indices matrix coefficients =
  matrixTraceScaleExact indices
    (Tail.coefficient coefficients zero)
    (Tail.fifthPower indices matrix)

signedTailTraceSucExact :
  ∀ {Index : Set} (indices : List Index)
    (matrix : Matrix.Matrix Index)
    (coefficients : Tail.LogTailCoefficients) exponent →
  signedTailTrace indices matrix coefficients (suc exponent)
  ≡ Tail.coefficient coefficients zero
      * Matrix.matrixTrace indices (Tail.fifthPower indices matrix)
    - Matrix.matrixTrace indices
        (Matrix.matrixProduct indices matrix
          (Signed.signedFifthTail
            indices matrix (Tail.shiftCoefficients coefficients) exponent))
signedTailTraceSucExact indices matrix coefficients exponent =
  trans
    (matrixTraceSubtractExact indices
      (Neumann.scaleMatrix
        (Tail.coefficient coefficients zero) (Tail.fifthPower indices matrix))
      (Matrix.matrixProduct indices matrix
        (Signed.signedFifthTail
          indices matrix (Tail.shiftCoefficients coefficients) exponent)))
    (cong
      (λ first →
        first - Matrix.matrixTrace indices
          (Matrix.matrixProduct indices matrix
            (Signed.signedFifthTail
              indices matrix (Tail.shiftCoefficients coefficients) exponent)))
      (matrixTraceScaleExact indices
        (Tail.coefficient coefficients zero) (Tail.fifthPower indices matrix)))

reducedGhostFiniteTraceLinearityLevel : ProofLevel
reducedGhostFiniteTraceLinearityLevel = machineChecked

reducedGhostSignedFiniteTraceTailIdentityLevel : ProofLevel
reducedGhostSignedFiniteTraceTailIdentityLevel = machineChecked
