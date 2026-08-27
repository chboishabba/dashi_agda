module DASHI.Physics.YangMills.BalabanFiniteRationalTraceConnectionCancellationExact where

------------------------------------------------------------------------
-- ROW A1: TANGENTIAL C' IS COORDINATE GAUGE, NOT PHYSICAL GAUSSIAN DEBT
--
-- PRIMARY MATHEMATICAL REFERENCE
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- PHYSICAL SOURCE
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- For the constrained-coordinate Gaussian B' = C(U)B, a pure free-coordinate
-- basis motion C' = C K gives
--
--      D(C*AC)|tangent = K^T Ahat + Ahat K,
--      Ahat = C*AC.
--
-- On the exact finite rational matrix carrier this file proves, without
-- function extensionality or postulates,
--
--   tr(Ahat^-1 (K^T Ahat + Ahat K)) = 2 tr K.
--
-- Therefore the -1/2 log-determinant response is -tr K.  If the accompanying
-- coordinate-volume Jacobian is the induced one, its logarithmic derivative is
-- +tr K and the tangential terms cancel exactly.  Only normal motion of the
-- constrained subspace can remain in the physical Gaussian beta coefficient.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini

transpose : ∀ {Index} → Matrix.RationalMatrix Index → Matrix.RationalMatrix Index
transpose matrix row column = matrix column row

matrixAdd : ∀ {Index} →
  Matrix.RationalMatrix Index → Matrix.RationalMatrix Index →
  Matrix.RationalMatrix Index
matrixAdd left right row column = left row column + right row column

matrixTrace : ∀ {Index} →
  Matrix.FiniteRationalCoordinates Index → Matrix.RationalMatrix Index → ℚ
matrixTrace carrier matrix =
  Sums.sumRational (Matrix.coordinates carrier) (λ index → matrix index index)

traceCong : ∀ {Index}
  (carrier : Matrix.FiniteRationalCoordinates Index)
  (left right : Matrix.RationalMatrix Index) →
  (∀ row column → left row column ≡ right row column) →
  matrixTrace carrier left ≡ matrixTrace carrier right
traceCong carrier left right pointwise =
  Sums.sumRationalCong
    (Matrix.coordinates carrier)
    (λ index → left index index)
    (λ index → right index index)
    (λ index → pointwise index index)

traceAdd : ∀ {Index}
  (carrier : Matrix.FiniteRationalCoordinates Index) left right →
  matrixTrace carrier (matrixAdd left right)
  ≡ matrixTrace carrier left + matrixTrace carrier right
traceAdd carrier left right =
  Sums.sumRationalAdd
    (Matrix.coordinates carrier)
    (λ index → left index index)
    (λ index → right index index)

traceTranspose : ∀ {Index}
  (carrier : Matrix.FiniteRationalCoordinates Index) matrix →
  matrixTrace carrier (transpose matrix) ≡ matrixTrace carrier matrix
traceTranspose carrier matrix = refl

traceProductCyclic : ∀ {Index}
  (carrier : Matrix.FiniteRationalCoordinates Index) left right →
  matrixTrace carrier (Matrix.multiplyMatrix carrier left right)
  ≡ matrixTrace carrier (Matrix.multiplyMatrix carrier right left)
traceProductCyclic carrier left right =
  trans
    (Fubini.sumSwap
      (Matrix.coordinates carrier)
      (Matrix.coordinates carrier)
      (λ row column → left row column * right column row))
    (Sums.sumRationalCong
      (Matrix.coordinates carrier)
      (λ column →
        Sums.sumRational (Matrix.coordinates carrier)
          (λ row → left row column * right column row))
      (λ column →
        Sums.sumRational (Matrix.coordinates carrier)
          (λ row → right column row * left row column))
      (λ column →
        Sums.sumRationalCong
          (Matrix.coordinates carrier)
          (λ row → left row column * right column row)
          (λ row → right column row * left row column)
          (λ row → ℚP.*-comm (left row column) (right column row))))

matrixMultiplyAssociative : ∀ {Index}
  (carrier : Matrix.FiniteRationalCoordinates Index) first second third row column →
  Matrix.multiplyMatrix carrier
    (Matrix.multiplyMatrix carrier first second) third row column
  ≡ Matrix.multiplyMatrix carrier
      first (Matrix.multiplyMatrix carrier second third) row column
matrixMultiplyAssociative carrier first second third row column =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates carrier)
      (λ middleRight →
        Sums.sumRational (Matrix.coordinates carrier)
          (λ middleLeft → first row middleLeft * second middleLeft middleRight)
        * third middleRight column)
      (λ middleRight →
        Sums.sumRational (Matrix.coordinates carrier)
          (λ middleLeft →
            (first row middleLeft * second middleLeft middleRight)
              * third middleRight column))
      (λ middleRight →
        sym
          (Matrix.sumRationalRightScale
            (Matrix.coordinates carrier)
            (λ middleLeft → first row middleLeft * second middleLeft middleRight)
            (third middleRight column))))
    (trans
      (Fubini.sumSwap
        (Matrix.coordinates carrier)
        (Matrix.coordinates carrier)
        (λ middleRight middleLeft →
          (first row middleLeft * second middleLeft middleRight)
            * third middleRight column))
      (Sums.sumRationalCong
        (Matrix.coordinates carrier)
        (λ middleLeft →
          Sums.sumRational (Matrix.coordinates carrier)
            (λ middleRight →
              (first row middleLeft * second middleLeft middleRight)
                * third middleRight column))
        (λ middleLeft →
          first row middleLeft
            * Sums.sumRational (Matrix.coordinates carrier)
                (λ middleRight →
                  second middleLeft middleRight * third middleRight column))
        (λ middleLeft →
          trans
            (Sums.sumRationalCong
              (Matrix.coordinates carrier)
              (λ middleRight →
                (first row middleLeft * second middleLeft middleRight)
                  * third middleRight column)
              (λ middleRight →
                first row middleLeft
                  * (second middleLeft middleRight * third middleRight column))
              (λ middleRight →
                ℚP.*-assoc
                  (first row middleLeft)
                  (second middleLeft middleRight)
                  (third middleRight column)))
            (Sums.sumRationalScale
              (first row middleLeft)
              (Matrix.coordinates carrier)
              (λ middleRight →
                second middleLeft middleRight * third middleRight column))))))

traceMultiplyAssociative : ∀ {Index}
  (carrier : Matrix.FiniteRationalCoordinates Index) first second third →
  matrixTrace carrier
    (Matrix.multiplyMatrix carrier
      (Matrix.multiplyMatrix carrier first second) third)
  ≡ matrixTrace carrier
      (Matrix.multiplyMatrix carrier
        first (Matrix.multiplyMatrix carrier second third))
traceMultiplyAssociative carrier first second third =
  traceCong carrier _ _ (matrixMultiplyAssociative carrier first second third)

multiplyLeftCong : ∀ {Index}
  (carrier : Matrix.FiniteRationalCoordinates Index)
  left right multiplier →
  (∀ row column → left row column ≡ right row column) →
  ∀ row column →
  Matrix.multiplyMatrix carrier left multiplier row column
  ≡ Matrix.multiplyMatrix carrier right multiplier row column
multiplyLeftCong carrier left right multiplier pointwise row column =
  Sums.sumRationalCong
    (Matrix.coordinates carrier)
    (λ middle → left row middle * multiplier middle column)
    (λ middle → right row middle * multiplier middle column)
    (λ middle → cong (_* multiplier middle column) (pointwise row middle))

multiplyRightCong : ∀ {Index}
  (carrier : Matrix.FiniteRationalCoordinates Index)
  multiplier left right →
  (∀ row column → left row column ≡ right row column) →
  ∀ row column →
  Matrix.multiplyMatrix carrier multiplier left row column
  ≡ Matrix.multiplyMatrix carrier multiplier right row column
multiplyRightCong carrier multiplier left right pointwise row column =
  Sums.sumRationalCong
    (Matrix.coordinates carrier)
    (λ middle → multiplier row middle * left middle column)
    (λ middle → multiplier row middle * right middle column)
    (λ middle → cong (multiplier row middle *_) (pointwise middle column))

traceLeftIdentity : ∀ {Index}
  (carrier : Matrix.FiniteRationalCoordinates Index) matrix →
  matrixTrace carrier
    (Matrix.multiplyMatrix carrier (Matrix.delta carrier) matrix)
  ≡ matrixTrace carrier matrix
traceLeftIdentity carrier matrix =
  traceCong carrier _ matrix
    (λ row column →
      Matrix.deltaActsAsIdentity carrier (λ middle → matrix middle column) row)

traceRightIdentity : ∀ {Index}
  (carrier : Matrix.FiniteRationalCoordinates Index) matrix →
  matrixTrace carrier
    (Matrix.multiplyMatrix carrier matrix (Matrix.delta carrier))
  ≡ matrixTrace carrier matrix
traceRightIdentity carrier matrix =
  trans
    (traceProductCyclic carrier matrix (Matrix.delta carrier))
    (traceLeftIdentity carrier matrix)

record TangentialConnectionData (Index : Set) : Set₁ where
  field
    carrier : Matrix.FiniteRationalCoordinates Index
    restrictedOperator : Matrix.RationalMatrix Index
    inverseCertificate :
      Matrix.RationalMatrixInverseCertificate carrier restrictedOperator
    basisGenerator : Matrix.RationalMatrix Index

open TangentialConnectionData public

inverseRestricted : ∀ {Index} →
  TangentialConnectionData Index → Matrix.RationalMatrix Index
inverseRestricted dataSet = Matrix.inverseMatrix (inverseCertificate dataSet)

connectionVariation : ∀ {Index} →
  TangentialConnectionData Index → Matrix.RationalMatrix Index
connectionVariation dataSet =
  matrixAdd
    (Matrix.multiplyMatrix (carrier dataSet)
      (transpose (basisGenerator dataSet)) (restrictedOperator dataSet))
    (Matrix.multiplyMatrix (carrier dataSet)
      (restrictedOperator dataSet) (basisGenerator dataSet))

traceInverseTimesLeftConnection : ∀ {Index}
  (dataSet : TangentialConnectionData Index) →
  matrixTrace (carrier dataSet)
    (Matrix.multiplyMatrix (carrier dataSet)
      (inverseRestricted dataSet)
      (Matrix.multiplyMatrix (carrier dataSet)
        (transpose (basisGenerator dataSet)) (restrictedOperator dataSet)))
  ≡ matrixTrace (carrier dataSet) (transpose (basisGenerator dataSet))
traceInverseTimesLeftConnection dataSet =
  let
    c = carrier dataSet
    inv = inverseRestricted dataSet
    op = restrictedOperator dataSet
    kT = transpose (basisGenerator dataSet)
    cert = inverseCertificate dataSet
  in
  trans
    (traceProductCyclic c inv (Matrix.multiplyMatrix c kT op))
    (trans
      (traceMultiplyAssociative c kT op inv)
      (trans
        (traceCong c _ _
          (multiplyRightCong c kT
            (Matrix.multiplyMatrix c op inv)
            (Matrix.delta c)
            (Matrix.operatorTimesInverse cert)))
        (traceRightIdentity c kT)))

traceInverseTimesRightConnection : ∀ {Index}
  (dataSet : TangentialConnectionData Index) →
  matrixTrace (carrier dataSet)
    (Matrix.multiplyMatrix (carrier dataSet)
      (inverseRestricted dataSet)
      (Matrix.multiplyMatrix (carrier dataSet)
        (restrictedOperator dataSet) (basisGenerator dataSet)))
  ≡ matrixTrace (carrier dataSet) (basisGenerator dataSet)
traceInverseTimesRightConnection dataSet =
  let
    c = carrier dataSet
    inv = inverseRestricted dataSet
    op = restrictedOperator dataSet
    k = basisGenerator dataSet
    cert = inverseCertificate dataSet
  in
  trans
    (sym (traceMultiplyAssociative c inv op k))
    (trans
      (traceCong c _ _
        (multiplyLeftCong c
          (Matrix.multiplyMatrix c inv op)
          (Matrix.delta c)
          k
          (Matrix.inverseTimesOperator cert)))
      (traceLeftIdentity c k))

tangentialConnectionTraceExact : ∀ {Index}
  (dataSet : TangentialConnectionData Index) →
  matrixTrace (carrier dataSet)
    (Matrix.multiplyMatrix (carrier dataSet)
      (inverseRestricted dataSet)
      (connectionVariation dataSet))
  ≡ (+ 2 / 1) * matrixTrace (carrier dataSet) (basisGenerator dataSet)
tangentialConnectionTraceExact dataSet =
  let
    c = carrier dataSet
    inv = inverseRestricted dataSet
    left = Matrix.multiplyMatrix c
      (transpose (basisGenerator dataSet)) (restrictedOperator dataSet)
    right = Matrix.multiplyMatrix c
      (restrictedOperator dataSet) (basisGenerator dataSet)
  in
  trans
    (traceCong c _ _
      (λ row column →
        Sums.sumRationalAdd
          (Matrix.coordinates c)
          (λ middle → inv row middle * left middle column)
          (λ middle → inv row middle * right middle column)))
    (trans
      (traceAdd c
        (Matrix.multiplyMatrix c inv left)
        (Matrix.multiplyMatrix c inv right))
      (trans
        (cong₂ _+_
          (traceInverseTimesLeftConnection dataSet)
          (traceInverseTimesRightConnection dataSet))
        (trans
          (cong (_+ matrixTrace c (basisGenerator dataSet))
            (traceTranspose c (basisGenerator dataSet)))
          (ℚRing.solve-∀ (matrixTrace c (basisGenerator dataSet))))))

record InducedVolumeJacobianResponse (Index : Set) : Set₁ where
  field
    connection : TangentialConnectionData Index
    logVolumeDerivative : ℚ
    inducedVolumeDerivativeExact :
      logVolumeDerivative
      ≡ matrixTrace (carrier connection) (basisGenerator connection)

open InducedVolumeJacobianResponse public

gaussianTangentialConnectionCancelsVolumeJacobian : ∀ {Index}
  (response : InducedVolumeJacobianResponse Index) →
  logVolumeDerivative response
    - (+ 1 / 2)
      * matrixTrace
          (carrier (connection response))
          (Matrix.multiplyMatrix
            (carrier (connection response))
            (inverseRestricted (connection response))
            (connectionVariation (connection response)))
  ≡ 0ℚ
gaussianTangentialConnectionCancelsVolumeJacobian response
  rewrite tangentialConnectionTraceExact (connection response)
        | inducedVolumeDerivativeExact response =
  ℚRing.solve-∀
    (matrixTrace
      (carrier (connection response))
      (basisGenerator (connection response)))

finiteRationalTraceCyclicityLevel : ProofLevel
finiteRationalTraceCyclicityLevel = machineChecked

tangentialConnectionTraceCancellationLevel : ProofLevel
tangentialConnectionTraceCancellationLevel = machineChecked

-- Physical same-object seam: prove that the change-of-variables density in the
-- literal CMP99/CMP109 Gaussian is exactly the induced coordinate-volume
-- Jacobian whose logarithmic derivative is tr K for the tangential component.
gaussianTangentialCoordinateCancellationLevel : ProofLevel
gaussianTangentialCoordinateCancellationLevel = conditional
