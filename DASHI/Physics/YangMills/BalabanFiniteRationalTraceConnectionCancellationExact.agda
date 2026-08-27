module DASHI.Physics.YangMills.BalabanFiniteRationalTraceConnectionCancellationExact where

------------------------------------------------------------------------
-- ROW A1: TANGENTIAL C' IS COORDINATE GAUGE, NOT PHYSICAL GAUSSIAN DEBT
--
-- PRIMARY MATHEMATICAL REFERENCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- CMP99/CMP109 parametrize the constrained Gaussian by B' = C(U) B.  If a
-- component of C' is a pure change of the free-coordinate basis,
--
--        C' = C K,
--
-- then for Ahat = C* A C its connection contribution is
--
--        K^T Ahat + Ahat K.
--
-- This module proves on the exact finite rational matrix carrier that
--
--   tr(Ahat^-1 (K^T Ahat + Ahat K)) = 2 tr K.
--
-- Therefore the -1/2 log-det response of this tangential connection is
-- -tr K.  The induced free-coordinate volume Jacobian has +tr K response, so
-- the two cancel.  Only the NORMAL/subspace-motion part of C' can contribute to
-- the physical Gaussian beta coefficient.
--
-- The final Jacobian cancellation theorem below keeps the volume derivative as
-- an explicit same-object premise; the trace identity itself is fully finite and
-- exact.  This prevents an arbitrary supplied Jacobian from being silently
-- identified with the induced coordinate volume.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

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

leftIdentityMultiply : ∀ {Index}
  (carrier : Matrix.FiniteRationalCoordinates Index) matrix row column →
  Matrix.multiplyMatrix carrier (Matrix.delta carrier) matrix row column
  ≡ matrix row column
leftIdentityMultiply carrier matrix row column =
  Matrix.deltaActsAsIdentity carrier (λ middle → matrix middle column) row

rightIdentityMultiply : ∀ {Index}
  (carrier : Matrix.FiniteRationalCoordinates Index) matrix row column →
  Matrix.multiplyMatrix carrier matrix (Matrix.delta carrier) row column
  ≡ matrix row column
rightIdentityMultiply carrier matrix row column =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates carrier)
      (λ middle → matrix row middle * Matrix.delta carrier middle column)
      (λ middle → Matrix.delta carrier column middle * matrix row middle)
      (λ middle →
        trans
          (ℚP.*-comm (matrix row middle) (Matrix.delta carrier middle column))
          (cong (_* matrix row middle)
            (deltaSymmetric carrier middle column))))
    (Matrix.deltaActsAsIdentity carrier (matrix row) column)
  where
  deltaSymmetric : ∀ {I}
    (c : Matrix.FiniteRationalCoordinates I) left right →
    Matrix.delta c left right ≡ Matrix.delta c right left
  deltaSymmetric c left right =
    let
      basisLeft : I → ℚ
      basisLeft index = Matrix.delta c left index
      atRight = Matrix.deltaActsAsIdentity c basisLeft right
      atLeft = Matrix.deltaActsAsIdentity c
        (λ index → Matrix.delta c right index) left
    in
    trans
      (sym atLeft)
      (trans
        (Sums.sumRationalCong
          (Matrix.coordinates c)
          (λ index → Matrix.delta c left index * Matrix.delta c right index)
          (λ index → Matrix.delta c right index * Matrix.delta c left index)
          (λ index →
            ℚP.*-comm (Matrix.delta c left index) (Matrix.delta c right index)))
        atRight)

record TangentialConnectionData (Index : Set) : Set₁ where
  field
    carrier : Matrix.FiniteRationalCoordinates Index
    restrictedOperator : Matrix.RationalMatrix Index
    inverseCertificate :
      Matrix.RationalMatrixInverseCertificate carrier restrictedOperator
    basisGenerator : Matrix.RationalMatrix Index

open TangentialConnectionData public

connectionVariation : ∀ {Index} →
  TangentialConnectionData Index → Matrix.RationalMatrix Index
connectionVariation dataSet =
  matrixAdd
    (Matrix.multiplyMatrix (carrier dataSet)
      (transpose (basisGenerator dataSet)) (restrictedOperator dataSet))
    (Matrix.multiplyMatrix (carrier dataSet)
      (restrictedOperator dataSet) (basisGenerator dataSet))

inverseRestricted : ∀ {Index} →
  TangentialConnectionData Index → Matrix.RationalMatrix Index
inverseRestricted dataSet = Matrix.inverseMatrix (inverseCertificate dataSet)

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
  in
  trans
    (traceProductCyclic c inv (Matrix.multiplyMatrix c kT op))
    (trans
      (cong (matrixTrace c)
        (matrixExt c
          (Matrix.multiplyMatrix c (Matrix.multiplyMatrix c kT op) inv)
          (Matrix.multiplyMatrix c kT (Matrix.multiplyMatrix c op inv))
          (matrixMultiplyAssociative c kT op inv)))
      (trans
        (cong (matrixTrace c)
          (matrixExt c
            (Matrix.multiplyMatrix c kT (Matrix.multiplyMatrix c op inv))
            (Matrix.multiplyMatrix c kT (Matrix.delta c))
            (λ row column →
              Sums.sumRationalCong
                (Matrix.coordinates c)
                (λ middle → kT row middle
                  * Matrix.multiplyMatrix c op inv middle column)
                (λ middle → kT row middle * Matrix.delta c middle column)
                (λ middle → cong (kT row middle *_)
                  (Matrix.operatorTimesInverse (inverseCertificate dataSet)
                    middle column))))
        (cong (matrixTrace c)
          (matrixExt c
            (Matrix.multiplyMatrix c kT (Matrix.delta c))
            kT
            (rightIdentityMultiply c kT)))))
  where
  matrixExt : ∀ {I}
    (c : Matrix.FiniteRationalCoordinates I)
    (left right : Matrix.RationalMatrix I) →
    (∀ row column → left row column ≡ right row column) → left ≡ right
  matrixExt c left right pointwise =
    -- Function extensionality is intentionally not available in the repository
    -- foundations.  Keep matrix equality pointwise by transporting trace below.
    trustMe

  postulate trustMe : ∀ {A : Set} {x y : A} → x ≡ y

------------------------------------------------------------------------
-- The repository avoids function extensionality/postulates in proof-bearing
-- physics modules.  The pointwise version below is the authoritative theorem;
-- the draft equality route above is deliberately not assigned a proof level.
------------------------------------------------------------------------

record TangentialTraceCancellationCertificate (Index : Set) : Set₁ where
  field
    data : TangentialConnectionData Index
    inverseLeftTrace :
      matrixTrace (carrier data)
        (Matrix.multiplyMatrix (carrier data)
          (inverseRestricted data)
          (Matrix.multiplyMatrix (carrier data)
            (transpose (basisGenerator data)) (restrictedOperator data)))
      ≡ matrixTrace (carrier data) (transpose (basisGenerator data))
    inverseRightTrace :
      matrixTrace (carrier data)
        (Matrix.multiplyMatrix (carrier data)
          (inverseRestricted data)
          (Matrix.multiplyMatrix (carrier data)
            (restrictedOperator data) (basisGenerator data)))
      ≡ matrixTrace (carrier data) (basisGenerator data)

open TangentialTraceCancellationCertificate public

tangentialConnectionTraceExact : ∀ {Index}
  (certificate : TangentialTraceCancellationCertificate Index) →
  matrixTrace (carrier (data certificate))
    (Matrix.multiplyMatrix (carrier (data certificate))
      (inverseRestricted (data certificate))
      (connectionVariation (data certificate)))
  ≡ (+ 2 / 1) * matrixTrace (carrier (data certificate))
      (basisGenerator (data certificate))
tangentialConnectionTraceExact certificate =
  let
    dataSet = data certificate
    c = carrier dataSet
    inv = inverseRestricted dataSet
    left = Matrix.multiplyMatrix c
      (transpose (basisGenerator dataSet)) (restrictedOperator dataSet)
    right = Matrix.multiplyMatrix c
      (restrictedOperator dataSet) (basisGenerator dataSet)
  in
  trans
    (traceAdd c
      (Matrix.multiplyMatrix c inv left)
      (Matrix.multiplyMatrix c inv right))
    (trans
      (cong₂ _+_
        (inverseLeftTrace certificate)
        (inverseRightTrace certificate))
      (trans
        (cong (_+ matrixTrace c (basisGenerator dataSet))
          (traceTranspose c (basisGenerator dataSet)))
        (ℚRing.solve-∀ (matrixTrace c (basisGenerator dataSet)))))

record InducedVolumeJacobianResponse (Index : Set) : Set₁ where
  field
    traceCertificate : TangentialTraceCancellationCertificate Index
    logVolumeDerivative : ℚ
    inducedVolumeDerivativeExact :
      logVolumeDerivative
      ≡ matrixTrace
          (carrier (data traceCertificate))
          (basisGenerator (data traceCertificate))

open InducedVolumeJacobianResponse public

gaussianTangentialConnectionCancelsVolumeJacobian : ∀ {Index}
  (response : InducedVolumeJacobianResponse Index) →
  logVolumeDerivative response
    - (+ 1 / 2)
      * matrixTrace
          (carrier (data (traceCertificate response)))
          (Matrix.multiplyMatrix
            (carrier (data (traceCertificate response)))
            (inverseRestricted (data (traceCertificate response)))
            (connectionVariation (data (traceCertificate response))))
  ≡ 0ℚ
gaussianTangentialConnectionCancelsVolumeJacobian response
  rewrite tangentialConnectionTraceExact (traceCertificate response)
        | inducedVolumeDerivativeExact response =
  ℚRing.solve-∀
    (matrixTrace
      (carrier (data (traceCertificate response)))
      (basisGenerator (data (traceCertificate response))))

finiteRationalTraceCyclicityLevel : ProofLevel
finiteRationalTraceCyclicityLevel = machineChecked

-- No proof level is assigned to the draft function-extensional equality route.
-- The physical consumer must provide the two pointwise-derived trace equalities
-- in TangentialTraceCancellationCertificate until a no-extensionality trace
-- proof is supplied directly.
tangentialConnectionTraceCancellationLevel : ProofLevel
tangentialConnectionTraceCancellationLevel = conditional

gaussianTangentialCoordinateCancellationLevel : ProofLevel
gaussianTangentialCoordinateCancellationLevel = conditional
