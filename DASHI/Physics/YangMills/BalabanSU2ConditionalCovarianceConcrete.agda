module DASHI.Physics.YangMills.BalabanSU2ConditionalCovarianceConcrete where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.BalabanFiniteOneStepCore using
  (FiniteHessianCertificate; FiniteCovarianceCertificate; hessian;
   covariance; covarianceLeft; covarianceRight)

conditionalCovariance :
  ∀ {Vector Scalar}
  {hessianData : FiniteHessianCertificate Vector Scalar} →
  FiniteCovarianceCertificate hessianData → Vector → Vector
conditionalCovariance = covariance

conditionalCovarianceLeftInverse :
  ∀ {Vector Scalar}
  {hessianData : FiniteHessianCertificate Vector Scalar}
  (data : FiniteCovarianceCertificate hessianData) →
  ∀ vector → conditionalCovariance data (hessian hessianData vector) ≡ vector
conditionalCovarianceLeftInverse = covarianceLeft

conditionalCovarianceRightInverse :
  ∀ {Vector Scalar}
  {hessianData : FiniteHessianCertificate Vector Scalar}
  (data : FiniteCovarianceCertificate hessianData) →
  ∀ vector → hessian hessianData (conditionalCovariance data vector) ≡ vector
conditionalCovarianceRightInverse = covarianceRight
