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
  (bundle : FiniteCovarianceCertificate hessianData) →
  ∀ vector → conditionalCovariance bundle (hessian hessianData vector) ≡ vector
conditionalCovarianceLeftInverse = covarianceLeft

conditionalCovarianceRightInverse :
  ∀ {Vector Scalar}
  {hessianData : FiniteHessianCertificate Vector Scalar}
  (bundle : FiniteCovarianceCertificate hessianData) →
  ∀ vector → hessian hessianData (conditionalCovariance bundle vector) ≡ vector
conditionalCovarianceRightInverse = covarianceRight
