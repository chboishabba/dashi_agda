module DASHI.Education.DigitalESDTransformativePrincipleMatrixRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDTransformativePrincipleMatrixExact as Matrix

matrixRowCountRegression : Matrix.transformativePrincipleMatrixRowCount ≡ 7
matrixRowCountRegression = refl

aliceAndSustainabilitySourcesSeparatedRegression :
  Matrix.TransformativePrincipleMatrixBoundary.aliceAndSustainabilitySourceRolesSeparated
    Matrix.canonicalTransformativePrincipleMatrixBoundary
  ≡ true
aliceAndSustainabilitySourcesSeparatedRegression = refl

matrixCandidateOnlyRegression :
  Matrix.TransformativePrincipleMatrixBoundary.matrixCandidateOnly
    Matrix.canonicalTransformativePrincipleMatrixBoundary
  ≡ true
matrixCandidateOnlyRegression = refl

matrixDoesNotCreateEmpiricalEffectRegression :
  Matrix.PrincipleConstraintPairCreatesEmpiricalDigitalESDEffect → ⊥
matrixDoesNotCreateEmpiricalEffectRegression =
  Matrix.principleConstraintPairDoesNotCreateEmpiricalDigitalESDEffect

sustainabilityEvidenceNotRetrofitToAliceRegression :
  Matrix.SustainabilityEvidenceBecomesAliceSourceFinding → ⊥
sustainabilityEvidenceNotRetrofitToAliceRegression =
  Matrix.sustainabilityEvidenceDoesNotBecomeAliceSourceFinding

custodianshipRetainsLifecycleConstraintRegression :
  Matrix.PrincipleConstraintRow.candidateOnly
    Matrix.contextualCustodianshipConstraintRow
  ≡ true
custodianshipRetainsLifecycleConstraintRegression = refl
