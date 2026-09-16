module DASHI.Education.DigitalESDPreScreenCandidateSourceScopeMatrixRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDPreScreenCandidateSourceScopeMatrixExact as Matrix

candidateCountRegression : Matrix.candidateSourceCount ≡ 8
candidateCountRegression = refl

allRowsRemainCandidateRegression :
  Matrix.SourceScopeMatrixBoundary.allRowsCandidateOnly
    Matrix.canonicalSourceScopeMatrixBoundary
  ≡ true
allRowsRemainCandidateRegression = refl

matrixDoesNotCreateInclusionRegression :
  Matrix.PreScreenMatrixCreatesIncludedCorpus → ⊥
matrixDoesNotCreateInclusionRegression = Matrix.preScreenMatrixDoesNotCreateIncludedCorpus

matrixDoesNotCloseSearchRegression :
  Matrix.PreScreenMatrixClosesStructuredSearch → ⊥
matrixDoesNotCloseSearchRegression = Matrix.preScreenMatrixDoesNotCloseStructuredSearch

l1410RemainsMethodOnlyRegression :
  Matrix.CandidateSourceScopeRow.candidateOnly Matrix.ituL1410Candidate ≡ true
l1410RemainsMethodOnlyRegression = refl

ministerialRemainsGovernanceRegression :
  Matrix.CandidateSourceScopeRow.candidateOnly Matrix.unescoAICommonGoodCandidate ≡ true
ministerialRemainsGovernanceRegression = refl

midtermRetainsGlobalProgrammeScopeRegression :
  Matrix.CandidateSourceScopeRow.candidateOnly Matrix.unescoMidtermCandidate ≡ true
midtermRetainsGlobalProgrammeScopeRegression = refl
