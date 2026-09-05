module DASHI.Analysis.NonArchimedeanUniformBranchProbabilitySourceExact where

------------------------------------------------------------------------
-- UNIFORM BRANCH PROBABILITY SOURCE RECEIPT
--
-- External source head audited:
--   sneed-and-feed/adelic-spectral-zeta
--   f94b956e6e970c40c8bb9f9c39e9052ad7a5f884
--
-- CollatzRelMatrix.lean defines D_n(x,y)=1 iff y=3x or y=3x-1 and states that
-- the matrix is {0,1}-valued with no edge multiplicities. L2Mixing.lean defines
-- the random-walk transition matrix P_n=(1/2) D_n.
--
-- Therefore the binary branch-word model used by the constructive stopping
-- proof has the correct source probability semantics: each length-m branch word
-- carries weight 2^{-m}. This does not resurrect any refuted L2 or survival
-- rate; it only identifies the finite counting measure with the source Markov
-- branch measure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record UniformBranchProbabilitySourceReceipt : Set where
  constructor uniformBranchProbabilitySourceReceipt
  field
    sourceCommit : String
    directedMatrixIsZeroOneValued : Bool
    directedMatrixHasNoEdgeMultiplicities : Bool
    branchAIsThreeX : Bool
    branchBIsThreeXMinusOne : Bool
    normalizedMatrixIsHalfDirectedMatrix : Bool
    finiteBinaryWordsMatchMarkovBranchChoices : Bool
    allLengthMWordsEquiprobable : Bool
    universalInverseSqrtTwoTailRecovered : Bool

canonicalUniformBranchProbabilitySourceReceipt :
  UniformBranchProbabilitySourceReceipt
canonicalUniformBranchProbabilitySourceReceipt =
  uniformBranchProbabilitySourceReceipt
    "f94b956e6e970c40c8bb9f9c39e9052ad7a5f884"
    true true true true true true true false

uniformBranchProbabilitySourceOwned :
  UniformBranchProbabilitySourceReceipt.allLengthMWordsEquiprobable
    canonicalUniformBranchProbabilitySourceReceipt
  ≡ true
uniformBranchProbabilitySourceOwned = refl

falseUniversalTailNotRecovered :
  UniformBranchProbabilitySourceReceipt.universalInverseSqrtTwoTailRecovered
    canonicalUniformBranchProbabilitySourceReceipt
  ≡ false
falseUniversalTailNotRecovered = refl
