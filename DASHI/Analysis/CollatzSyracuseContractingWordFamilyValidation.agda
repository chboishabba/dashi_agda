module DASHI.Analysis.CollatzSyracuseContractingWordFamilyValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseContractingWordFamilyExact as Family

canonicalThresholdPaid :
  Family.ContractingWordFamilyBoundary.canonicalCorrectionPlusOneThresholdPaid
    Family.canonicalContractingWordFamilyBoundary
  ≡ 1
canonicalThresholdPaid = refl

uniformFamilyPaid :
  Family.ContractingWordFamilyBoundary.everyContractingWordGetsUniformCertificate
    Family.canonicalContractingWordFamilyBoundary
  ≡ 1
uniformFamilyPaid = refl

universalTailStillOpen :
  Family.ContractingWordFamilyBoundary.contractingWordFamilyAutomaticallyCoversEveryResidualStart
    Family.canonicalContractingWordFamilyBoundary
  ≡ 0
universalTailStillOpen = refl
