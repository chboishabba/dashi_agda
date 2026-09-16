module DASHI.Education.DigitalESDColladoAnalysisSetRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Education.DigitalESDColladoAnalysisSetExact as Sets
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling

immediateSetNRegression :
  Sets.Analysis.AnalysisSetReceipt.analysisN Sets.colladoImmediateSet
  ≡ Ceiling.derivedNatWithSameObjectReceipt 257
      "120 experimental + 137 control complete T0/T1 cases"
      "same-object arithmetic from Participants and procedure"
immediateSetNRegression = refl

longitudinalSetNRegression :
  Sets.Analysis.AnalysisSetReceipt.analysisN Sets.colladoT2Set
  ≡ Ceiling.explicitlyReportedNat 98
      "49 experimental + 49 control completed T2"
longitudinalSetNRegression = refl
