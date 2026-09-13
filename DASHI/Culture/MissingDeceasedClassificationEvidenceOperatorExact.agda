module DASHI.Culture.MissingDeceasedClassificationEvidenceOperatorExact where

open import DASHI.Core.Prelude
open import DASHI.Core.ScientificOperatorFamilyExact as O

fengClassificationEvidence : O.OperatorFactorisation
fengClassificationEvidence = O.operator-factorisation
  "Feng Yanghe"
  "DASHI.GameTheory.FengYangheMilitaryAIGameStatisticsBidiExact"
  O.classificationEvidenceShape
  "labelled/noisy-labelled samples + statistical assumptions -> Bayesian/noise-aware classifier -> class/decision output"
  "Classification rules and noise models remain source-specific; this does not weld the publication to War Skull code."

liuClassificationEvidence : O.OperatorFactorisation
liuClassificationEvidence = O.operator-factorisation
  "Liu Donghao"
  "DASHI.ComputerScience.LiuDonghaoDSMMBidiExact"
  O.classificationEvidenceShape
  "data-lifecycle controls/evidence -> maturity assessment -> evidence-bearing maturity state"
  "Governance maturity assessment shares evidence-to-decision structure without becoming machine learning."

chenClassificationEvidence : O.OperatorFactorisation
chenClassificationEvidence = O.operator-factorisation
  "Chen Shuming"
  "DASHI.ComputerScience.ChenShumingGraphHardwareVerificationBidiExact"
  O.classificationEvidenceShape
  "graph specification + simulated trace -> conformance/coverage assessment -> verified/mismatch state"
  "Verification is an evidence-bearing decision operator; hardware semantics remain distinct from classification science."

classificationEvidenceFactorisations : List O.OperatorFactorisation
classificationEvidenceFactorisations =
  fengClassificationEvidence ∷ liuClassificationEvidence ∷ chenClassificationEvidence ∷ []
