module DASHI.Physics.CondensedMatter.MATBGBMEisensteinMatrixValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Biology.EisensteinNineRingInterferenceExact as E
import DASHI.Physics.CondensedMatter.MATBGBMFirstHarmonicC3Exact as BM
import DASHI.Physics.CondensedMatter.MATBGBMEisensteinMatrixExact as Exact

phaseZeroEvaluatesToOne : Exact.phaseToEisenstein C3.phase0 ≡ E.one
phaseZeroEvaluatesToOne = refl

phaseOneEvaluatesToOmega : Exact.phaseToEisenstein C3.phase1 ≡ E.omega
phaseOneEvaluatesToOmega = refl

phaseTwoEvaluatesToOmegaSquared : Exact.phaseToEisenstein C3.phase2 ≡ E.omegaSquared
phaseTwoEvaluatesToOmegaSquared = refl

phaseConjugationCommutesWithEvaluation :
  (p : C3.C3Phase) →
  Exact.phaseToEisenstein (C3.conjugatePhase p)
    ≡ E.conjugate (Exact.phaseToEisenstein p)
phaseConjugationCommutesWithEvaluation = Exact.phaseEvaluationConjugates

matrixTimeReversalSurvivesExactEvaluation :
  (v : BM.Valley) (h : BM.MoireHarmonic) →
  Exact.evaluateTunnellingMatrix Exact.fixtureW0 Exact.fixtureW1
    (BM.tunnellingMatrix (BM.timeReverseValley v) h)
    ≡
  Exact.conjugateEisensteinMatrix
    (Exact.evaluateTunnellingMatrix Exact.fixtureW0 Exact.fixtureW1
      (BM.tunnellingMatrix v h))
matrixTimeReversalSurvivesExactEvaluation = Exact.evaluatedMatrixTimeReversal

exactEisensteinBackendIsPaid :
  Exact.exactEisensteinMatrixBackendPaid Exact.canonicalBMEisensteinBoundary ≡ true
exactEisensteinBackendIsPaid = refl

sampleCalibrationStillUnpaid :
  Exact.sampleW0W1CalibrationPaid Exact.canonicalBMEisensteinBoundary ≡ false
sampleCalibrationStillUnpaid = refl
