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
  Exact.qtmNormalizedTunnellingMatrix (BM.timeReverseValley v) h
    ≡
  Exact.conjugateEisensteinMatrix
    (Exact.qtmNormalizedTunnellingMatrix v h)
matrixTimeReversalSurvivesExactEvaluation = Exact.evaluatedMatrixTimeReversal

exactEisensteinBackendIsPaid :
  Exact.exactEisensteinMatrixBackendPaid Exact.canonicalBMEisensteinBoundary ≡ true
exactEisensteinBackendIsPaid = refl

sourceNormalizedRatioIsPaid :
  Exact.sourceNormalizedW0W1RatioPaid Exact.canonicalBMEisensteinBoundary ≡ true
sourceNormalizedRatioIsPaid = refl

absoluteTunnellingScaleStillUnpaid :
  Exact.absoluteTunnellingEnergyScalePaid Exact.canonicalBMEisensteinBoundary ≡ false
absoluteTunnellingScaleStillUnpaid = refl

biologyMechanismDoesNotTransfer :
  Exact.biologyMechanismTransferred Exact.canonicalBMEisensteinBoundary ≡ false
biologyMechanismDoesNotTransfer = refl
