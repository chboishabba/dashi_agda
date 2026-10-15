module DASHI.Physics.CondensedMatter.MATBGBMEisensteinMatrixExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; _/_)
open import Relation.Binary.PropositionalEquality using (cong₂)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Biology.EisensteinNineRingInterferenceExact as E
import DASHI.Physics.CondensedMatter.MATBGBMFirstHarmonicC3Exact as BM

------------------------------------------------------------------------
-- EXACT EISENSTEIN EVALUATION OF THE BM C3 TUNNELLING MATRICES
--
-- The imported Eisenstein carrier is used ONLY as exact mathematics:
-- rational coordinates for 1, omega and omega^2 with conjugation.  No biology
-- mechanism or authority is transferred into the condensed-matter consumer.
--
-- The source-reported QTM matrix-element fit w0/w1 = 0.6 is represented in a
-- dimensionless normalized convention w1 = 1 and w0 = 3/5.  This pays a ratio
-- coordinate only; no absolute tunnelling-energy scale is inferred.
------------------------------------------------------------------------

phaseToEisenstein : C3.C3Phase → E.Eisenstein
phaseToEisenstein C3.phase0 = E.one
phaseToEisenstein C3.phase1 = E.omega
phaseToEisenstein C3.phase2 = E.omegaSquared

phaseEvaluationConjugates :
  (p : C3.C3Phase) →
  phaseToEisenstein (C3.conjugatePhase p)
    ≡ E.conjugate (phaseToEisenstein p)
phaseEvaluationConjugates C3.phase0 = refl
phaseEvaluationConjugates C3.phase1 = refl
phaseEvaluationConjugates C3.phase2 = refl

qOne qThreeFifths : ℚ
qOne = + 1 / 1
qThreeFifths = + 3 / 5

qtmNormalizedW0 qtmNormalizedW1 : ℚ
qtmNormalizedW0 = qThreeFifths
qtmNormalizedW1 = qOne

scaledPhase : ℚ → C3.C3Phase → E.Eisenstein
scaledPhase amplitude C3.phase0 = E.eisenstein amplitude 0ℚ
scaledPhase amplitude C3.phase1 = E.eisenstein 0ℚ amplitude
scaledPhase amplitude C3.phase2 =
  E.eisenstein (0ℚ - amplitude) (0ℚ - amplitude)

scaledPhaseEvaluationConjugates :
  (amplitude : ℚ) (p : C3.C3Phase) →
  scaledPhase amplitude (C3.conjugatePhase p)
    ≡ E.conjugate (scaledPhase amplitude p)
scaledPhaseEvaluationConjugates amplitude C3.phase0 =
  cong₂ E.eisenstein
    (ℚRing.solve-∀ amplitude)
    (ℚRing.solve-∀ amplitude)
scaledPhaseEvaluationConjugates amplitude C3.phase1 =
  cong₂ E.eisenstein
    (ℚRing.solve-∀ amplitude)
    (ℚRing.solve-∀ amplitude)
scaledPhaseEvaluationConjugates amplitude C3.phase2 =
  cong₂ E.eisenstein
    (ℚRing.solve-∀ amplitude)
    (ℚRing.solve-∀ amplitude)

record EisensteinMatrix2 : Set where
  constructor eisenstein-matrix2
  field
    entryAA : E.Eisenstein
    entryAB : E.Eisenstein
    entryBA : E.Eisenstein
    entryBB : E.Eisenstein

open EisensteinMatrix2 public

evaluateSymbolicScalar : ℚ → ℚ → BM.BMSymbolicScalar → E.Eisenstein
evaluateSymbolicScalar w0 w1 BM.w0Term = E.eisenstein w0 0ℚ
evaluateSymbolicScalar w0 w1 (BM.w1PhaseTerm p) = scaledPhase w1 p

evaluateTunnellingMatrix :
  ℚ → ℚ → BM.BMSymbolicMatrix2 → EisensteinMatrix2
evaluateTunnellingMatrix w0 w1 (BM.bm-symbolic-matrix2 aa ab ba bb) =
  eisenstein-matrix2
    (evaluateSymbolicScalar w0 w1 aa)
    (evaluateSymbolicScalar w0 w1 ab)
    (evaluateSymbolicScalar w0 w1 ba)
    (evaluateSymbolicScalar w0 w1 bb)

qtmNormalizedTunnellingMatrix : BM.Valley → BM.MoireHarmonic → EisensteinMatrix2
qtmNormalizedTunnellingMatrix v h =
  evaluateTunnellingMatrix qtmNormalizedW0 qtmNormalizedW1
    (BM.tunnellingMatrix v h)

conjugateEisensteinMatrix : EisensteinMatrix2 → EisensteinMatrix2
conjugateEisensteinMatrix (eisenstein-matrix2 aa ab ba bb) =
  eisenstein-matrix2
    (E.conjugate aa)
    (E.conjugate ab)
    (E.conjugate ba)
    (E.conjugate bb)

evaluatedMatrixTimeReversal :
  (v : BM.Valley) (h : BM.MoireHarmonic) →
  qtmNormalizedTunnellingMatrix (BM.timeReverseValley v) h
    ≡
  conjugateEisensteinMatrix (qtmNormalizedTunnellingMatrix v h)
evaluatedMatrixTimeReversal BM.K BM.harmonic0 = refl
evaluatedMatrixTimeReversal BM.K BM.harmonic1 = refl
evaluatedMatrixTimeReversal BM.K BM.harmonic2 = refl
evaluatedMatrixTimeReversal BM.KPrime BM.harmonic0 = refl
evaluatedMatrixTimeReversal BM.KPrime BM.harmonic1 = refl
evaluatedMatrixTimeReversal BM.KPrime BM.harmonic2 = refl

record BMEisensteinBoundary : Set where
  constructor bm-eisenstein-boundary
  field
    exactPhaseEmbeddingPaid : Bool
    exactRationalAmplitudeEvaluationPaid : Bool
    exactEisensteinMatrixBackendPaid : Bool
    evaluatedTimeReversalConjugationPaid : Bool
    sourceNormalizedW0W1RatioPaid : Bool
    biologyMechanismTransferred : Bool
    absoluteTunnellingEnergyScalePaid : Bool
    continuumMomentumLatticePaid : Bool
    interactingSelfEnergyPaid : Bool
    qtmDataReplayPaid : Bool

open BMEisensteinBoundary public

canonicalBMEisensteinBoundary : BMEisensteinBoundary
canonicalBMEisensteinBoundary =
  bm-eisenstein-boundary
    true true true true true false false false false false
