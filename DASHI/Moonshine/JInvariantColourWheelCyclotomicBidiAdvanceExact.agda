module DASHI.Moonshine.JInvariantColourWheelCyclotomicBidiAdvanceExact where

------------------------------------------------------------------------
-- COLOUR-WHEEL BIDI ADVANCE: FINITE PHASE -> EXACT CYCLOTOMIC PHASE
--
-- The previous introspective cut stopped at "complex root-of-unity
-- realisation" because Base369PolyphaseCharacters deliberately left that
-- promotion gated.  A broader repo search finds stronger existing owners:
--
--   C3FourierConjugationExact
--     Audrey Terras, Fourier Analysis on Finite Groups and Applications,
--     DOI 10.1017/CBO9780511626265;
--     Jean-Pierre Serre, Linear Representations of Finite Groups,
--     DOI 10.1007/978-1-4684-9458-7;
--     Barraclough & Wilson, Character Table of a Maximal Subgroup of the
--     Monster, DOI 10.1112/S1461157000001352.
--
--   MonsterC3CyclotomicEvaluationExact
--     I. M. Isaacs, Character Theory of Finite Groups, ISBN 978-0-486-68014-9;
--     Audrey Terras, DOI 10.1017/CBO9780511626265.
--
-- These owners provide exact symbolic C3 roots/Fourier rows and an integer
-- cyclotomic carrier a+b*zeta.  They do NOT provide the analytic embedding
-- into the complex upper-half-plane/theta carrier required by j.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Foundations.Base369PolyphaseCharacters as Polyphase
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Moonshine.MonsterC3CyclotomicEvaluationExact as Cyclotomic
import DASHI.Moonshine.JInvariantColourWheelPolyphaseSpectralBidiExact as Weld
import DASHI.Moonshine.JInvariantSourceAtlasExact as Sources

------------------------------------------------------------------------
-- 1. Exact sequence <-> symbolic C3 phase equivalence.
------------------------------------------------------------------------

sequenceToPhase : Polyphase.C3Sequence → C3.C3Phase
sequenceToPhase Polyphase.zeroSequence = C3.phase0
sequenceToPhase Polyphase.positiveSequence = C3.phase1
sequenceToPhase Polyphase.negativeSequence = C3.phase2

phaseToSequence : C3.C3Phase → Polyphase.C3Sequence
phaseToSequence C3.phase0 = Polyphase.zeroSequence
phaseToSequence C3.phase1 = Polyphase.positiveSequence
phaseToSequence C3.phase2 = Polyphase.negativeSequence

sequencePhaseRoundTrip :
  (s : Polyphase.C3Sequence) → phaseToSequence (sequenceToPhase s) ≡ s
sequencePhaseRoundTrip Polyphase.zeroSequence = refl
sequencePhaseRoundTrip Polyphase.positiveSequence = refl
sequencePhaseRoundTrip Polyphase.negativeSequence = refl

phaseSequenceRoundTrip :
  (p : C3.C3Phase) → sequenceToPhase (phaseToSequence p) ≡ p
phaseSequenceRoundTrip C3.phase0 = refl
phaseSequenceRoundTrip C3.phase1 = refl
phaseSequenceRoundTrip C3.phase2 = refl

sequenceConjugationMatchesPhaseConjugation :
  (s : Polyphase.C3Sequence) →
  sequenceToPhase (Weld.conjugateSequence s) ≡
  C3.conjugatePhase (sequenceToPhase s)
sequenceConjugationMatchesPhaseConjugation Polyphase.zeroSequence = refl
sequenceConjugationMatchesPhaseConjugation Polyphase.positiveSequence = refl
sequenceConjugationMatchesPhaseConjugation Polyphase.negativeSequence = refl

------------------------------------------------------------------------
-- 2. Exact Fourier-row realization of the same three sequence labels.
------------------------------------------------------------------------

sequenceFourierRow : Polyphase.C3Sequence → Fourier.FourierRow
sequenceFourierRow Polyphase.zeroSequence = Fourier.chi0
sequenceFourierRow Polyphase.positiveSequence = Fourier.chi1
sequenceFourierRow Polyphase.negativeSequence = Fourier.chi2

sequenceConjugationMatchesFourierRowConjugation :
  (s : Polyphase.C3Sequence) →
  sequenceFourierRow (Weld.conjugateSequence s) ≡
  Fourier.conjugateRow (sequenceFourierRow s)
sequenceConjugationMatchesFourierRowConjugation Polyphase.zeroSequence =
  Fourier.chi0IsFixedByConjugation
sequenceConjugationMatchesFourierRowConjugation Polyphase.positiveSequence =
  Fourier.chi1ConjugateIsChi2
sequenceConjugationMatchesFourierRowConjugation Polyphase.negativeSequence =
  Fourier.chi2ConjugateIsChi1

------------------------------------------------------------------------
-- 3. Exact cyclotomic evaluation labels.
------------------------------------------------------------------------

sequenceCyclotomicValue : Polyphase.C3Sequence → Cyclotomic.Cyclotomic3
sequenceCyclotomicValue Polyphase.zeroSequence = Cyclotomic.oneC3
sequenceCyclotomicValue Polyphase.positiveSequence = Cyclotomic.zetaC3
sequenceCyclotomicValue Polyphase.negativeSequence = Cyclotomic.zetaSquaredC3

regularThreePhaseCyclotomicSum : Cyclotomic.Cyclotomic3
regularThreePhaseCyclotomicSum =
  Cyclotomic._+c3_
    (Cyclotomic._+c3_
      (sequenceCyclotomicValue Polyphase.zeroSequence)
      (sequenceCyclotomicValue Polyphase.positiveSequence))
    (sequenceCyclotomicValue Polyphase.negativeSequence)

regularThreePhaseCyclotomicSumCancels :
  regularThreePhaseCyclotomicSum ≡ Cyclotomic.zeroC3
regularThreePhaseCyclotomicSumCancels =
  Cyclotomic.completeRegularPhaseOrbitCancels

------------------------------------------------------------------------
-- 4. Refined BIDI cut.
--
-- Finite phase labelling, symbolic root arithmetic, conjugate Fourier rows,
-- and exact integer cyclotomic evaluation are now on the forward side.
-- Backward from theta/j, the first surviving coordinate is an ANALYTIC
-- same-object embedding of this exact cyclotomic phase into the complex wave/
-- theta carrier.  That is strictly narrower than "find roots of unity".
------------------------------------------------------------------------

data CyclotomicAnalyticResidual : Set where
  missingAnalyticCyclotomicEmbedding : CyclotomicAnalyticResidual
  missingThetaSameObjectRealisation : CyclotomicAnalyticResidual
  missingJSameObjectWeld : CyclotomicAnalyticResidual
  missingMonsterActionIntertwiner : CyclotomicAnalyticResidual

firstRefinedAnalyticResidual : CyclotomicAnalyticResidual
firstRefinedAnalyticResidual = missingAnalyticCyclotomicEmbedding

record CyclotomicColourWheelExact : Set₁ where
  constructor cyclotomic-colour-wheel-exact
  field
    sequencePhaseBidi :
      (s : Polyphase.C3Sequence) → phaseToSequence (sequenceToPhase s) ≡ s
    sequenceFourierConjugation :
      (s : Polyphase.C3Sequence) →
      sequenceFourierRow (Weld.conjugateSequence s) ≡
      Fourier.conjugateRow (sequenceFourierRow s)
    regularPhaseCancellation :
      regularThreePhaseCyclotomicSum ≡ Cyclotomic.zeroC3

cyclotomicColourWheelExact : CyclotomicColourWheelExact
cyclotomicColourWheelExact =
  cyclotomic-colour-wheel-exact
    sequencePhaseRoundTrip
    sequenceConjugationMatchesFourierRowConjugation
    regularThreePhaseCyclotomicSumCancels

refinedColourWheelBidiCut :
  Bidi.ApproximationWithResidualObligation
    CyclotomicColourWheelExact
    CyclotomicAnalyticResidual
refinedColourWheelBidiCut =
  Bidi.approximationWithResidualObligation
    cyclotomicColourWheelExact
    firstRefinedAnalyticResidual

------------------------------------------------------------------------
-- 5. Source/introspection firewall.
------------------------------------------------------------------------

visualStillDoesNotEntitleThetaClaim :
  Sources.JSourceAttributionBoundary.visualPatternIsSourceEntitledClaim
    Sources.canonicalJSourceAttributionBoundary ≡ false
visualStillDoesNotEntitleThetaClaim = refl
