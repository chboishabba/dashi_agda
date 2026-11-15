module DASHI.Cognition.PNF.X369OrbitAbsolutePhaseGaugeExact where

-- X369 F2 finite mathematical correction: orbit ACTION INDEX is not
-- the absolute CHARACTER LABEL.  A shifted orbit base must be divided
-- out before interpreting within-orbit character multiplication.
-- Uses original C3Phase and multiplyPhase from the in-repo character owner.
--
-- Not a learned Leech neural circuit, labelled natural-language action,
-- or a source-to-PyTorch tensor BIDI.  Kernel receipt still required.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Algebra.TriadicDepthOneCharacters as Characters

open Characters using (C3Phase; phase0; phase1; phase2)

absolutePhaseNormalize : C3Phase → C3Phase → C3Phase
absolutePhaseNormalize base phase =
  Characters.multiplyPhase (Characters.conjugatePhase base)
                           (Characters.multiplyPhase base phase)

-- Nine cases on the ORIGINAL character carrier, not a new synthetic C3.
absolutePhaseNormalizeCancelsBase :
  ∀ base phase → absolutePhaseNormalize base phase ≡ phase
absolutePhaseNormalizeCancelsBase phase0 phase0 = refl
absolutePhaseNormalizeCancelsBase phase0 phase1 = refl
absolutePhaseNormalizeCancelsBase phase0 phase2 = refl
absolutePhaseNormalizeCancelsBase phase1 phase0 = refl
absolutePhaseNormalizeCancelsBase phase1 phase1 = refl
absolutePhaseNormalizeCancelsBase phase1 phase2 = refl
absolutePhaseNormalizeCancelsBase phase2 phase0 = refl
absolutePhaseNormalizeCancelsBase phase2 phase1 = refl
absolutePhaseNormalizeCancelsBase phase2 phase2 = refl

-- Once the absolute origin is restored, composition respects the
-- original character multiplication at any orbit base.
absolutePhaseCompositionAfterReindexing :
  ∀ base left right →
  Characters.multiplyPhase
    (absolutePhaseNormalize base left)
    (absolutePhaseNormalize base right)
  ≡ absolutePhaseNormalize base
      (Characters.multiplyPhase left right)
absolutePhaseCompositionAfterReindexing base left right
  rewrite absolutePhaseNormalizeCancelsBase base left
        | absolutePhaseNormalizeCancelsBase base right
        | absolutePhaseNormalizeCancelsBase base
            (Characters.multiplyPhase left right) = refl

-- Exact counterexample to incorrectly using the orbit's shifted base
-- (phase1) as though it were absolute identity phase0.
shiftedBaseNaivePhaseSquareIsPhase2 :
  Characters.multiplyPhase phase1 phase1 ≡ phase2
shiftedBaseNaivePhaseSquareIsPhase2 = refl

shiftedBaseNaiveCompositionCannotEqualPhase1 :
  Characters.multiplyPhase phase1 phase1 ≡ phase1 → ⊥
shiftedBaseNaiveCompositionCannotEqualPhase1 ()

-- Still OPEN: an independently labelled original LM task action,
-- original checkpoint hidden representation, consumer equivalence,
-- phase readout identifiability and paired causal excess loss.
