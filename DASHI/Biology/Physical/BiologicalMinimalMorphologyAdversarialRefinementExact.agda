module DASHI.Biology.Physical.BiologicalMinimalMorphologyAdversarialRefinementExact where

------------------------------------------------------------------------
-- A constructive negative control for the EXACT 18-class fixture quotient.
-- If an independently justified future intervention reads the discarded
-- chromatin-marker coordinate, the original 18-class code ceases to be
-- behaviourally safe. No claim is made that the synthetic marker-probe
-- is a real molecular assay or that chromatin is inert in real biology.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Bio
import DASHI.Biology.Physical.BiologicalMinimalMorphologyFutureQuotientExact as Minimal
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Bridge
import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement
import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Section
import DASHI.Core.FutureObservationLanguageQuotientExact as Future

data MarkerSensitiveAction : Set where
  markerProbe : MarkerSensitiveAction

markerActionLabel : MarkerSensitiveAction → String
markerActionLabel markerProbe = "synthetic-marker-sensitive-probe"

markerSensitiveStep :
  MarkerSensitiveAction → Bio.BiologicalState → Bio.BiologicalState
markerSensitiveStep markerProbe
  (Bio.biologicalState g c h j e p) =
    Bio.biologicalState g c h j e c

sameMinimal18ClassBeforeMarkerProbe :
  Minimal.minimalProject Bio.withoutMemory
    ≡ Minimal.minimalProject Bio.differentMarker
sameMinimal18ClassBeforeMarkerProbe = refl

markerProbeReadsFirstFalse :
  Bio.observe (markerSensitiveStep markerProbe Bio.withoutMemory)
    ≡ false
markerProbeReadsFirstFalse = refl

markerProbeReadsSecondTrue :
  Bio.observe (markerSensitiveStep markerProbe Bio.differentMarker)
    ≡ true
markerProbeReadsSecondTrue = refl

original18ClassProjectionNotSafeUnderNewDynamics :
  Future.FutureLanguageSafeProjection
    (Bridge.deterministicSystem markerSensitiveStep markerActionLabel)
    Bio.observe Minimal.minimalProject →
  ⊥
original18ClassProjectionNotSafeUnderNewDynamics safe =
  Bio.false≢true
    (Bridge.canonicalFutureEquivalentImpliesTraceEquivalent
      (Future.kernelContainedInFutureEquivalence
        safe sameMinimal18ClassBeforeMarkerProbe)
      (markerProbe ∷ []))

-- This is why the source/evidence revision loop must be permitted to reopen
-- and refine a quotient when new intervention measurements discriminate it.

-- Stronger necessary condition, for ANY candidate replacement quotient.
-- A new quotient cannot be future-safe if it still identifies this pair.
-- This does not presume a minimal replacement partition.
everySafeMarkerProjectionSeparatesWitness :
  (Q : Set) (project : Bio.BiologicalState → Q) →
  Future.FutureLanguageSafeProjection
    (Bridge.deterministicSystem markerSensitiveStep markerActionLabel)
    Bio.observe project →
  project Bio.withoutMemory ≡ project Bio.differentMarker →
  ⊥
everySafeMarkerProjectionSeparatesWitness Q project safe same =
  Bio.false≢true
    (Bridge.canonicalFutureEquivalentImpliesTraceEquivalent
      (Future.kernelContainedInFutureEquivalence safe same)
      (markerProbe ∷ []))

-- The previous 18-class counterexample is a direct specialization of
-- this general separation requirement. No new observer carrier is needed.
original18ClassFailureFromNecessarySeparation :
  Future.FutureLanguageSafeProjection
    (Bridge.deterministicSystem markerSensitiveStep markerActionLabel)
    Bio.observe Minimal.minimalProject →
  ⊥
original18ClassFailureFromNecessarySeparation safe =
  everySafeMarkerProjectionSeparatesWitness
    Minimal.MorphologyFutureCode Minimal.minimalProject safe
    sameMinimal18ClassBeforeMarkerProbe

-- Selected finite positive repair: retain the marker coordinate while
-- keeping the original minimal morphology code. No physical optimality
-- or real biochemical validity is implied.
markerAwareProject :
  Bio.BiologicalState → Minimal.MorphologyFutureCode × Bool
markerAwareProject state@(Bio.biologicalState g c h j e p) =
  Minimal.minimalProject state , c

markerAwareObserve : Minimal.MorphologyFutureCode × Bool → Bool
markerAwareObserve (code , c) = Minimal.minimalObserve code

replaceMorphology :
  Minimal.MorphologyFutureCode → Bool → Minimal.MorphologyFutureCode
replaceMorphology (Minimal.inactive p) c = Minimal.inactive c
replaceMorphology (Minimal.active h j e p) c = Minimal.active h j e c

markerAwareStep :
  MarkerSensitiveAction →
  Minimal.MorphologyFutureCode × Bool →
  Minimal.MorphologyFutureCode × Bool
markerAwareStep markerProbe (code , c) =
  replaceMorphology code c , c

markerAwareObservationCommutes :
  (state : Bio.BiologicalState) →
  markerAwareObserve (markerAwareProject state) ≡ Bio.observe state
markerAwareObservationCommutes (Bio.biologicalState false c h j e p) = refl
markerAwareObservationCommutes (Bio.biologicalState true c h j e p) = refl

markerAwareStepCommutes :
  (a : MarkerSensitiveAction) (state : Bio.BiologicalState) →
  markerAwareProject (markerSensitiveStep a state)
    ≡ markerAwareStep a (markerAwareProject state)
markerAwareStepCommutes markerProbe
  (Bio.biologicalState false c h j e p) = refl
markerAwareStepCommutes markerProbe
  (Bio.biologicalState true c h j e p) = refl

markerAwareAfterTrace :
  (actions : List MarkerSensitiveAction) (state : Bio.BiologicalState) →
  markerAwareProject (Refinement.run markerSensitiveStep actions state)
    ≡ Refinement.run markerAwareStep actions (markerAwareProject state)
markerAwareAfterTrace [] state = refl
markerAwareAfterTrace (a ∷ rest) state =
  trans
    (markerAwareAfterTrace rest (markerSensitiveStep a state))
    (cong (Refinement.run markerAwareStep rest)
      (markerAwareStepCommutes a state))

markerAwareCodeImpliesTraceEquivalence :
  ∀ {left right} →
  markerAwareProject left ≡ markerAwareProject right →
  Bridge.TraceEquivalent Bio.observe markerSensitiveStep left right
markerAwareCodeImpliesTraceEquivalence {left} {right} same actions =
  trans
    (sym (markerAwareObservationCommutes
      (Refinement.run markerSensitiveStep actions left)))
    (trans
      (cong markerAwareObserve (markerAwareAfterTrace actions left))
      (trans
        (cong
          (λ code → markerAwareObserve (Refinement.run markerAwareStep actions code))
          same)
        (trans
          (sym (cong markerAwareObserve (markerAwareAfterTrace actions right)))
          (markerAwareObservationCommutes
            (Refinement.run markerSensitiveStep actions right)))))

markerAwareFutureSafe :
  Future.FutureLanguageSafeProjection
    (Bridge.deterministicSystem markerSensitiveStep markerActionLabel)
    Bio.observe markerAwareProject
markerAwareFutureSafe =
  Future.futureLanguageSafeProjection
    (λ {left} {right} same →
      Bridge.traceEquivalentImpliesCanonicalFutureEquivalent
        (markerAwareCodeImpliesTraceEquivalence same))

-- Cross-domain same-interface weld: instantiate the EXACT canonical
-- SectionedProjection/ResidualReopening types used by the original TSVF
-- observer, without identifying their different physical state carriers.
markerCodeSection :
  Section.SectionedProjection
    (Minimal.MorphologyFutureCode × Bool)
    Minimal.MorphologyFutureCode
markerCodeSection = record
  { Section.SectionedProjection.project = proj₁
  ; Section.SectionedProjection.representative = λ code → code , false
  ; Section.SectionedProjection.section = λ _ → refl
  }

markerCodeResidual :
  Section.ResidualReopening markerCodeSection
markerCodeResidual = record
  { Section.ResidualReopening.Residual = Bool
  ; Section.ResidualReopening.residual = proj₂
  ; Section.ResidualReopening.reopen = λ code marker → code , marker
  ; Section.ResidualReopening.reopenExact = λ { (code , marker) → refl }
  }

markerCodeReopensExactly :
  (state : Minimal.MorphologyFutureCode × Bool) →
  Section.reopen markerCodeResidual
    (Section.project markerCodeSection state)
    (Section.residual markerCodeResidual state) ≡ state
markerCodeReopensExactly =
  Section.reopenExact markerCodeResidual

-- The same old coarse code carries the two different marker values.
-- The impossibility is constructive and requires no injection/choice.
oldMorphologyCodeCannotDecodeMarker :
  (decode : Minimal.MorphologyFutureCode → Bool) →
  ((state : Bio.BiologicalState) →
    decode (Minimal.minimalProject state) ≡ Bio.chromatinMarker state) →
  ⊥
oldMorphologyCodeCannotDecodeMarker decode correct =
  Bio.false≢true
    (trans
      (sym (correct Bio.withoutMemory))
      (trans
        (cong decode sameMinimal18ClassBeforeMarkerProbe)
        (correct Bio.differentMarker)))
