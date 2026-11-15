module DASHI.Biology.Physical.BiologicalMinimalMorphologyFutureQuotientExact where

------------------------------------------------------------------------
-- P1: EXACT MINIMAL FUTURE QUOTIENT FOR THE *MORPHOLOGY* OBSERVER
--
-- The older five-coordinate code is sufficient, but not minimal:
-- when genome competence is false, its remaining latent flags cannot
-- affect any future observed morphology under the selected interventions.
-- This module proves BOTH directions of the canonical future-language
-- equivalence for the smaller code, using five explicit diagnostic words.
--
-- This is an exact theorem about the source-written BOOLEAN fixture,
-- not a claim that the same quotient describes real developmental biology.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Bio
import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Bridge
import DASHI.Core.FutureObservationLanguageQuotientExact as Future

data MorphologyFutureCode : Set where
  inactive : Bool → MorphologyFutureCode
  active : Bool → Bool → Bool → Bool → MorphologyFutureCode

-- The Boolean phenotype itself is always observed.
-- For g=false all h/j/e states collapse; for g=true the three
-- latent causal flags must remain distinguishable under interventions.
minimalProject : Bio.BiologicalState → MorphologyFutureCode
minimalProject (Bio.biologicalState false c h j e p) = inactive p
minimalProject (Bio.biologicalState true c h j e p) = active h j e p

minimalObserve : MorphologyFutureCode → Bool
minimalObserve (inactive p) = p
minimalObserve (active h j e p) = p

minimalStep :
  Bio.Intervention → MorphologyFutureCode → MorphologyFutureCode
minimalStep Bio.signal (inactive p) = inactive false
minimalStep Bio.signal (active h j e p) =
  active h j e (Bio.andB h (Bio.andB j e))
minimalStep Bio.wound (inactive p) = inactive false
minimalStep Bio.wound (active h j e p) = active h j e false
minimalStep Bio.connect (inactive p) = inactive p
minimalStep Bio.connect (active h j e p) = active h true e p
minimalStep Bio.restoreMemory (inactive p) = inactive p
minimalStep Bio.restoreMemory (active h j e p) = active true j e p
minimalStep Bio.provideEnvironment (inactive p) = inactive p
minimalStep Bio.provideEnvironment (active h j e p) = active h j true p

minimalStepCommutes :
  (a : Bio.Intervention) (state : Bio.BiologicalState) →
  minimalProject (Bio.step a state)
    ≡ minimalStep a (minimalProject state)
minimalStepCommutes Bio.signal
  (Bio.biologicalState false c h j e p) = refl
minimalStepCommutes Bio.signal
  (Bio.biologicalState true c h j e p) = refl
minimalStepCommutes Bio.wound
  (Bio.biologicalState false c h j e p) = refl
minimalStepCommutes Bio.wound
  (Bio.biologicalState true c h j e p) = refl
minimalStepCommutes Bio.connect
  (Bio.biologicalState false c h j e p) = refl
minimalStepCommutes Bio.connect
  (Bio.biologicalState true c h j e p) = refl
minimalStepCommutes Bio.restoreMemory
  (Bio.biologicalState false c h j e p) = refl
minimalStepCommutes Bio.restoreMemory
  (Bio.biologicalState true c h j e p) = refl
minimalStepCommutes Bio.provideEnvironment
  (Bio.biologicalState false c h j e p) = refl
minimalStepCommutes Bio.provideEnvironment
  (Bio.biologicalState true c h j e p) = refl

observationCommutes :
  (state : Bio.BiologicalState) →
  minimalObserve (minimalProject state) ≡ Bio.observe state
observationCommutes (Bio.biologicalState false c h j e p) = refl
observationCommutes (Bio.biologicalState true c h j e p) = refl

minimalProjectionAfterTrace :
  (actions : List Bio.Intervention) (state : Bio.BiologicalState) →
  minimalProject (Refinement.run Bio.step actions state)
  ≡ Refinement.run minimalStep actions (minimalProject state)
minimalProjectionAfterTrace [] state = refl
minimalProjectionAfterTrace (a ∷ rest) state =
  trans
    (minimalProjectionAfterTrace rest (Bio.step a state))
    (cong (Refinement.run minimalStep rest)
      (minimalStepCommutes a state))

minimalCodeImpliesTraceEquivalence :
  ∀ {left right} →
  minimalProject left ≡ minimalProject right →
  Bridge.TraceEquivalent Bio.observe Bio.step left right
minimalCodeImpliesTraceEquivalence {left} {right} same actions =
  trans
    (sym (observationCommutes (Refinement.run Bio.step actions left)))
    (trans
      (cong minimalObserve (minimalProjectionAfterTrace actions left))
      (trans
        (cong
          (λ code →
            minimalObserve (Refinement.run minimalStep actions code))
          same)
        (trans
          (sym (cong minimalObserve
            (minimalProjectionAfterTrace actions right)))
          (observationCommutes
            (Refinement.run Bio.step actions right)))))

-- Five finite experiments recover the minimal class from current
-- morphology and responses to controlled intervention histories.
-- The first word turns on ALL three modifiable flags, revealing genome.
-- The other three leave exactly one modifiable flag unchanged.
genomeWord : List Bio.Intervention
genomeWord =
  Bio.restoreMemory ∷ Bio.connect ∷
  Bio.provideEnvironment ∷ Bio.signal ∷ []

memoryWord : List Bio.Intervention
memoryWord = Bio.connect ∷ Bio.provideEnvironment ∷ Bio.signal ∷ []

junctionWord : List Bio.Intervention
junctionWord =
  Bio.restoreMemory ∷ Bio.provideEnvironment ∷ Bio.signal ∷ []

environmentWord : List Bio.Intervention
environmentWord = Bio.restoreMemory ∷ Bio.connect ∷ Bio.signal ∷ []

readTrace : List Bio.Intervention → Bio.BiologicalState → Bool
readTrace actions state =
  Bio.observe (Refinement.run Bio.step actions state)

record Diagnostic : Set where
  constructor diagnostic
  field
    presentReading : Bool
    genomeReading : Bool
    memoryReading : Bool
    junctionReading : Bool
    environmentReading : Bool

diagnosticOf : Bio.BiologicalState → Diagnostic
diagnosticOf x =
  diagnostic (readTrace [] x)
    (readTrace genomeWord x)
    (readTrace memoryWord x)
    (readTrace junctionWord x)
    (readTrace environmentWord x)

decodeDiagnostic : Diagnostic → MorphologyFutureCode
decodeDiagnostic (diagnostic p false h j e) = inactive p
decodeDiagnostic (diagnostic p true h j e) = active h j e p

-- All 2^3 active flag configurations are covered, without classical
-- choice, extensionality, an opaque solver or a postulated oracle.
diagnosticRecoversCode :
  (x : Bio.BiologicalState) →
  decodeDiagnostic (diagnosticOf x) ≡ minimalProject x
diagnosticRecoversCode
  (Bio.biologicalState false c h j e p) = refl
diagnosticRecoversCode
  (Bio.biologicalState true c false false false p) = refl
diagnosticRecoversCode
  (Bio.biologicalState true c false false true p) = refl
diagnosticRecoversCode
  (Bio.biologicalState true c false true false p) = refl
diagnosticRecoversCode
  (Bio.biologicalState true c false true true p) = refl
diagnosticRecoversCode
  (Bio.biologicalState true c true false false p) = refl
diagnosticRecoversCode
  (Bio.biologicalState true c true false true p) = refl
diagnosticRecoversCode
  (Bio.biologicalState true c true true false p) = refl
diagnosticRecoversCode
  (Bio.biologicalState true c true true true p) = refl

traceEquivalenceImpliesSameDiagnostic :
  ∀ {left right} →
  Bridge.TraceEquivalent Bio.observe Bio.step left right →
  diagnosticOf left ≡ diagnosticOf right
traceEquivalenceImpliesSameDiagnostic equal
  rewrite equal []
        | equal genomeWord
        | equal memoryWord
        | equal junctionWord
        | equal environmentWord = refl

traceEquivalenceImpliesMinimalCode :
  ∀ {left right} →
  Bridge.TraceEquivalent Bio.observe Bio.step left right →
  minimalProject left ≡ minimalProject right
traceEquivalenceImpliesMinimalCode {left} {right} equal =
  trans
    (sym (diagnosticRecoversCode left))
    (trans
      (cong decodeDiagnostic
        (traceEquivalenceImpliesSameDiagnostic equal))
      (diagnosticRecoversCode right))

-- Exactly the canonical behavioural equivalence, in BOTH directions.
-- 2 inactive classes + 2^4 active classes = 18 finite code classes.
morphologyFutureEquivalenceExactlyMinimalCode :
  (left right : Bio.BiologicalState) →
  (minimalProject left ≡ minimalProject right →
    Future.FutureObservationEquivalent
      (Bridge.deterministicSystem Bio.step Bio.actionLabel)
      Bio.observe left right)
  ×
  (Future.FutureObservationEquivalent
      (Bridge.deterministicSystem Bio.step Bio.actionLabel)
      Bio.observe left right →
    minimalProject left ≡ minimalProject right)
morphologyFutureEquivalenceExactlyMinimalCode left right =
  (λ same →
    Bridge.traceEquivalentImpliesCanonicalFutureEquivalent
      (minimalCodeImpliesTraceEquivalence same))
  ,
  (λ equivalent →
    traceEquivalenceImpliesMinimalCode
      (Bridge.canonicalFutureEquivalentImpliesTraceEquivalent equivalent))

minimalMorphologyFutureSafe :
  Future.FutureLanguageSafeProjection
    (Bridge.deterministicSystem Bio.step Bio.actionLabel)
    Bio.observe minimalProject
minimalMorphologyFutureSafe =
  Future.futureLanguageSafeProjection
    (λ {left} {right} same →
      proj₁ (morphologyFutureEquivalenceExactlyMinimalCode left right)
        same)

-- This exact collapse is specific to the fixture's intervention family.
-- Genome-off cells can have different memory/junction/environment and
-- still have identical future observed morphology.
genomeOffLeft genomeOffRight : Bio.BiologicalState
genomeOffLeft = Bio.biologicalState false false false false false true
genomeOffRight = Bio.biologicalState false true true true true true

genomeOffClassesCollapse :
  minimalProject genomeOffLeft ≡ minimalProject genomeOffRight
genomeOffClassesCollapse = refl

genomeOffStillFutureEquivalent :
  Future.FutureObservationEquivalent
    (Bridge.deterministicSystem Bio.step Bio.actionLabel)
    Bio.observe genomeOffLeft genomeOffRight
genomeOffStillFutureEquivalent =
  proj₁
    (morphologyFutureEquivalenceExactlyMinimalCode
      genomeOffLeft genomeOffRight)
    genomeOffClassesCollapse
