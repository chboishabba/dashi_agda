module DASHI.Biology.Physical.CoupledDevelopmentalOperatorStackExact where

------------------------------------------------------------------------
-- A finite coupled developmental operator stack.
--
-- This module makes the attachment's G/E/T/P/M/B/C/D/X/R/Phi decomposition
-- executable enough to ask causal-order questions.  Independent coordinate
-- writes commute; feedback-coupled operators need not.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

false≢true : false ≢ true
false≢true ()

xor : Bool → Bool → Bool
xor false false = false
xor false true = true
xor true false = true
xor true true = false

record DevelopmentalState : Set where
  constructor developmentalState
  field
    genome : Bool
    epigenetic : Bool
    transcript : Bool
    protein : Bool
    metabolic : Bool
    bioelectric : Bool
    mechanical : Bool
    proliferative : Bool
    migrated : Bool
    repaired : Bool
    phenotype : Bool

open DevelopmentalState public

transcription : DevelopmentalState → DevelopmentalState
transcription (developmentalState g e t p m b c d x r phi) =
  developmentalState g e (xor g e) p m b c d x r phi

translation : DevelopmentalState → DevelopmentalState
translation (developmentalState g e t p m b c d x r phi) =
  developmentalState g e t t m b c d x r phi

metabolism : DevelopmentalState → DevelopmentalState
metabolism (developmentalState g e t p m b c d x r phi) =
  developmentalState g e t p (xor p m) b c d x r phi

bioelectricUpdate : DevelopmentalState → DevelopmentalState
bioelectricUpdate (developmentalState g e t p m b c d x r phi) =
  developmentalState g e t p m (xor p b) c d x r phi

mechanicalUpdate : DevelopmentalState → DevelopmentalState
mechanicalUpdate (developmentalState g e t p m b c d x r phi) =
  developmentalState g e t p m b (xor b c) d x r phi

proliferation : DevelopmentalState → DevelopmentalState
proliferation (developmentalState g e t p m b c d x r phi) =
  developmentalState g e t p m b c (xor m d) x r phi

migration : DevelopmentalState → DevelopmentalState
migration (developmentalState g e t p m b c d x r phi) =
  developmentalState g e t p m b c d (xor c x) r phi

repair : DevelopmentalState → DevelopmentalState
repair (developmentalState g e t p m b c d x r phi) =
  developmentalState g e t p m b c d x true phi

observeMorphology : DevelopmentalState → DevelopmentalState
observeMorphology (developmentalState g e t p m b c d x r phi) =
  developmentalState g e t p m b c d x r (xor c (xor d x))

fullStep : DevelopmentalState → DevelopmentalState
fullStep s =
  observeMorphology
    (repair
      (migration
        (proliferation
          (mechanicalUpdate
            (bioelectricUpdate
              (metabolism
                (translation
                  (transcription s))))))))

------------------------------------------------------------------------
-- Independent writes commute.
------------------------------------------------------------------------

setRepair : Bool → DevelopmentalState → DevelopmentalState
setRepair value (developmentalState g e t p m b c d x r phi) =
  developmentalState g e t p m b c d x value phi

setPhenotype : Bool → DevelopmentalState → DevelopmentalState
setPhenotype value (developmentalState g e t p m b c d x r phi) =
  developmentalState g e t p m b c d x r value

independentCoordinateWritesCommute :
  (r phi : Bool) (s : DevelopmentalState) →
  setRepair r (setPhenotype phi s) ≡ setPhenotype phi (setRepair r s)
independentCoordinateWritesCommute r phi
  (developmentalState g e t p m b c d x oldR oldPhi) = refl

------------------------------------------------------------------------
-- Feedback/order dependence.
------------------------------------------------------------------------

witness : DevelopmentalState
witness = developmentalState true false false false false false false false false false false

transcriptionThenTranslation : DevelopmentalState
transcriptionThenTranslation = translation (transcription witness)

translationThenTranscription : DevelopmentalState
translationThenTranscription = transcription (translation witness)

causalOrderChangesProtein :
  protein transcriptionThenTranslation ≢ protein translationThenTranscription
causalOrderChangesProtein = false≢true

transcriptionAndTranslationDoNotCommute :
  translation (transcription witness) ≢ transcription (translation witness)
transcriptionAndTranslationDoNotCommute eq = causalOrderChangesProtein (cong protein eq)

bioelectricWitness : DevelopmentalState
bioelectricWitness = developmentalState false false false true false false false false false false false

bioelectricThenMechanical : DevelopmentalState
bioelectricThenMechanical = mechanicalUpdate (bioelectricUpdate bioelectricWitness)

mechanicalThenBioelectric : DevelopmentalState
mechanicalThenBioelectric = bioelectricUpdate (mechanicalUpdate bioelectricWitness)

causalOrderChangesMechanics :
  mechanical bioelectricThenMechanical ≢ mechanical mechanicalThenBioelectric
causalOrderChangesMechanics = false≢true

bioelectricAndMechanicalDoNotCommute :
  mechanicalUpdate (bioelectricUpdate bioelectricWitness)
  ≢ bioelectricUpdate (mechanicalUpdate bioelectricWitness)
bioelectricAndMechanicalDoNotCommute eq =
  causalOrderChangesMechanics (cong mechanical eq)

------------------------------------------------------------------------
-- A feed-forward projection is not enough to reconstruct the coupled state.
------------------------------------------------------------------------

transcriptProjection : DevelopmentalState → Bool
transcriptProjection = transcript

sameTranscriptDifferentBioelectric :
  Σ DevelopmentalState (λ left →
    Σ DevelopmentalState (λ right →
      transcriptProjection left ≡ transcriptProjection right ×
      bioelectric left ≢ bioelectric right))
sameTranscriptDifferentBioelectric =
  developmentalState false false false false false false false false false false false ,
  (developmentalState false false false false false true false false false false false ,
    (refl , false≢true))

fullStepFactorisation :
  (s : DevelopmentalState) →
  fullStep s ≡
  observeMorphology
    (repair
      (migration
        (proliferation
          (mechanicalUpdate
            (bioelectricUpdate
              (metabolism
                (translation
                  (transcription s))))))))
fullStepFactorisation s = refl

-- The finite stack is intentionally not claimed to be a calibrated molecular
-- developmental model.  Its theorem surface is causal/factorization geometry.
