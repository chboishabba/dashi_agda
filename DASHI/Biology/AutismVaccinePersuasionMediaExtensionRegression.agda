module DASHI.Biology.AutismVaccinePersuasionMediaExtensionRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.AutismVaccinePersuasionMediaExtensionExact as P

nyhanTrialRetained : P.nyhanTrialRepresented P.canonicalPersuasionMediaBoundary ≡ true
nyhanTrialRetained = refl

universalBackfireRejected : P.universalBackfireLawPaid P.canonicalPersuasionMediaBoundary ≡ false
universalBackfireRejected = refl

correctionAccuracyEvidenceRetained :
  P.correctionUsuallyImprovesAccuracyRepresented P.canonicalPersuasionMediaBoundary ≡ true
correctionAccuracyEvidenceRetained = refl

accuracyNotIntent : P.accuracyCollapsedWithIntent P.canonicalPersuasionMediaBoundary ≡ false
accuracyNotIntent = refl

intentNotBehaviour : P.intentCollapsedWithBehaviour P.canonicalPersuasionMediaBoundary ≡ false
intentNotBehaviour = refl

mediaNarrativeNotCausalLaw : P.mediaNarrativePromotedToCausalLaw P.canonicalPersuasionMediaBoundary ≡ false
mediaNarrativeNotCausalLaw = refl

truthSeparatedFromPropagation : P.propositionTruthSeparatedFromPropagation P.canonicalPersuasionMediaBoundary ≡ true
truthSeparatedFromPropagation = refl

exposureToBeliefNotAutomatic : P.automatic P.exposureToBelief ≡ false
exposureToBeliefNotAutomatic = refl

beliefToIntentNotAutomatic : P.automatic P.beliefToIntent ≡ false
beliefToIntentNotAutomatic = refl

intentToBehaviourNotAutomatic : P.automatic P.intentToBehaviour ≡ false
intentToBehaviourNotAutomatic = refl
