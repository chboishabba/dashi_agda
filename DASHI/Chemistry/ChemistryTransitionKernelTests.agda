module DASHI.Chemistry.ChemistryTransitionKernelTests where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Chemistry.ExistingContentBridge as Existing
import DASHI.Chemistry.Photography.InstantFilmSurface as Film
import DASHI.Chemistry.TransitionKernel as K

existingQuantitativePromotionRemainsClosed :
  Existing.ExistingChemistryBridge.physicalChemistryPromoted
    Existing.canonicalExistingChemistryBridge
  ≡ false
existingQuantitativePromotionRemainsClosed = refl

existingWetLabPromotionRemainsClosed :
  Existing.ExistingChemistryBridge.wetLabValidationAccepted
    Existing.canonicalExistingChemistryBridge
  ≡ false
existingWetLabPromotionRemainsClosed = refl

filmRecipeRecoveryRemainsClosed :
  Film.InstantFilmFormalisation.proprietaryRecipeRecovered
    Film.canonicalInstantFilmFormalisation
  ≡ false
filmRecipeRecoveryRemainsClosed = refl

filmWetLabPromotionRemainsClosed :
  Film.InstantFilmFormalisation.wetLabValidationAccepted
    Film.canonicalInstantFilmFormalisation
  ≡ false
filmWetLabPromotionRemainsClosed = refl

filmProcessWindowRemainsOpenObligation :
  Film.AlkaliTimingSurface.processWindowNonempty
    Film.canonicalTimingSurface
  ≡ false
filmProcessWindowRemainsOpenObligation = refl

filmMechanicsAreOptional :
  Film.OptionalSpreadMechanics.enabled
    Film.canonicalOptionalSpreadMechanics
  ≡ false
filmMechanicsAreOptional = refl

filmTransitionSystemIsCanonical :
  Film.InstantFilmFormalisation.transitionSystem
    Film.canonicalInstantFilmFormalisation
  ≡ Film.filmHybridSystem
filmTransitionSystemIsCanonical = refl
