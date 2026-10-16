module DASHI.Biology.IBSPersonalizationValidationRegression where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Biology.IBSPersonalizationValidationExact as P

atlasRegression : P.canonicalIBSPersonalizationValidationAtlas ≡ P.canonicalIBSPersonalizationValidationAtlas
atlasRegression = refl

personalizedNotSuperiorRegression : P.PersonalizedLabelImpliesSuperiorOutcomePermission → ⊥
personalizedNotSuperiorRegression = P.personalizedLabelDoesNotImplySuperiorOutcome

biomarkerNotSelectorRegression : P.MechanisticBiomarkerIsValidatedSelectorPermission → ⊥
biomarkerNotSelectorRegression = P.mechanisticBiomarkerDoesNotBecomeValidatedSelector

algorithmNotTransportRegression : P.InternalPersonalizationModelAutomaticallyTransportsPermission → ⊥
algorithmNotTransportRegression = P.internalPersonalizationModelDoesNotAutomaticallyTransport
