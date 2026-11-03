{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkSignUnderdeterminationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- SIGN UNDERDETERMINATION
--
-- Birthmark persistence is a statement that history-sensitive residual data can
-- survive coarse equilibration.  It carries no sign of a metric variation by
-- itself.  This finite witness exhibits the same persistent-history flag with
-- opposite selected effective-action signs.
------------------------------------------------------------------------

data EffectiveVariationSign : Set where
  negativeVariation : EffectiveVariationSign
  zeroVariation : EffectiveVariationSign
  positiveVariation : EffectiveVariationSign

record PersistentHistorySignModel : Set where
  constructor persistent-history-sign-model
  field
    historyPersists : Bool
    selectedVariationSign : EffectiveVariationSign

open PersistentHistorySignModel public

negativeSignModel : PersistentHistorySignModel
negativeSignModel = persistent-history-sign-model true negativeVariation

positiveSignModel : PersistentHistorySignModel
positiveSignModel = persistent-history-sign-model true positiveVariation

samePersistenceOppositeSignWitness :
  historyPersists negativeSignModel ≡ historyPersists positiveSignModel
samePersistenceOppositeSignWitness = refl

persistentHistoryForcesUniqueVariationSign : Bool
persistentHistoryForcesUniqueVariationSign = false

birthmarkPersistenceAloneFixesEq223Sign : Bool
birthmarkPersistenceAloneFixesEq223Sign = false

birthmarkPersistenceAloneFixesDarkEnergyEquationOfState : Bool
birthmarkPersistenceAloneFixesDarkEnergyEquationOfState = false

sourceDynamicsNeededToChooseSign : Bool
sourceDynamicsNeededToChooseSign = true
