module DASHI.Unified.TOEGaugeInhabitantsValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.TOEConcreteInhabitantsExact as Inhabitants
import DASHI.Unified.TOEGaugeInhabitantsExact as GaugeInhabitants

hodgeCrossIsFormalInhabitant :
  Inhabitants.authority GaugeInhabitants.agda1164HodgeCrossInhabitant
  ≡ Inhabitants.importedFormalInhabitant
hodgeCrossIsFormalInhabitant = refl

u1SU2IsFormalInhabitant :
  Inhabitants.authority GaugeInhabitants.agda1164U1SU2TorusInhabitant
  ≡ Inhabitants.importedFormalInhabitant
u1SU2IsFormalInhabitant = refl

brownMaclayStressIsFormalInhabitant :
  Inhabitants.authority GaugeInhabitants.agda1165BrownMaclayStressInhabitant
  ≡ Inhabitants.importedFormalInhabitant
brownMaclayStressIsFormalInhabitant = refl
