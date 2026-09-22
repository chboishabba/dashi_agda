module DASHI.Law.SensibLawMunkaraTipakalippaNonCollapseRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawMunkaraTipakalippaNonCollapseExact as M

seaCountryContextRemainsRelevant :
  M.seaCountryContextMayBeRelevant
    M.canonicalMunkaraTipakalippaNonCollapseBoundary
  ≡ true
seaCountryContextRemainsRelevant = refl

seaCountryContextStillCannotPayReg17_6 :
  M.seaCountryContextPaysReg17_6
    M.canonicalMunkaraTipakalippaNonCollapseBoundary
  ≡ false
seaCountryContextStillCannotPayReg17_6 = refl

tipakalippaConsultationStillCannotPayReg17_6 :
  M.tipakalippaConsultationPaysReg17_6
    M.canonicalMunkaraTipakalippaNonCollapseBoundary
  ≡ false
tipakalippaConsultationStillCannotPayReg17_6 = refl

exactMunkaraCoordinateMayStillPay :
  M.exactMunkaraReg17_6MayPay
    M.canonicalMunkaraTipakalippaNonCollapseBoundary
  ≡ true
exactMunkaraCoordinateMayStillPay = refl

wrongTypeRemainsMachineVisible :
  M.wrongTypeIsMachineVisible
    M.canonicalMunkaraTipakalippaNonCollapseBoundary
  ≡ true
wrongTypeRemainsMachineVisible = refl

adjacencyStillCannotPay :
  M.SeaCountryAdjacencyPaysReg17_6 → ⊥
adjacencyStillCannotPay =
  M.seaCountryAdjacencyCannotPayReg17_6
