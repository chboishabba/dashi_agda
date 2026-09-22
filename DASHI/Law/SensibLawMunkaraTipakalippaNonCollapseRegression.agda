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

seaCountryContextStillCannotPayRegSeventeenSix :
  M.seaCountryContextPaysRegSeventeenSix
    M.canonicalMunkaraTipakalippaNonCollapseBoundary
  ≡ false
seaCountryContextStillCannotPayRegSeventeenSix = refl

tipakalippaConsultationStillCannotPayRegSeventeenSix :
  M.tipakalippaConsultationPaysRegSeventeenSix
    M.canonicalMunkaraTipakalippaNonCollapseBoundary
  ≡ false
tipakalippaConsultationStillCannotPayRegSeventeenSix = refl

exactMunkaraCoordinateMayStillPay :
  M.exactMunkaraRegSeventeenSixMayPay
    M.canonicalMunkaraTipakalippaNonCollapseBoundary
  ≡ true
exactMunkaraCoordinateMayStillPay = refl

wrongTypeRemainsMachineVisible :
  M.wrongTypeIsMachineVisible
    M.canonicalMunkaraTipakalippaNonCollapseBoundary
  ≡ true
wrongTypeRemainsMachineVisible = refl

adjacencyStillCannotPay :
  M.SeaCountryAdjacencyPaysRegSeventeenSix → ⊥
adjacencyStillCannotPay =
  M.seaCountryAdjacencyCannotPayRegSeventeenSix
