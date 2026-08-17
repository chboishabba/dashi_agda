module DASHI.Moonshine.AristotleDeltaObserverHighestAlphaRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_)
  renaming (_*_ to _*ℤ_; _-_ to _-ℤ_)

import DASHI.Moonshine.RamanujanTauHecke23Exact as Tau
import DASHI.Moonshine.DeltaAnalyticHeckeObservationSameObjectExact as Same
import DASHI.Moonshine.PaletteLeadingModeObserverExact as Palette

canonicalTauReadout : Same.DeltaCoefficientReadout
canonicalTauReadout = record
  { coefficient = Same.tauThreePowerReadout
  ; sameTauCoefficient = λ observation → refl
  }

canonicalReadout9Recurrence :
  Same.coefficientAt9 canonicalTauReadout
  ≡ Same.coefficientAt3 canonicalTauReadout
      *ℤ Same.coefficientAt3 canonicalTauReadout
      -ℤ Tau.pow3Eleven
canonicalReadout9Recurrence =
  Same.coefficient9HeckeRecurrence canonicalTauReadout

canonicalReadout27Recurrence :
  Same.coefficientAt27 canonicalTauReadout
  ≡
    (Same.coefficientAt3 canonicalTauReadout
      *ℤ Same.coefficientAt3 canonicalTauReadout
      *ℤ Same.coefficientAt3 canonicalTauReadout)
      -ℤ ((+ 2 *ℤ Tau.pow3Eleven)
            *ℤ Same.coefficientAt3 canonicalTauReadout)
canonicalReadout27Recurrence =
  Same.coefficient27HeckeRecurrence canonicalTauReadout

leadingResidualRoundTripRegression :
  Palette.decodeLeadingResidual
    (Palette.encodeLeadingResidual (Palette.leadingResidual 7 3))
  ≡ Palette.leadingResidual 7 3
leadingResidualRoundTripRegression =
  Palette.leadingResidualRoundTrip (Palette.leadingResidual 7 3)

coarseObserverReallyCollapsesFineStates :
  Palette.leadingObserver Palette.coarseState0
  ≡ Palette.leadingObserver Palette.coarseState1
coarseObserverReallyCollapsesFineStates = Palette.sameLeadingObservation

coarseObserverDoesNotProveFineIdentity :
  Palette.coarseState0 ≡ Palette.coarseState1 → ⊥
coarseObserverDoesNotProveFineIdentity =
  Palette.sameLeadingObservationDoesNotIdentifyFineState
