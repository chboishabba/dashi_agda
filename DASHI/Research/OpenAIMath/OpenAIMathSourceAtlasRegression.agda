module DASHI.Research.OpenAIMath.OpenAIMathSourceAtlasRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Research.OpenAIMath.OpenAIMathSourceAtlasExact

_ : RoutedSource.familyId quasiRiemann ≡ "003"
_ = refl

_ : RoutedSource.declaration quasiRiemann ≡ "OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re"
_ = refl

_ : RoutedSource.familyId uniqueGamesMaxCut ≡ "102"
_ = refl

_ : RoutedSource.familyId relativisticVlasovMaxwell ≡ "362"
_ = refl

_ : RoutedSource.familyId forcedNavierStokesComputation ≡ "376"
_ = refl

_ : RoutedSource.provesFullRiemannHypothesis quasiRiemann ≡ false
_ = refl

_ : RoutedSource.provesPNotEqualsNP uniqueGamesMaxCut ≡ false
_ = refl

_ : RoutedSource.provesClayNavierStokes forcedNavierStokesComputation ≡ false
_ = refl

_ : RoutedSource.provesGeneralHodgeConjecture hodgeCM ≡ false
_ = refl

_ : RoutedSource.provesGeneralBSD bsdLowSelmer ≡ false
_ = refl
