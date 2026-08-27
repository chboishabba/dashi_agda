module DASHI.Analysis.RiemannHermitianEndgameTrichotomyExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- One typed dispatch surface for the three presently credible ways of crossing
-- the Alpöge--Furman second-moment error floor:
--
--   localization | higher-moment amplification | arithmetic rigidity.
--
-- A constructor is evidence: no route is manufactured merely because the
-- carrier has three cases.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

record EndgameSystem : Set₁ where
  field
    State : Set
    offLine : State → Set

open EndgameSystem public

record LocalizationCloser (s : EndgameSystem) : Set₁ where
  field
    closes : (x : State s) → offLine s x → ⊥

record HigherMomentCloser (s : EndgameSystem) : Set₁ where
  field
    closes : (x : State s) → offLine s x → ⊥

record ArithmeticRigidityCloser (s : EndgameSystem) : Set₁ where
  field
    closes : (x : State s) → offLine s x → ⊥

data EndgameAlternative (s : EndgameSystem) : Set₁ where
  localizationRoute : LocalizationCloser s → EndgameAlternative s
  higherMomentRoute : HigherMomentCloser s → EndgameAlternative s
  arithmeticRigidityRoute : ArithmeticRigidityCloser s → EndgameAlternative s

endgameAlternativeClosesOffLine :
  (s : EndgameSystem) →
  EndgameAlternative s →
  (x : State s) → offLine s x → ⊥
endgameAlternativeClosesOffLine s (localizationRoute c) x h =
  LocalizationCloser.closes c x h
endgameAlternativeClosesOffLine s (higherMomentRoute c) x h =
  HigherMomentCloser.closes c x h
endgameAlternativeClosesOffLine s (arithmeticRigidityRoute c) x h =
  ArithmeticRigidityCloser.closes c x h

record EndgameTrichotomyBoundary : Set where
  field
    threeRouteCarrierConstructed : Bool
    evidenceBearingDispatchClosed : Bool
    noRouteManufacturedFromEnumeration : Bool
    zetaLocalizationCloserConstructedHere : Bool
    zetaHigherMomentCloserConstructedHere : Bool
    zetaArithmeticRigidityCloserConstructedHere : Bool
    riemannHypothesisProvedHere : Bool

endgameTrichotomyBoundary : EndgameTrichotomyBoundary
endgameTrichotomyBoundary = record
  { threeRouteCarrierConstructed = true
  ; evidenceBearingDispatchClosed = true
  ; noRouteManufacturedFromEnumeration = true
  ; zetaLocalizationCloserConstructedHere = false
  ; zetaHigherMomentCloserConstructedHere = false
  ; zetaArithmeticRigidityCloserConstructedHere = false
  ; riemannHypothesisProvedHere = false
  }
