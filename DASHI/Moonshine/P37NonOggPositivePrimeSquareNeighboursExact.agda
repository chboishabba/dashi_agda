module DASHI.Moonshine.P37NonOggPositivePrimeSquareNeighboursExact where

------------------------------------------------------------------------
-- SOURCE CONTEXT
--
-- Extends `P37NonOggPositiveHeckeControlExact` using only the source T2 matrix
-- from SageMath's supersingular-module documentation plus the weight-two Hecke
-- relation T2^2 = T4 + 2 I.
--
-- DASHI CONTRIBUTION
--
-- Replace the positive residual matrix by a literal seven-neighbour system.
-- Therefore the non-Ogg p=37 control survives the same set-level prime-square
-- positivity gate used by the p=11 five-state model.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)

import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive
import DASHI.Moonshine.BrandtStackUnweightingControlsExact as Controls
import DASHI.Moonshine.P37NonOggPositiveHeckeControlExact as P37

p37T4Neighbour : Controls.P37BrandtClass → Fin 7 → Controls.P37BrandtClass
p37T4Neighbour Controls.p37c0 zero = Controls.p37c0
p37T4Neighbour Controls.p37c0 (suc zero) = Controls.p37c1
p37T4Neighbour Controls.p37c0 (suc (suc zero)) = Controls.p37c1
p37T4Neighbour Controls.p37c0 (suc (suc (suc zero))) = Controls.p37c1
p37T4Neighbour Controls.p37c0 (suc (suc (suc (suc zero)))) = Controls.p37c2
p37T4Neighbour Controls.p37c0 (suc (suc (suc (suc (suc zero))))) = Controls.p37c2
p37T4Neighbour Controls.p37c0 (suc (suc (suc (suc (suc (suc zero)))))) = Controls.p37c2

p37T4Neighbour Controls.p37c1 zero = Controls.p37c0
p37T4Neighbour Controls.p37c1 (suc zero) = Controls.p37c0
p37T4Neighbour Controls.p37c1 (suc (suc zero)) = Controls.p37c0
p37T4Neighbour Controls.p37c1 (suc (suc (suc zero))) = Controls.p37c1
p37T4Neighbour Controls.p37c1 (suc (suc (suc (suc zero)))) = Controls.p37c1
p37T4Neighbour Controls.p37c1 (suc (suc (suc (suc (suc zero))))) = Controls.p37c1
p37T4Neighbour Controls.p37c1 (suc (suc (suc (suc (suc (suc zero)))))) = Controls.p37c2

p37T4Neighbour Controls.p37c2 zero = Controls.p37c0
p37T4Neighbour Controls.p37c2 (suc zero) = Controls.p37c0
p37T4Neighbour Controls.p37c2 (suc (suc zero)) = Controls.p37c0
p37T4Neighbour Controls.p37c2 (suc (suc (suc zero))) = Controls.p37c1
p37T4Neighbour Controls.p37c2 (suc (suc (suc (suc zero)))) = Controls.p37c2
p37T4Neighbour Controls.p37c2 (suc (suc (suc (suc (suc zero))))) = Controls.p37c2
p37T4Neighbour Controls.p37c2 (suc (suc (suc (suc (suc (suc zero)))))) = Controls.p37c2

P37R4 : Positive.PositiveFiniteNeighbourSystem Controls.P37BrandtClass
P37R4 =
  record
    { Positive.arity = 7
    ; Positive.neighbour = p37T4Neighbour
    }

p37R4Count : Controls.P37BrandtClass → Controls.P37BrandtClass → Nat
p37R4Count source Controls.p37c0 = Positive.positiveOperator P37R4 P37.isC0 source
p37R4Count source Controls.p37c1 = Positive.positiveOperator P37R4 P37.isC1 source
p37R4Count source Controls.p37c2 = Positive.positiveOperator P37R4 P37.isC2 source

p37R4MatchesResidual :
  (source target : Controls.P37BrandtClass) →
  p37R4Count source target ≡ P37.p37T4Residual source target
p37R4MatchesResidual Controls.p37c0 Controls.p37c0 = refl
p37R4MatchesResidual Controls.p37c0 Controls.p37c1 = refl
p37R4MatchesResidual Controls.p37c0 Controls.p37c2 = refl
p37R4MatchesResidual Controls.p37c1 Controls.p37c0 = refl
p37R4MatchesResidual Controls.p37c1 Controls.p37c1 = refl
p37R4MatchesResidual Controls.p37c1 Controls.p37c2 = refl
p37R4MatchesResidual Controls.p37c2 Controls.p37c0 = refl
p37R4MatchesResidual Controls.p37c2 Controls.p37c1 = refl
p37R4MatchesResidual Controls.p37c2 Controls.p37c2 = refl

p37SetLevelPrimeSquareRelation :
  (source target : Controls.P37BrandtClass) →
  P37.twoStepCount target source
  ≡ p37R4Count source target + 2 * P37.identityMultiplicity source target
p37SetLevelPrimeSquareRelation source target
  rewrite p37R4MatchesResidual source target
  = P37.p37T2SquareRelation source target

record P37PrimeSquareNeighbourBoundary : Set where
  field
    positiveR4NeighbourSystemConstructed : Bool
    positiveR4NeighbourSystemConstructedIsTrue :
      positiveR4NeighbourSystemConstructed ≡ true

    setLevelPrimeSquareRelationConstructed : Bool
    setLevelPrimeSquareRelationConstructedIsTrue :
      setLevelPrimeSquareRelationConstructed ≡ true

    nonOggControlSurvivesP11PositivityGate : Bool
    nonOggControlSurvivesP11PositivityGateIsTrue :
      nonOggControlSurvivesP11PositivityGate ≡ true

canonicalP37PrimeSquareNeighbourBoundary : P37PrimeSquareNeighbourBoundary
canonicalP37PrimeSquareNeighbourBoundary =
  record
    { positiveR4NeighbourSystemConstructed = true
    ; positiveR4NeighbourSystemConstructedIsTrue = refl
    ; setLevelPrimeSquareRelationConstructed = true
    ; setLevelPrimeSquareRelationConstructedIsTrue = refl
    ; nonOggControlSurvivesP11PositivityGate = true
    ; nonOggControlSurvivesP11PositivityGateIsTrue = refl
    }
