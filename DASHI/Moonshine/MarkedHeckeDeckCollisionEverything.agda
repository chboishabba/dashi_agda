module DASHI.Moonshine.MarkedHeckeDeckCollisionEverything where

------------------------------------------------------------------------
-- Focused aggregate for the next marked-Hecke / deck-observer tranche.
--
-- p=11:
--   direct E(F_7) point count
--     -> a_7 = -2
--     -> direct quaternion marked norm-seven theta loops
--     -> positive marked T7 orbital correspondence
--     -> Brandt-newform / deck-standard collision survives T7
--     -> all-prime collision reduced to one marked theta identity.
--
-- p=37:
--   actual 18-root Legendre T3/T5/F carrier
--     -> two distinct observables with identical (T3,T5,F)=(1,0,+1)
--     -> one is deck invariant, one is moved by deck C3
--     -> scalar Hecke/Frobenius observation is not deck separating.
--
-- Generic algebra:
--   if the marked space is genuinely identified as
--       global Hecke factor x auxiliary deck factor
--   and prime-to-level Hecke acts on the global coordinate only, then the
--   entire prime-to-level Hecke family is necessarily blind to deck type.
--
-- No module here promotes the finite p=11 prime scan to an all-prime theorem,
-- nor does it assert that the actual p=11 carrier has already been proved to
-- possess the required global x deck product factorization.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11Level11Ell7PointCountExact as Point7
import DASHI.Moonshine.P11MarkedQuaternionThetaEll7Exact as Theta7
import DASHI.Moonshine.P11MarkedX2T7HeckeCollisionExact as T7
import DASHI.Moonshine.P11MarkedHeckeThetaCollisionCriterionExact as Criterion
import DASHI.Moonshine.P37NonOggFullLevel2DeuringControlExact as P37
import DASHI.Moonshine.P37MarkedX2JointFingerprintDeckCollisionExact as P37Collision
import DASHI.Moonshine.AuxiliaryLevelHeckeDeckFactorizationExact as Aux

------------------------------------------------------------------------
-- Regression witnesses consume actual theorem surfaces rather than receipt
-- booleans.
------------------------------------------------------------------------

p11PointCountTenRegression : Point7.projectivePointCount ≡ 10
p11PointCountTenRegression = Point7.projectivePointCountIsTen

p11ThetaSevenRegression : Theta7.markedT7LoopTable ≡ (2 , 0)
p11ThetaSevenRegression = Theta7.markedT7LoopTableIsTwoZero

p11T7CollisionRegression :
  T7.brandt357FFingerprint ≡ T7.standard357FFingerprint
p11T7CollisionRegression = T7.brandtAndStandardStillCollideAtT7

p11ThetaCriterionEll7Regression :
  Criterion.DifferenceEquivalent
    (Criterion.standardDeckDifference Theta7.j1728MarkedT7LoopCount 2)
    (Criterion.coarseNonconstantDifference 8 2)
p11ThetaCriterionEll7Regression = Criterion.ell7DeckBrandtDifferenceCollision

p37CoarseFingerprintRegression :
  (x : P37.P37SupersingularLambda) →
  P37Collision.t3Action P37Collision.coarseEvenObserver x
  ≡ P37Collision.coarseEvenObserver x
p37CoarseFingerprintRegression = P37Collision.coarseEvenT3Eigen

p37DeckMovingFingerprintRegression :
  (x : P37.P37SupersingularLambda) →
  P37Collision.t3Action P37Collision.deckMovingEvenObserver x
  ≡ P37Collision.deckMovingEvenObserver x
p37DeckMovingFingerprintRegression = P37Collision.deckMovingEvenT3Eigen

-- The generic auxiliary-level mechanism remains reusable but does not identify
-- the arithmetic carrier automatically.
auxiliaryLevelBoundaryRegression :
  Aux.p11SameObjectProductFactorizationClaimedHere
    Aux.canonicalAuxiliaryLevelHeckeDeckBoundary ≡ false
auxiliaryLevelBoundaryRegression = refl
