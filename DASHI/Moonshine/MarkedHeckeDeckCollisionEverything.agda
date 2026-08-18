module DASHI.Moonshine.MarkedHeckeDeckCollisionEverything where

------------------------------------------------------------------------
-- Focused aggregate for marked-Hecke / deck-observer collision and selector
-- cutset work.
--
-- p=11:
--   direct E(F_7) point count
--     -> a_7 = -2
--     -> direct quaternion marked norm-seven theta loops
--     -> positive marked T7 orbital correspondence
--     -> Brandt-newform / deck-standard collision survives T7
--     -> level-44 oldspace fingerprint
--     -> literal integral three-copy permutation basis in the marked carrier
--     -> one Z-linear realization intertwines deck S3 and T3/T5/T7.
--
-- p=37:
--   actual 18-root Legendre T3/T5/F carrier
--     -> source-native 3 x regular-S3 orbital presentation
--     -> complete right-deck isotypic decomposition 3 + 3 + 12
--     -> explicit trivial/sign 3x3 blocks and standard 6x6 multiplicity block
--     -> structural trivial-vs-standard collision at (T3,T5,F)=(1,0,+1)
--     -> exact T3 annihilator and theorem-level T5(T3), F(T3) polynomials
--     -> deck type repairs the scalar observation.
--
-- p=43:
--   independent Deuring/full-level-2 control with nontrivial stabilizer
--     -> 21 marked points = 3 fixed + 9 Frobenius pairs
--     -> four coarse j classes = 2 fixed + 1 pair
--     -> explicit normal-form realization of the SAME coarse defect=1 that the
--        finite Fricke/class-number spectrum predicts.
--
-- Cross-prime selector cutset:
--   scalar Hecke/Frobenius blindness to deck type occurs at BOTH p=11 and the
--   non-Ogg control p=37, so deck refinement is representation-relevant but is
--   not itself an Ogg selector.  The first currently surviving selector
--   coordinate is the COARSE geometric Frobenius paired-orbit defect:
--
--       p11 = 0, p37 = 1, p43 = 1.
--
-- The remaining p=11 global producer is no longer "try another prime": it is
-- the same-object identification of the actual marked three-copy permutation
-- module with the analytic level-11 oldspace inside level 44.  The finite map
-- on the marked side is now constructed and carries both deck and Hecke
-- commuting squares.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (-[1+_])
open import Data.Rational using (_/_)

import DASHI.Moonshine.P11Level11Ell7PointCountExact as Point7
import DASHI.Moonshine.P11MarkedQuaternionThetaEll7Exact as Theta7
import DASHI.Moonshine.P11MarkedX2T7HeckeCollisionExact as T7
import DASHI.Moonshine.P11MarkedHeckeThetaCollisionCriterionExact as Criterion
import DASHI.Moonshine.P11Ell7PointCountBrandtTraceExact as Trace7
import DASHI.Moonshine.P11MarkedLevel44OldspaceWeldExact as P11Old
import DASHI.Moonshine.P11MarkedLevel44PermutationOldspaceExact as P11PermOld
import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as P11OldInt
import DASHI.Moonshine.P37NonOggFullLevel2DeuringControlExact as P37
import DASHI.Moonshine.P37MarkedX2JointFingerprintDeckCollisionExact as P37Collision
import DASHI.Moonshine.P37MarkedDeckIsotypicJointDecompositionExact as P37Iso
import DASHI.Moonshine.P37MarkedDeckIsotypicPolynomialExact as P37Poly
import DASHI.Moonshine.P37MarkedDeckIsotypicCollisionExact as P37IsoCollision
import DASHI.Moonshine.P43NonOggFullLevel2DeuringControlExact as P43
import DASHI.Moonshine.P43GeometricFrobeniusRealizationExact as P43Geo
import DASHI.Moonshine.P11P37MarkedDeckSelectorCutsetExact as SelectorCutset
import DASHI.Moonshine.P37MarkedDeckIsotypicHighestAlphaRegression as P37Regression
import DASHI.Moonshine.AuxiliaryLevelHeckeDeckFactorizationExact as Aux
import DASHI.Moonshine.AuxiliaryLevelHeckeObserverNoGoExact as ObserverNoGo

------------------------------------------------------------------------
-- p=11 arithmetic and T7 regression.
------------------------------------------------------------------------

p11PointCountTenRegression : Point7.projectivePointCount ≡ 10
p11PointCountTenRegression = Point7.projectivePointCountIsTen

p11ThetaSevenRegression : Theta7.markedT7LoopTable ≡ (2 , 0)
p11ThetaSevenRegression = Theta7.markedT7LoopTableIsTwoZero

p11DirectPointCountTraceRegression :
  Criterion.DifferenceEquivalent
    (Criterion.coarseNonconstantDifference T7.p11Ell7Degree T7.p11Ell7CrossUnit)
    (Criterion.natDifference 0 Point7.a7NegativeMagnitude)
p11DirectPointCountTraceRegression = Trace7.ell7CoarseBrandtDifferenceIsPointCountTrace

p11T7CollisionRegression :
  T7.brandt357FFingerprint ≡ T7.standard357FFingerprint
p11T7CollisionRegression = T7.brandtAndStandardStillCollideAtT7

p11ThetaCriterionEll7Regression :
  Criterion.DifferenceEquivalent
    (Criterion.standardDeckDifference Theta7.j1728MarkedT7LoopCount 2)
    (Criterion.coarseNonconstantDifference 8 2)
p11ThetaCriterionEll7Regression = Criterion.ell7DeckBrandtDifferenceCollision

------------------------------------------------------------------------
-- p=11 level-44 permutation oldspace: actual deck + Hecke commuting maps.
------------------------------------------------------------------------

p11OldPermutationDeckRRegression :
  (copy : P11Old.OldCopy44) →
  P11PermOld.deckR5 (P11PermOld.oldCopyVector copy)
  ≡ P11PermOld.oldCopyVector (P11Old.oldDeckR copy)
p11OldPermutationDeckRRegression = P11PermOld.oldCopyDeckRIntertwines

p11OldModuleT7IntertwinerRegression :
  (v : P11OldInt.Old3) →
  T7.markedT7Action (P11OldInt.realizeOld3 v)
  ≡ P11OldInt.realizeOld3 (P11OldInt.scaleOld3 (-[1+ 1 ]) v)
p11OldModuleT7IntertwinerRegression = P11OldInt.realizeT7

------------------------------------------------------------------------
-- p37 witness-level collision remains intact.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Complete p37 deck-isotypic compression and polynomial closure.
------------------------------------------------------------------------

p37DeckDimensionsRegression :
  P37Iso.trivialDeckDimension + P37Iso.signDeckDimension + P37Iso.standardDeckIsotypicDimension
  ≡ 18
p37DeckDimensionsRegression = P37Iso.isotypicDimensionsSumToEighteen

p37StandardIsotypicTwoCopiesRegression :
  2 * P37Iso.standardMultiplicityDimension ≡ P37Iso.standardDeckIsotypicDimension
p37StandardIsotypicTwoCopiesRegression = P37Iso.standardIsotypicIsTwoMultiplicityCopies

p37StandardT5PolynomialRegression :
  (x : P37Iso.StdBlock3) →
  P37Poly.scaleStd (34 / 1) (P37Iso.standardT5 x)
  ≡ P37Poly.t5Polynomial x
p37StandardT5PolynomialRegression = P37Poly.standardT5PolynomialExact

p37StandardT3AnnihilatorRegression :
  (x : P37Iso.StdBlock3) →
  P37Poly.linearOne
    (P37Poly.linearNegThree
      (P37Poly.quadraticA (P37Poly.quadraticB x)))
  ≡ P37Poly.zeroStd
p37StandardT3AnnihilatorRegression = P37Poly.standardT3FactorizedAnnihilatorExact

p37StructuralScalarCollisionRegression :
  P37IsoCollision.p37TrivialFingerprint ≡ P37IsoCollision.p37StandardFingerprint
p37StructuralScalarCollisionRegression = P37IsoCollision.p37ArithmeticFingerprintsCoincide

p37StructuralDeckRepairRegression :
  P37IsoCollision.p37TrivialRefined ≡ P37IsoCollision.p37StandardRefined → ⊥
p37StructuralDeckRepairRegression = P37IsoCollision.p37DeckRefinementSeparates

------------------------------------------------------------------------
-- p43 second independent non-Ogg geometric control.
------------------------------------------------------------------------

p43MarkedCountRegression : P43.p43MarkedStateCount ≡ 21
p43MarkedCountRegression = P43.p43MarkedStateCountIsTwentyOne

p43CoarsePairRegression : P43.p43CoarsePairCount ≡ 1
p43CoarsePairRegression = P43.p43CoarsePairCountIsOne

p43GenericDefectRealizedGeometrically :
  SelectorCutset.p43CoarseFrobeniusPairDefect ≡ 1
p43GenericDefectRealizedGeometrically = SelectorCutset.p43DefectOne

p11P37FrobeniusDefectSelectorRegression :
  SelectorCutset.p11CoarseFrobeniusPairDefect
  ≡ SelectorCutset.p37CoarseFrobeniusPairDefect → ⊥
p11P37FrobeniusDefectSelectorRegression =
  SelectorCutset.coarseFrobeniusPairDefectSeparates11And37

p11P43FrobeniusDefectSelectorRegression :
  SelectorCutset.p11CoarseFrobeniusPairDefect
  ≡ SelectorCutset.p43CoarseFrobeniusPairDefect → ⊥
p11P43FrobeniusDefectSelectorRegression =
  SelectorCutset.coarseFrobeniusPairDefectSeparates11And43

------------------------------------------------------------------------
-- Product-factorization remains a boundary, not a false p37 identification.
------------------------------------------------------------------------

auxiliaryLevelBoundaryRegression :
  Aux.p11SameObjectProductFactorizationClaimedHere
    Aux.canonicalAuxiliaryLevelHeckeDeckBoundary ≡ false
auxiliaryLevelBoundaryRegression = refl

allPrimeObserverNoGoBoundaryRegression :
  ObserverNoGo.allPrimeBlindnessDerived
    ObserverNoGo.canonicalAuxiliaryHeckeObserverNoGoBoundary ≡ true
allPrimeObserverNoGoBoundaryRegression = refl
