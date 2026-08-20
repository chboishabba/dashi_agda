module DASHI.Moonshine.P11MarkedQuaternionHeckeHighestAlphaRegression where

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11VoightNonprincipalLeftOrderExact as J0Order
import DASHI.Moonshine.P11MarkedQuaternionThetaExact as Theta
import DASHI.Moonshine.P11MarkedRefinedThetaCrossCheckExact as Theta2
import DASHI.Moonshine.P11Level2DoubleCosetHeckeBasisExact as Orbital
import DASHI.Moonshine.P11MarkedX2HeckeReconstructionExact as Marked
import DASHI.Moonshine.P11MarkedX2HeckeAlgebraExact as Algebra
import DASHI.Moonshine.P11MarkedX2PrimeSquareNeighboursExact as Squares
import DASHI.Moonshine.P11MarkedX2FrobeniusFrickeExact as FF
import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact as S3Hecke
import DASHI.Moonshine.P37NonOggFullLevel2DeuringControlExact as P37

------------------------------------------------------------------------
-- Exact p=11 quaternion-order / theta frontier regression.
------------------------------------------------------------------------

j0LeftOrderReducedDiscriminantEleven : J0Order.reducedDiscriminant ≡ 11
j0LeftOrderReducedDiscriminantEleven = J0Order.reducedDiscriminantIsEleven

rawFourCellThetaTable :
  Theta.rawThetaTable Theta.ell3 ≡ (2 , 0)
  × Theta.rawThetaTable Theta.ell5 ≡ (0 , 4)
rawFourCellThetaTable = Theta.rawThetaEll3IsTwoZero , Theta.rawThetaEll5IsZeroFour

markedFourCellLoopTable :
  Theta.markedLoopTable Theta.ell3 ≡ (1 , 0)
  × Theta.markedLoopTable Theta.ell5 ≡ (0 , 2)
markedFourCellLoopTable = Theta.markedLoopEll3IsOneZero , Theta.markedLoopEll5IsZeroTwo

secondThetaPathAgrees :
  Theta2.markedThetaCoefficient Theta.ell3 ≡ Theta.markedLoopTable Theta.ell3
  × Theta2.markedThetaCoefficient Theta.ell5 ≡ Theta.markedLoopTable Theta.ell5
secondThetaPathAgrees = Theta2.markedThetaEll3Agrees , Theta2.markedThetaEll5Agrees

------------------------------------------------------------------------
-- Corrected orbital coefficients explicitly differ from both old hand models.
------------------------------------------------------------------------

correctedT3OrbitalVector :
  Marked.markedT3OrbitalCoefficients ≡ Orbital.orbitalCoefficients 1 0 1 1 0 1
correctedT3OrbitalVector = refl

correctedT5OrbitalVector :
  Marked.markedT5OrbitalCoefficients ≡ Orbital.orbitalCoefficients 0 3 1 1 2 1
correctedT5OrbitalVector = refl

correctedT3IsNotOldR3 :
  Marked.markedT3OrbitalCoefficients ≡ Orbital.r3OrbitalCoefficients → ⊥
correctedT3IsNotOldR3 ()

correctedT5IsNotOldR5 :
  Marked.markedT5OrbitalCoefficients ≡ Orbital.r5OrbitalCoefficients → ⊥
correctedT5IsNotOldR5 ()

------------------------------------------------------------------------
-- Corrected marked algebra remains positive and unital.
------------------------------------------------------------------------

correctedT3T5Commute :
  Algebra.correctedT3T5Commute Algebra.canonicalP11MarkedX2HeckeAlgebraBoundary ≡ true
correctedT3T5Commute =
  Algebra.correctedT3T5CommuteIsTrue Algebra.canonicalP11MarkedX2HeckeAlgebraBoundary

correctedPrimeSquaresUseTrueIdentity :
  Squares.correctedT3SquareUsesTrueIdentity Squares.canonicalP11MarkedX2PrimeSquareBoundary ≡ true
  × Squares.correctedT5SquareUsesTrueIdentity Squares.canonicalP11MarkedX2PrimeSquareBoundary ≡ true
correctedPrimeSquaresUseTrueIdentity = refl , refl

correctedHeckeFrobeniusEquivariant :
  FF.correctedT3T5FrobeniusEquivariant FF.canonicalP11MarkedX2FrobeniusFrickeBoundary ≡ true
correctedHeckeFrobeniusEquivariant =
  FF.correctedT3T5FrobeniusEquivariantIsTrue FF.canonicalP11MarkedX2FrobeniusFrickeBoundary

------------------------------------------------------------------------
-- Representation information not recoverable from the current joint spectrum.
------------------------------------------------------------------------

brandtStandardObservationCollision :
  S3Hecke.brandtNewformFingerprint ≡ S3Hecke.standardFingerprint
brandtStandardObservationCollision = S3Hecke.brandtAndStandardFingerprintsCoincide

------------------------------------------------------------------------
-- Cross-prime full-level-2 control.
--
-- p=11 marked Frobenius: three fixed rational lambda points + one conjugate pair.
-- p=37 marked Frobenius: zero fixed points + nine conjugate pairs.
------------------------------------------------------------------------

p11MarkedFrobeniusFixedCount : Nat
p11MarkedFrobeniusFixedCount = 3

p11MarkedFrobeniusPairCount : Nat
p11MarkedFrobeniusPairCount = 1

p37MarkedFrobeniusFixedCount : Nat
p37MarkedFrobeniusFixedCount = 0

p37MarkedFrobeniusPairCount : Nat
p37MarkedFrobeniusPairCount = P37.p37MarkedFrobeniusPairCount

p11VsP37MarkedFrobeniusSignature :
  (p11MarkedFrobeniusFixedCount , p11MarkedFrobeniusPairCount)
  ≡ (3 , 1)
  ×
  (p37MarkedFrobeniusFixedCount , p37MarkedFrobeniusPairCount)
  ≡ (0 , 9)
p11VsP37MarkedFrobeniusSignature = refl , refl

p37MarkedCarrierCountIsEighteen : P37.p37FullLevel2StateCount ≡ 18
p37MarkedCarrierCountIsEighteen = P37.p37FullLevel2StateCountIsEighteen

p37HasNoMarkedFrobeniusFixedPoint :
  (x : P37.P37SupersingularLambda) → P37.p37MarkedFrobenius x ≡ x → ⊥
p37HasNoMarkedFrobeniusFixedPoint = P37.p37MarkedFrobeniusHasNoFixedPoint
