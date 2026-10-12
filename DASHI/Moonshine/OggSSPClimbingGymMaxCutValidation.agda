module DASHI.Moonshine.OggSSPClimbingGymMaxCutValidation where

open import DASHI.Core.Prelude

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.RadixValuationStageBridge as Radix
import DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact as SignedBranch
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.OggSSPSignedRadixClimbingGymExact as Gym
import DASHI.Moonshine.OggSSPClimbingGymFigureObservationExact as Figure

------------------------------------------------------------------------
-- TDD regression contract.
------------------------------------------------------------------------

p2RadixIsTwo :
  Radix.radix (Gym.oggPrimeRadixChart Lane.p2) ≡ 2
p2RadixIsTwo = refl

p71RadixIsSeventyOne :
  Radix.radix (Gym.oggPrimeRadixChart Lane.p71) ≡ 71
p71RadixIsSeventyOne = refl

signedCarrierBridgeReusedAtP47 :
  SignedBranch.lanePrimeToSignedPrime Lane.p47 ≡ Signed.ssp47
signedCarrierBridgeReusedAtP47 = refl

coarseningCommutesWithSignedNegation :
  ∀ {depth}
    (state : Gym.SignedRadixWallState (suc depth)) →
  Gym.coarsenSignedRadixWall (Gym.negateSignedRadixWall state)
  ≡
  Gym.negateSignedRadixWall (Gym.coarsenSignedRadixWall state)
coarseningCommutesWithSignedNegation =
  Gym.coarsenNegationCommutes

p2FirstFormNIsTwo :
  Gym.wallFormN Gym.p2Exponent1 ≡ 2
p2FirstFormNIsTwo = refl

p2SquaredFormNIsFour :
  Gym.wallFormN Gym.p2Exponent2 ≡ 4
p2SquaredFormNIsFour = refl

p3SquaredFormNIsNine :
  Gym.wallFormN Gym.p3Exponent2 ≡ 9
p3SquaredFormNIsNine = refl

p2CubedFormNIsEight :
  Gym.wallFormN Gym.p2Exponent3 ≡ 8
p2CubedFormNIsEight = refl

figureZeroCountIs849 :
  Figure.figureZeroCount ≡ 849
figureZeroCountIs849 = refl

p11FigureSaturates :
  Figure.mutualPairs Figure.p11Exponent1Row ≡ Figure.figureZeroCount
p11FigureSaturates = refl

p13FigureSaturates :
  Figure.mutualPairs Figure.p13Exponent1Row ≡ Figure.figureZeroCount
p13FigureSaturates = refl

p71FigureSaturates :
  Figure.mutualPairs Figure.p71Exponent1Row ≡ Figure.figureZeroCount
p71FigureSaturates = refl

figurePrimeLaneIsTypedCanonical :
  (row : Figure.ClimbingGymFigureRow) →
  Lane.MonsterPrimeLane
figurePrimeLaneIsTypedCanonical = Figure.figureLane

boundaryKeepsAddressAndSignedFlowDistinct :
  Gym.signedValuationIsRadixAddress
    Gym.canonicalOggSSPSignedRadixClimbingGymBoundary
  ≡ false
boundaryKeepsAddressAndSignedFlowDistinct = refl

boundaryKeepsObservationOutOfRHPromotion :
  Figure.figureObservationProvesZetaZeroParametrisation
    Figure.canonicalClimbingGymFigureObservationBoundary
  ≡ false
boundaryKeepsObservationOutOfRHPromotion = refl
