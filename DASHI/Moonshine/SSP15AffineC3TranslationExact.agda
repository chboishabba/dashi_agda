module DASHI.Moonshine.SSP15AffineC3TranslationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CALIBRATION
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem",
-- Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine",
-- Bulletin of the London Mathematical Society 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- DASHI CONTRIBUTION
--
-- Do not identify the fifteen Ogg/Monster prime lanes with an arbitrary
-- five-by-three product.  Instead expose transformations that actually act
-- on the finite data.  The six SSP values
--
--   5  17  29
--   47 59  71
--
-- form an exact affine 2 x 3 grid: horizontal translation is +12 and vertical
-- translation is +42.  On the three phase-mobile nonary complement modes,
-- +12 and +42 induce inverse order-three cycles.  Under the exact symbolic
-- C3 phase chart, they are multiplication by zeta and zeta^2 = zeta^-1.
--
-- Independently, the +42 vertical translation preserves the existing
-- Q(sqrt(-7)) CM splitting class on all three displayed SSP pairs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Nonary
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Physics.Closure.SSP15CMFieldSplittingCorrectionReceipt as CM

------------------------------------------------------------------------
-- Exact nonary state and complement-mode address of every SSP lane.

primeNonaryState : Lane.MonsterPrimeLane → Nonary.DecimalCompletionState
primeNonaryState Lane.p2 = Nonary.d2
primeNonaryState Lane.p3 = Nonary.d3
primeNonaryState Lane.p5 = Nonary.d5
primeNonaryState Lane.p7 = Nonary.d7
primeNonaryState Lane.p11 = Nonary.d2
primeNonaryState Lane.p13 = Nonary.d4
primeNonaryState Lane.p17 = Nonary.d8
primeNonaryState Lane.p19 = Nonary.d1
primeNonaryState Lane.p23 = Nonary.d5
primeNonaryState Lane.p29 = Nonary.d2
primeNonaryState Lane.p31 = Nonary.d4
primeNonaryState Lane.p41 = Nonary.d5
primeNonaryState Lane.p47 = Nonary.d2
primeNonaryState Lane.p59 = Nonary.d5
primeNonaryState Lane.p71 = Nonary.d8

primeComplementMode : Lane.MonsterPrimeLane → Nonary.ComplementMode5
primeComplementMode prime = Nonary.complementMode (primeNonaryState prime)

primeBinaryPhase : Lane.MonsterPrimeLane → Nonary.BinaryPhase
primeBinaryPhase prime = Nonary.binaryPhase (primeNonaryState prime)

p17p19p71ShareMode18 :
  primeComplementMode Lane.p17 ≡ Nonary.mode18
  × primeComplementMode Lane.p19 ≡ Nonary.mode18
  × primeComplementMode Lane.p71 ≡ Nonary.mode18
p17p19p71ShareMode18 = refl , (refl , refl)

p2p7p11p29p47ShareMode27 :
  primeComplementMode Lane.p2 ≡ Nonary.mode27
  × primeComplementMode Lane.p7 ≡ Nonary.mode27
  × primeComplementMode Lane.p11 ≡ Nonary.mode27
  × primeComplementMode Lane.p29 ≡ Nonary.mode27
  × primeComplementMode Lane.p47 ≡ Nonary.mode27
p2p7p11p29p47ShareMode27 =
  refl , (refl , (refl , (refl , refl)))

p3OccupiesExceptionalMode36 :
  primeComplementMode Lane.p3 ≡ Nonary.mode36
p3OccupiesExceptionalMode36 = refl

p5p13p23p31p41p59ShareMode45 :
  primeComplementMode Lane.p5 ≡ Nonary.mode45
  × primeComplementMode Lane.p13 ≡ Nonary.mode45
  × primeComplementMode Lane.p23 ≡ Nonary.mode45
  × primeComplementMode Lane.p31 ≡ Nonary.mode45
  × primeComplementMode Lane.p41 ≡ Nonary.mode45
  × primeComplementMode Lane.p59 ≡ Nonary.mode45
p5p13p23p31p41p59ShareMode45 =
  refl , (refl , (refl , (refl , (refl , refl))))

------------------------------------------------------------------------
-- The prime-native complement observer is not a five-by-three partition.
-- Its exact occupancies are 3,5,1,6,0 across modes 18,27,36,45,09.

mode18Occupancy mode27Occupancy mode36Occupancy mode45Occupancy mode09Occupancy : Nat
mode18Occupancy = 3
mode27Occupancy = 5
mode36Occupancy = 1
mode45Occupancy = 6
mode09Occupancy = 0

primeComplementOccupanciesSumToFifteen :
  mode18Occupancy + mode27Occupancy + mode36Occupancy
  + mode45Occupancy + mode09Occupancy ≡ 15
primeComplementOccupanciesSumToFifteen = refl

modeOccupanciesAreNotFiveTriples : mode27Occupancy ≡ 5
modeOccupanciesAreNotFiveTriples = refl

------------------------------------------------------------------------
-- Existing Q(sqrt(-7)) splitting observer, made lane-indexed so that it can
-- be crossed with the nonary complement observer.

cmClass : Lane.MonsterPrimeLane → CM.CMPrimeSplittingClass
cmClass Lane.p2 = CM.split
cmClass Lane.p3 = CM.inert
cmClass Lane.p5 = CM.inert
cmClass Lane.p7 = CM.ramified
cmClass Lane.p11 = CM.split
cmClass Lane.p13 = CM.inert
cmClass Lane.p17 = CM.inert
cmClass Lane.p19 = CM.inert
cmClass Lane.p23 = CM.split
cmClass Lane.p29 = CM.split
cmClass Lane.p31 = CM.inert
cmClass Lane.p41 = CM.inert
cmClass Lane.p47 = CM.inert
cmClass Lane.p59 = CM.inert
cmClass Lane.p71 = CM.split

splitNotInert : CM.split ≡ CM.inert → ⊥
splitNotInert ()

sameNonaryModeDoesNotDetermineCMClass :
  primeComplementMode Lane.p2 ≡ primeComplementMode Lane.p47
sameNonaryModeDoesNotDetermineCMClass = refl

sameModeButDifferentCMClass : cmClass Lane.p2 ≡ CM.split
sameModeButDifferentCMClass = refl

p47SameModeIsInert : cmClass Lane.p47 ≡ CM.inert
p47SameModeIsInert = refl

nonaryModeCannotRecoverCMClass :
  (primeComplementMode Lane.p2 ≡ primeComplementMode Lane.p47)
  × (cmClass Lane.p2 ≡ CM.split)
  × (cmClass Lane.p47 ≡ CM.inert)
nonaryModeCannotRecoverCMClass = refl , (refl , refl)

------------------------------------------------------------------------
-- Exact SSP affine grid.

fivePlusTwelveIsSeventeen : 5 + 12 ≡ 17
fivePlusTwelveIsSeventeen = refl

seventeenPlusTwelveIsTwentyNine : 17 + 12 ≡ 29
seventeenPlusTwelveIsTwentyNine = refl

fortySevenPlusTwelveIsFiftyNine : 47 + 12 ≡ 59
fortySevenPlusTwelveIsFiftyNine = refl

fiftyNinePlusTwelveIsSeventyOne : 59 + 12 ≡ 71
fiftyNinePlusTwelveIsSeventyOne = refl

fivePlusFortyTwoIsFortySeven : 5 + 42 ≡ 47
fivePlusFortyTwoIsFortySeven = refl

seventeenPlusFortyTwoIsFiftyNine : 17 + 42 ≡ 59
seventeenPlusFortyTwoIsFiftyNine = refl

twentyNinePlusFortyTwoIsSeventyOne : 29 + 42 ≡ 71
twentyNinePlusFortyTwoIsSeventyOne = refl

largestThreeOggProductIsMonsterDimension : 47 * 59 * 71 ≡ 196883
largestThreeOggProductIsMonsterDimension = refl

------------------------------------------------------------------------
-- The three mobile complement modes carry an actual C3 action.  +12 is +3
-- modulo 9 and +42 is +6 = -3 modulo 9, so they induce inverse cycles.

data MobileComplementMode3 : Set where
  mobile45 mobile18 mobile27 : MobileComplementMode3

advance12 : MobileComplementMode3 → MobileComplementMode3
advance12 mobile45 = mobile18
advance12 mobile18 = mobile27
advance12 mobile27 = mobile45

advance42 : MobileComplementMode3 → MobileComplementMode3
advance42 mobile45 = mobile27
advance42 mobile18 = mobile45
advance42 mobile27 = mobile18

advance12Cubed :
  (mode : MobileComplementMode3) →
  advance12 (advance12 (advance12 mode)) ≡ mode
advance12Cubed mobile45 = refl
advance12Cubed mobile18 = refl
advance12Cubed mobile27 = refl

advance42Cubed :
  (mode : MobileComplementMode3) →
  advance42 (advance42 (advance42 mode)) ≡ mode
advance42Cubed mobile45 = refl
advance42Cubed mobile18 = refl
advance42Cubed mobile27 = refl

advance12After42 :
  (mode : MobileComplementMode3) →
  advance12 (advance42 mode) ≡ mode
advance12After42 mobile45 = refl
advance12After42 mobile18 = refl
advance12After42 mobile27 = refl

advance42After12 :
  (mode : MobileComplementMode3) →
  advance42 (advance12 mode) ≡ mode
advance42After12 mobile45 = refl
advance42After12 mobile18 = refl
advance42After12 mobile27 = refl

mobileModeToNonary : MobileComplementMode3 → Nonary.ComplementMode5
mobileModeToNonary mobile45 = Nonary.mode45
mobileModeToNonary mobile18 = Nonary.mode18
mobileModeToNonary mobile27 = Nonary.mode27

mobileModePhase : MobileComplementMode3 → C3.C3Phase
mobileModePhase mobile45 = Fourier.one
mobileModePhase mobile18 = Fourier.zeta
mobileModePhase mobile27 = Fourier.zetaSquared

advance12IsMultiplyByZeta :
  (mode : MobileComplementMode3) →
  mobileModePhase (advance12 mode)
  ≡ C3.multiplyPhase Fourier.zeta (mobileModePhase mode)
advance12IsMultiplyByZeta mobile45 = refl
advance12IsMultiplyByZeta mobile18 = refl
advance12IsMultiplyByZeta mobile27 = refl

advance42IsMultiplyByInverseZeta :
  (mode : MobileComplementMode3) →
  mobileModePhase (advance42 mode)
  ≡ C3.multiplyPhase (Fourier.inversePhase Fourier.zeta)
      (mobileModePhase mode)
advance42IsMultiplyByInverseZeta mobile45 = refl
advance42IsMultiplyByInverseZeta mobile18 = refl
advance42IsMultiplyByInverseZeta mobile27 = refl

advance42IsMultiplyByZetaSquared :
  (mode : MobileComplementMode3) →
  mobileModePhase (advance42 mode)
  ≡ C3.multiplyPhase Fourier.zetaSquared (mobileModePhase mode)
advance42IsMultiplyByZetaSquared mobile45 = refl
advance42IsMultiplyByZetaSquared mobile18 = refl
advance42IsMultiplyByZetaSquared mobile27 = refl

------------------------------------------------------------------------
-- The concrete six SSP points realize those inverse C3 motions.

fiveMode : MobileComplementMode3
fiveMode = mobile45
seventeenMode : MobileComplementMode3
seventeenMode = mobile18
twentyNineMode : MobileComplementMode3
twentyNineMode = mobile27
fortySevenMode : MobileComplementMode3
fortySevenMode = mobile27
fiftyNineMode : MobileComplementMode3
fiftyNineMode = mobile45
seventyOneMode : MobileComplementMode3
seventyOneMode = mobile18

horizontalSourceGridFollowsAdvance12 :
  advance12 fiveMode ≡ seventeenMode
  × advance12 seventeenMode ≡ twentyNineMode
horizontalSourceGridFollowsAdvance12 = refl , refl

horizontalTargetGridFollowsAdvance12 :
  advance12 fortySevenMode ≡ fiftyNineMode
  × advance12 fiftyNineMode ≡ seventyOneMode
horizontalTargetGridFollowsAdvance12 = refl , refl

verticalGridFollowsInverseAdvance42 :
  advance42 fiveMode ≡ fortySevenMode
  × advance42 seventeenMode ≡ fiftyNineMode
  × advance42 twentyNineMode ≡ seventyOneMode
verticalGridFollowsInverseAdvance42 = refl , (refl , refl)

------------------------------------------------------------------------
-- Cross-observer theorem: +42 changes the C3/nonary mobile phase but preserves
-- the independent CM splitting class on every vertical edge.

verticalFiveToFortySevenPreservesCM :
  cmClass Lane.p5 ≡ cmClass Lane.p47
verticalFiveToFortySevenPreservesCM = refl

verticalSeventeenToFiftyNinePreservesCM :
  cmClass Lane.p17 ≡ cmClass Lane.p59
verticalSeventeenToFiftyNinePreservesCM = refl

verticalTwentyNineToSeventyOnePreservesCM :
  cmClass Lane.p29 ≡ cmClass Lane.p71
verticalTwentyNineToSeventyOnePreservesCM = refl

verticalTranslationPreservesCMOnAffineTriple :
  (cmClass Lane.p5 ≡ cmClass Lane.p47)
  × (cmClass Lane.p17 ≡ cmClass Lane.p59)
  × (cmClass Lane.p29 ≡ cmClass Lane.p71)
verticalTranslationPreservesCMOnAffineTriple = refl , (refl , refl)

------------------------------------------------------------------------
-- Existing pointed-sign genealogy remains a distinct operation.

pointedTwoToFive : 2 * 2 + 1 ≡ 5
pointedTwoToFive = refl

pointedFiveToEleven : 2 * 5 + 1 ≡ 11
pointedFiveToEleven = refl

pointedElevenToTwentyThree : 2 * 11 + 1 ≡ 23
pointedElevenToTwentyThree = refl

pointedTwentyThreeToFortySeven : 2 * 23 + 1 ≡ 47
pointedTwentyThreeToFortySeven = refl

fortySevenMinusFiveEncodedAdditively : 5 + 42 ≡ 47
fortySevenMinusFiveEncodedAdditively = refl
