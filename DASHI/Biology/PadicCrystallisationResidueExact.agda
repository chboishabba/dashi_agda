module DASHI.Biology.PadicCrystallisationResidueExact where

open import DASHI.Core.Prelude
open import DASHI.Biology.TriadicKernelLiftQuotientExact

------------------------------------------------------------------------
-- Finite exact analogue of p-adic crystallisation as compatible stabilisation
-- of residue patterns.  Coarse residue order can stabilise before fine residue
-- order, and finer digits may reduce the translation stabiliser.

data Site4 : Set where
  site0 : Site4
  site1 : Site4
  site2 : Site4
  site3 : Site4

shiftOne : Site4 → Site4
shiftOne site0 = site1
shiftOne site1 = site2
shiftOne site2 = site3
shiftOne site3 = site0

shiftTwo : Site4 → Site4
shiftTwo x = shiftOne (shiftOne x)

Pattern4 : Set
Pattern4 = Site4 → KernelTrit

coarseOrderedPattern : Pattern4
coarseOrderedPattern site0 = positiveTrit
coarseOrderedPattern site1 = positiveTrit
coarseOrderedPattern site2 = positiveTrit
coarseOrderedPattern site3 = positiveTrit

fineAlternatingPattern : Pattern4
fineAlternatingPattern site0 = positiveTrit
fineAlternatingPattern site1 = negativeTrit
fineAlternatingPattern site2 = positiveTrit
fineAlternatingPattern site3 = negativeTrit

homogeneousDisorderedSeed : Pattern4
homogeneousDisorderedSeed site0 = zeroTrit
homogeneousDisorderedSeed site1 = zeroTrit
homogeneousDisorderedSeed site2 = zeroTrit
homogeneousDisorderedSeed site3 = zeroTrit

shiftOnePeriodic : Pattern4 → Set
shiftOnePeriodic pattern = (x : Site4) → pattern (shiftOne x) ≡ pattern x

shiftTwoPeriodic : Pattern4 → Set
shiftTwoPeriodic pattern = (x : Site4) → pattern (shiftTwo x) ≡ pattern x

coarseHasShiftOnePeriod : shiftOnePeriodic coarseOrderedPattern
coarseHasShiftOnePeriod site0 = refl
coarseHasShiftOnePeriod site1 = refl
coarseHasShiftOnePeriod site2 = refl
coarseHasShiftOnePeriod site3 = refl

fineHasShiftTwoPeriod : shiftTwoPeriodic fineAlternatingPattern
fineHasShiftTwoPeriod site0 = refl
fineHasShiftTwoPeriod site1 = refl
fineHasShiftTwoPeriod site2 = refl
fineHasShiftTwoPeriod site3 = refl

differentTrit : KernelTrit → KernelTrit → Bool
differentTrit negativeTrit negativeTrit = false
differentTrit zeroTrit zeroTrit = false
differentTrit positiveTrit positiveTrit = false
differentTrit _ _ = true

fineBreaksShiftOneAtSiteZero :
  differentTrit
    (fineAlternatingPattern (shiftOne site0))
    (fineAlternatingPattern site0)
  ≡
  true
fineBreaksShiftOneAtSiteZero = refl

------------------------------------------------------------------------
-- Coarse projection forgets orientation but retains nonzero support.

forgetFineOrientation : KernelTrit → KernelTrit
forgetFineOrientation negativeTrit = positiveTrit
forgetFineOrientation zeroTrit = zeroTrit
forgetFineOrientation positiveTrit = positiveTrit

fineProjectsToCoarse :
  (x : Site4) →
  forgetFineOrientation (fineAlternatingPattern x)
  ≡
  coarseOrderedPattern x
fineProjectsToCoarse site0 = refl
fineProjectsToCoarse site1 = refl
fineProjectsToCoarse site2 = refl
fineProjectsToCoarse site3 = refl

------------------------------------------------------------------------
-- Different residue depths stabilise at different finite times.

data CrystalTime : Set where
  time0 : CrystalTime
  time1 : CrystalTime
  time2 : CrystalTime
  time3 : CrystalTime

coarsePatternAt : CrystalTime → Pattern4
coarsePatternAt time0 = homogeneousDisorderedSeed
coarsePatternAt time1 = coarseOrderedPattern
coarsePatternAt time2 = coarseOrderedPattern
coarsePatternAt time3 = coarseOrderedPattern

finePatternAt : CrystalTime → Pattern4
finePatternAt time0 = homogeneousDisorderedSeed
finePatternAt time1 = homogeneousDisorderedSeed
finePatternAt time2 = fineAlternatingPattern
finePatternAt time3 = fineAlternatingPattern

coarseStabilisesFromTimeOne :
  (x : Site4) →
  coarsePatternAt time1 x
  ≡
  coarsePatternAt time3 x
coarseStabilisesFromTimeOne site0 = refl
coarseStabilisesFromTimeOne site1 = refl
coarseStabilisesFromTimeOne site2 = refl
coarseStabilisesFromTimeOne site3 = refl

fineStabilisesFromTimeTwo :
  (x : Site4) →
  finePatternAt time2 x
  ≡
  finePatternAt time3 x
fineStabilisesFromTimeTwo site0 = refl
fineStabilisesFromTimeTwo site1 = refl
fineStabilisesFromTimeTwo site2 = refl
fineStabilisesFromTimeTwo site3 = refl

------------------------------------------------------------------------
-- Translation mismatch density on the four-site carrier.

boolToNat : Bool → Nat
boolToNat false = 0
boolToNat true = 1

shiftOneMismatchCount : Pattern4 → Nat
shiftOneMismatchCount pattern =
  boolToNat (differentTrit (pattern (shiftOne site0)) (pattern site0))
  + boolToNat (differentTrit (pattern (shiftOne site1)) (pattern site1))
  + boolToNat (differentTrit (pattern (shiftOne site2)) (pattern site2))
  + boolToNat (differentTrit (pattern (shiftOne site3)) (pattern site3))

shiftTwoMismatchCount : Pattern4 → Nat
shiftTwoMismatchCount pattern =
  boolToNat (differentTrit (pattern (shiftTwo site0)) (pattern site0))
  + boolToNat (differentTrit (pattern (shiftTwo site1)) (pattern site1))
  + boolToNat (differentTrit (pattern (shiftTwo site2)) (pattern site2))
  + boolToNat (differentTrit (pattern (shiftTwo site3)) (pattern site3))

fineShiftOneMismatchIsFour :
  shiftOneMismatchCount fineAlternatingPattern ≡ 4
fineShiftOneMismatchIsFour = refl

fineShiftTwoMismatchIsZero :
  shiftTwoMismatchCount fineAlternatingPattern ≡ 0
fineShiftTwoMismatchIsZero = refl

coarseShiftOneMismatchIsZero :
  shiftOneMismatchCount coarseOrderedPattern ≡ 0
coarseShiftOneMismatchIsZero = refl

record PadicCrystallisationBoundary : Set where
  constructor padicCrystallisationBoundary
  field
    allDepthsMustStabiliseAtSameTime : Bool
    allDepthsMustStabiliseAtSameTimeIsFalse :
      allDepthsMustStabiliseAtSameTime ≡ false

    finerResiduesCanReduceTranslationSymmetry : Bool
    finerResiduesCanReduceTranslationSymmetryIsTrue :
      finerResiduesCanReduceTranslationSymmetry ≡ true

    finiteDepthPeriodicityProvesOneCommonInfinitePeriod : Bool
    finiteDepthPeriodicityProvesOneCommonInfinitePeriodIsFalse :
      finiteDepthPeriodicityProvesOneCommonInfinitePeriod ≡ false

open PadicCrystallisationBoundary public

canonicalPadicCrystallisationBoundary : PadicCrystallisationBoundary
canonicalPadicCrystallisationBoundary =
  padicCrystallisationBoundary false refl true refl false refl
