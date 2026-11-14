module DASHI.Physics.YangMills.BalabanP0FreeGhostWilsonPositiveWeldExact where

-- MAX-CUT SOURCE DONOR WELD, no axioms, no proxy ghost symbol:
--
--  BalabanP33PhysicalFaddeevPopovOperatorExact
--      -> BalabanClayT4FaddeevPopovWilsonSymbolBridgeExact
--      -> original canonical Bishop hat-momentum value
--      -> BalabanClayT4RefinedOriginalWilsonBishopEnvironmentExact
--      -> the SAME positive source-box Wilson denominator.
--
-- This is the exact free-symbol / real-value / positive interval triangle.
-- It is NOT the background FP determinant, the shifted-loop numerator,
-- a source-specific bubble integral, or a proof of the half-angle
-- identity and Fourier-domain interval membership. These remain
-- source-specific premises and are NOT manufactured by this module.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (false)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (0ℚ; _<_)
import RealProperties as BishopP

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4CanonicalBishopAtomEnvironmentExact as Canonical
import DASHI.Physics.YangMills.BalabanClayT4FaddeevPopovWilsonSymbolBridgeExact as Ghost
import DASHI.Physics.YangMills.BalabanClayT4SineDeterminesCosineAtomExact as Derived
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as BishopBox
import DASHI.Physics.YangMills.BalabanClayT4RefinedSineSquareRegularBoxesExact as Square
import DASHI.Physics.YangMills.BalabanClayT4RefinedOriginalWilsonBishopEnvironmentExact as Wilson

-- The actual ghost symbol is definitionally interpreted through the
-- original canonical Wilson hat-momentum atom at the SAME role.
-- Bishop real interval membership transports through the existing
-- half-angle/Faddeev-Popov proof, not a synthetic ghost interval.
actualGhostSymbolInRefinedWilsonBox :
  (dataSet : Ghost.CoherentGhostTrigBoxData) →
  ∀ {role cell} →
  Wilson.ActualSourceFourSineMembership (Ghost.trig dataSet) role cell →
  BishopBox.BishopLiesIn
    (Ghost.freeGhostSymbol dataSet role)
    (Square.sourceWilsonDenominatorBox cell)
actualGhostSymbolInRefinedWilsonBox dataSet {role} {cell} sines =
  let
    -- The source ghost is equal to the canonical Wilson real as a
    -- BISHOP SETOID real, not as an Agda Cauchy-record identity.
    equivalent =
      Ghost.freeGhostSymbolIsCanonicalHatMomentumAtom dataSet role
    wilsonInside = Wilson.originalWilsonHatSound sines
  in
  BishopBox.bishopLiesIn
    (BishopP.≤-respʳ-≃
      (BishopP.≃-symm equivalent)
      (BishopBox.lowerSound wilsonInside))
    (BishopP.≤-respˡ-≃
      equivalent
      (BishopBox.upperSound wilsonInside))

-- The actual sine-to-coherent-cosine donor already proves the identity
-- needed by the ghost symbol as a Bishop setoid theorem. No second
-- physical cosine box producer or propositional equality axiom.
derivedCoherentGhostFromOriginalSine :
  Derived.PhysicalSineHalfBoxData →
  Ghost.CoherentGhostTrigBoxData
derivedCoherentGhostFromOriginalSine sineSource = record
  { Ghost.CoherentGhostTrigBoxData.trig =
      Derived.derivedPhysicalTrigBoxData sineSource
  ; Ghost.CoherentGhostTrigBoxData.halfAngleExact =
      Derived.derivedHalfAngleCoherence sineSource
  }

-- Main strict positivity consumer: the source's ACTUAL free FP
-- Fourier symbol and original Wilson hat-p^2 both lie in this same
-- rational positive interval on a regular cell. Both are the same
-- canonical Bishop real, not merely equal numerical approximations.
regularFreeGhostWilsonSharedPositiveInterval :
  (dataSet : Ghost.CoherentGhostTrigBoxData) →
  (cell : Grid.GridCell4) →
  (sines : Wilson.ActualSourceFourSineMembership
    (Ghost.trig dataSet) Eval.loopMomentum cell) →
  Grid.allInner cell ≡ false →
  BishopBox.BishopLiesIn
    (Ghost.freeGhostSymbol dataSet Eval.loopMomentum)
    (Square.sourceWilsonDenominatorBox cell)
  ×
  (0ℚ < Eval.lower (Square.sourceWilsonDenominatorBox cell))
regularFreeGhostWilsonSharedPositiveInterval dataSet cell sines regular =
  actualGhostSymbolInRefinedWilsonBox dataSet sines ,
  Square.sourceStrictPositiveAtRegularBox cell regular

-- The source may require TWO different boxes: p and p+k can cross a
-- box boundary. Demanding the same original cell for shifted momentum
-- would be physically false for boundary points.
--
-- This theorem pays the *joint free symbol* algebra if both selected
-- Fourier roles have their own source-real sine membership AND their
-- respective boxes are regular. It does NOT assert that p+k is regular.
loopAndShiftedFreeSymbolsBothPositive :
  (dataSet : Ghost.CoherentGhostTrigBoxData) →
  (loopCell shiftedCell : Grid.GridCell4) →
  Wilson.ActualSourceFourSineMembership
    (Ghost.trig dataSet) Eval.loopMomentum loopCell →
  Wilson.ActualSourceFourSineMembership
    (Ghost.trig dataSet) Eval.shiftedMomentum shiftedCell →
  Grid.allInner loopCell ≡ false →
  Grid.allInner shiftedCell ≡ false →
  (BishopBox.BishopLiesIn
    (Ghost.freeGhostSymbol dataSet Eval.loopMomentum)
    (Square.sourceWilsonDenominatorBox loopCell)
   × (0ℚ < Eval.lower (Square.sourceWilsonDenominatorBox loopCell)))
  ×
  (BishopBox.BishopLiesIn
    (Ghost.freeGhostSymbol dataSet Eval.shiftedMomentum)
    (Square.sourceWilsonDenominatorBox shiftedCell)
   × (0ℚ < Eval.lower (Square.sourceWilsonDenominatorBox shiftedCell)))
loopAndShiftedFreeSymbolsBothPositive
  dataSet loopCell shiftedCell loopSines shiftedSines loopRegular shiftedRegular =
  regularFreeGhostWilsonSharedPositiveInterval
    dataSet loopCell loopSines loopRegular ,
  (actualGhostSymbolInRefinedWilsonBox dataSet shiftedSines ,
   Square.sourceStrictPositiveAtRegularBox shiftedCell shiftedRegular)

-- Boundary:
-- * CoherentGhostTrigBoxData.halfAngleExact is still to be produced
--   for the SAME actual continuum/Bishop Fourier point values.
-- * ActualSourceFourSineMembership requires actual uniform sine bounds.
-- * The p+k map's box/rank and shifted spectral gap need proof.
-- * The background FP determinant/trace-log to continuum momentum loop
--   and Wilson/Haar tensor-to-beta projection remain physical work.

-- Strongest source-closed consumer: the original PhysicalSineHalfBoxData
-- provides BOTH the selected actual sin-half values and the *derived*
-- cos values, so even the ghost half-angle coherence is no longer a
-- separate input. Only the physical Fourier/Machin source-cell sine
-- membership and the actual regular-box status remain.
derivedSineGhostWilsonPositive :
  (sineSource : Derived.PhysicalSineHalfBoxData) →
  (cell : Grid.GridCell4) →
  Wilson.ActualSourceFourSineMembership
    (Derived.derivedPhysicalTrigBoxData sineSource)
    Eval.loopMomentum cell →
  Grid.allInner cell ≡ false →
  BishopBox.BishopLiesIn
    (Ghost.freeGhostSymbol
      (derivedCoherentGhostFromOriginalSine sineSource)
      Eval.loopMomentum)
    (Square.sourceWilsonDenominatorBox cell)
  × (0ℚ < Eval.lower (Square.sourceWilsonDenominatorBox cell))
derivedSineGhostWilsonPositive sineSource cell membership regular =
  regularFreeGhostWilsonSharedPositiveInterval
    (derivedCoherentGhostFromOriginalSine sineSource)
    cell membership regular
