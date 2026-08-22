module DASHI.Moonshine.SSP15PhaseClosure54Exact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- The affine SSP translations found in SSP15AffineC3TranslationExact satisfy
--
--   12 + 42 = 54.
--
-- Their induced mobile-mode actions are inverse C3 rotations, so the composed
-- +54 displacement is phase-neutral.  This connects the independently arising
-- 54 = 6*9 boundary to an exact conjugate-translation closure law rather than
-- only to cardinal arithmetic.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Moonshine.SSP15AffineC3TranslationExact as SSP
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

horizontalPlusVerticalIsFiftyFour : 12 + 42 ≡ 54
horizontalPlusVerticalIsFiftyFour = refl

fivePlusFiftyFourIsFiftyNine : 5 + 54 ≡ 59
fivePlusFiftyFourIsFiftyNine = refl

seventeenPlusFiftyFourIsSeventyOne : 17 + 54 ≡ 71
seventeenPlusFiftyFourIsSeventyOne = refl

fiftyFourPreservesModeFiveToFiftyNine :
  SSP.primeComplementMode Lane.p5 ≡ SSP.primeComplementMode Lane.p59
fiftyFourPreservesModeFiveToFiftyNine = refl

fiftyFourPreservesModeSeventeenToSeventyOne :
  SSP.primeComplementMode Lane.p17 ≡ SSP.primeComplementMode Lane.p71
fiftyFourPreservesModeSeventeenToSeventyOne = refl

fiftyFourPhaseClosure :
  (mode : SSP.MobileComplementMode3) →
  SSP.advance12 (SSP.advance42 mode) ≡ mode
fiftyFourPhaseClosure = SSP.advance12After42

zetaTimesInversePhaseIsOne :
  C3.multiplyPhase Fourier.zeta (Fourier.inversePhase Fourier.zeta)
  ≡ Fourier.one
zetaTimesInversePhaseIsOne = Fourier.zetaTimesInverseZetaIsOne

fiftyFourClosureMatchesC3Identity :
  (mode : SSP.MobileComplementMode3) →
  SSP.mobileModePhase (SSP.advance12 (SSP.advance42 mode))
  ≡ SSP.mobileModePhase mode
fiftyFourClosureMatchesC3Identity SSP.mobile45 = refl
fiftyFourClosureMatchesC3Identity SSP.mobile18 = refl
fiftyFourClosureMatchesC3Identity SSP.mobile27 = refl
