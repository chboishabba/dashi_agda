module DASHI.Physics.Closure.NSTriadKNNestedCriticalGainConsumerRound315Exact where

------------------------------------------------------------------------
-- ROUND315 / BACKWARD CONSUMER FOR THE TWELVE ORIENTED NESTED ROUTES
--
-- R305 proves that heat/resolvent factorization alone leaves a positive
-- critical dyadic exponent.  R314 refines the outer FL shoulder by retaining
-- which leg carries the nested forcing N_p.
--
-- The BIDI consumer is therefore not "find a particular null form".  It is:
-- supply enough CERTIFIED SQUARED DYADIC GAIN g so that
--
--     residual - g <= 0.
--
-- Different forward mechanisms (inner homochiral radial difference, inner
-- heterochiral HH derivative relocation, outer slot defect, or a future signed
-- cancellation) may all inhabit the same consumer without being identified.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
import Data.Rational.Base as ℚ
open ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNCriticalConeHeatExponentDiagnosticRound305Exact as R305
import DASHI.Physics.Closure.NSTriadKNNestedOuterOrientationRefinementRound314Exact as R314

one two three four five : ℚ
one = 1ℚ
two = one + one
three = two + one
four = two + two
five = four + one

record OrientedOuterShells : Set where
  constructor oriented-outer-shells
  field
    pShell qShell kShell : ℚ
    -- HH analysis uses one declared high-shell coordinate m.  The physical
    -- shell-comparability weld remains upstream and is not invented here.
    hhHighShell : ℚ

open OrientedOuterShells public

missingSquaredGain :
  R314.OrientedOuterCriticalRegion → OrientedOuterShells → ℚ
missingSquaredGain R314.forcingLowFLShoulder S =
  R305.farLowHeatResidualExponent (pShell S) (qShell S)
missingSquaredGain R314.forcingHighHLShoulder S =
  R305.farLowHeatResidualExponent (qShell S) (pShell S)
missingSquaredGain R314.outerHHShoulder S =
  R305.hhHeatResidualExponent (kShell S) (hhHighShell S)
missingSquaredGain R314.outerComparable S =
  -- On the exact comparable ray the R305 residual is one shell power.  A
  -- physical comparable-band adapter may replace this exact-ray fixture by a
  -- bounded-width version upstream.
  pShell S

record CertifiedNestedGain : Set where
  constructor certified-nested-gain
  field
    route : R314.OrientedNestedRoute
    shells : OrientedOuterShells
    suppliedSquaredGain : ℚ
    suppliedGainNonnegative : 0ℚ ≤ suppliedSquaredGain
    residualAfterGain : ℚ
    residualMeaning :
      residualAfterGain
      ≡ missingSquaredGain (R314.outerRegion route) shells - suppliedSquaredGain
    residualPaid : residualAfterGain ≤ 0ℚ

open CertifiedNestedGain public

-- Compiler form useful to forward producers: proving missing <= supplied is
-- enough; no mechanism-specific structure appears downstream.
record GainDominatesResidual : Set where
  constructor gain-dominates-residual
  field
    region : R314.OrientedOuterCriticalRegion
    shells : OrientedOuterShells
    suppliedSquaredGain : ℚ
    dominance : missingSquaredGain region shells ≤ suppliedSquaredGain

open GainDominatesResidual public

dominanceGivesNonpositiveResidual :
  (D : GainDominatesResidual) →
  missingSquaredGain (region D) (shells D) - suppliedSquaredGain D ≤ 0ℚ
dominanceGivesNonpositiveResidual D =
  ℚ.-≤0⇒≤ (dominance D)

-- Orientation regression: swapping which physical leg carries the nested
-- forcing swaps which shell is treated as low/high by the FL residual.
forcingLowResidualFormula :
  (S : OrientedOuterShells) →
  missingSquaredGain R314.forcingLowFLShoulder S
  ≡ three * pShell S - two * qShell S
forcingLowResidualFormula S = solve (pShell S ∷ qShell S ∷ [])

forcingHighResidualFormula :
  (S : OrientedOuterShells) →
  missingSquaredGain R314.forcingHighHLShoulder S
  ≡ three * qShell S - two * pShell S
forcingHighResidualFormula S = solve (pShell S ∷ qShell S ∷ [])

hhResidualFormula :
  (S : OrientedOuterShells) →
  missingSquaredGain R314.outerHHShoulder S
  ≡ five * kShell S - four * hhHighShell S
hhResidualFormula S = solve (kShell S ∷ hhHighShell S ∷ [])

round315ExactBackwardGainConsumerInstalled : Bool
round315ExactBackwardGainConsumerInstalled = true

round315ForcingOrientationChangesFLResidualFormula : Bool
round315ForcingOrientationChangesFLResidualFormula = true

round315OneUniversalForwardGainMechanismAssumed : Bool
round315OneUniversalForwardGainMechanismAssumed = false

round315AnyPhysicalTwelveCellGainClosed : Bool
round315AnyPhysicalTwelveCellGainClosed = false

round315PackageAClosed : Bool
round315PackageAClosed = false

round315ClayPromotion : Bool
round315ClayPromotion = false

round315PackageAClosedIsFalse : round315PackageAClosed ≡ false
round315PackageAClosedIsFalse = refl
