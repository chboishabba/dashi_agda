module DASHI.Physics.Closure.NSTriadKNCrossLayerThresholdMarginsRound320Exact where

------------------------------------------------------------------------
-- ROUND320 / CROSS-LAYER THRESHOLD MARGINS AS PROOF-SEARCH DISCRIMINATORS
--
-- R319 normalizes the heterochiral-inner-HH closure thresholds.  None is a
-- theorem of the existing one-layer R234/R235 shell taxonomy because they
-- couple the INNER high shell M to OUTER shells p,q,k.
--
-- Therefore the correct proof-search move is to retain these quantities as
-- explicit discriminator margins rather than silently assume them:
--
--   forcing-low : mu = 2M + 2q - 5p
--   forcing-high: mu = 2M - 3q
--   outer HH    : mu = 4m_out + 2M - 5k - 2p
--   comparable  : mu = 2M - 3p
--
-- mu >= 0 is exactly the exponent-level condition that the currently-owned
-- R312 relocation gain dominates the R315 heat residual.  A negative outcome
-- does not falsify the whole resolvent route; it reopens only that cell for a
-- new signed/null/orthogonality mechanism.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
import Data.Rational.Base as ℚ
open ℚ using (ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNHeterochiralHHOuterThresholdsRound319Exact as R319

one two three four five : ℚ
one = 1ℚ
two = one + one
three = two + one
four = two + two
five = four + one

forcingLowMargin : ℚ → ℚ → ℚ → ℚ
forcingLowMargin p q innerHigh =
  two * innerHigh + two * q - five * p

forcingHighMargin : ℚ → ℚ → ℚ
forcingHighMargin q innerHigh =
  two * innerHigh - three * q

outerHHMargin : ℚ → ℚ → ℚ → ℚ → ℚ
outerHHMargin p k outerHigh innerHigh =
  four * outerHigh + two * innerHigh - five * k - two * p

comparableMargin : ℚ → ℚ → ℚ
comparableMargin p innerHigh =
  two * innerHigh - three * p

-- Each margin is the NEGATIVE of R319's normalized residual.  Thus checking
-- margin >= 0 is equivalent, by ordinary ordered-field algebra upstream, to
-- checking residual <= 0.
forcingLowMarginNegatesResidual :
  (p q innerHigh : ℚ) →
  forcingLowMargin p q innerHigh
  ≡ 0 - R319.forcingLowThresholdNormal p q innerHigh
forcingLowMarginNegatesResidual p q innerHigh =
  solve (p ∷ q ∷ innerHigh ∷ [])

forcingHighMarginNegatesResidual :
  (q innerHigh : ℚ) →
  forcingHighMargin q innerHigh
  ≡ 0 - R319.forcingHighThresholdNormal 0 q innerHigh
forcingHighMarginNegatesResidual q innerHigh =
  solve (q ∷ innerHigh ∷ [])

outerHHMarginNegatesResidual :
  (p k outerHigh innerHigh : ℚ) →
  outerHHMargin p k outerHigh innerHigh
  ≡ 0 - R319.hhThresholdNormal p k outerHigh innerHigh
outerHHMarginNegatesResidual p k outerHigh innerHigh =
  solve (p ∷ k ∷ outerHigh ∷ innerHigh ∷ [])

comparableMarginNegatesResidual :
  (p innerHigh : ℚ) →
  comparableMargin p innerHigh
  ≡ 0 - R319.comparableThresholdNormal p innerHigh
comparableMarginNegatesResidual p innerHigh =
  solve (p ∷ innerHigh ∷ [])

data MarginOutcome : Set where
  closesWithKnownRelocation : MarginOutcome
  unresolvedNeedsRefinement : MarginOutcome

record CrossLayerMarginObservation : Set where
  constructor cross-layer-margin-observation
  field
    margin : ℚ
    outcome : MarginOutcome

open CrossLayerMarginObservation public

round320CrossLayerMarginsExplicit : Bool
round320CrossLayerMarginsExplicit = true

round320ExistingOneLayerTaxonomyAssumedToImplyMargins : Bool
round320ExistingOneLayerTaxonomyAssumedToImplyMargins = false

round320MarginOutcomeCanRefineOnlyFailingCell : Bool
round320MarginOutcomeCanRefineOnlyFailingCell = true

round320AnyPhysicalMarginCertifiedNonnegative : Bool
round320AnyPhysicalMarginCertifiedNonnegative = false

round320PackageAClosed : Bool
round320PackageAClosed = false

round320ClayPromotion : Bool
round320ClayPromotion = false

round320PackageAClosedIsFalse : round320PackageAClosed ≡ false
round320PackageAClosedIsFalse = refl
