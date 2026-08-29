module DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondIterationExact where

------------------------------------------------------------------------
-- ROUND66: EXACT ITERATION OF THE UNIFIED 17/32 RG BUDGET
--
-- PRIMARY SOURCES / CALIBRATION
--
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- P. K. Mitter, "A non trivial fixed point in a three dimensional quantum
-- field theory", Oberwolfach Report 17/2006, The Rigorous Renormalization
-- Group. DOI of report: 10.4171/OWR/2006/17.
--
-- DASHI CONTRIBUTION
--
-- Round66 isolates the one-step unified-polymer target
--
--   K_(n+1) <= (17/32) K_n + E 2^{-n}.
--
-- Because 17/32 - 1/2 = 1/32, its discrete convolution has the exact closed
-- form
--
--   C_n = 32 ((17/32)^n - (1/2)^n).
--
-- Thus the all-depth estimate is no longer an independent continuum theorem:
-- once the physical one-step inequality is proved in the SAME corrected norm,
-- exact finite induction supplies the complete RG-depth majorant.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

theta half thirtyTwo : ℚ
theta = + 17 / 32
half = + 1 / 2
thirtyTwo = + 32 / 1

thetaNonnegative : 0ℚ ≤ theta
thetaNonnegative = ℚP.nonNegative⁻¹ theta

halfNonnegative : 0ℚ ≤ half
halfNonnegative = ℚP.nonNegative⁻¹ half

pow : ℚ → Nat → ℚ
pow q zero = 1ℚ
pow q (suc n) = q * pow q n

thetaPower halfPower : Nat → ℚ
thetaPower = pow theta
halfPower = pow half

convolution : Nat → ℚ
convolution zero = 0ℚ
convolution (suc n) = theta * convolution n + halfPower n

thetaMinusHalfIsOneThirtySecond :
  theta - half ≡ + 1 / 32
thetaMinusHalfIsOneThirtySecond = ℚRing.solve []

convolutionClosedForm : ∀ n →
  convolution n ≡ thirtyTwo * (thetaPower n - halfPower n)
convolutionClosedForm zero = ℚRing.solve []
convolutionClosedForm (suc n)
  rewrite convolutionClosedForm n =
  ℚRing.solve-∀ (thetaPower n) (halfPower n)

record SeventeenThirtySecondRGRecurrence : Set₁ where
  field
    K : Nat → ℚ
    forcingAmplitude : ℚ
    forcingAmplitudeNonnegative : 0ℚ ≤ forcingAmplitude
    oneStep : ∀ n →
      K (suc n) ≤ theta * K n + forcingAmplitude * halfPower n

open SeventeenThirtySecondRGRecurrence public

majorant : SeventeenThirtySecondRGRecurrence → Nat → ℚ
majorant dataSet n =
  thetaPower n * K dataSet zero
  + forcingAmplitude dataSet * convolution n

majorantRecurrence :
  (dataSet : SeventeenThirtySecondRGRecurrence) → ∀ n →
  majorant dataSet (suc n)
  ≡ theta * majorant dataSet n
      + forcingAmplitude dataSet * halfPower n
majorantRecurrence dataSet n =
  ℚRing.solve-∀
    (thetaPower n)
    (halfPower n)
    (K dataSet zero)
    (forcingAmplitude dataSet)
    (convolution n)

majorantDominates :
  (dataSet : SeventeenThirtySecondRGRecurrence) → ∀ n →
  K dataSet n ≤ majorant dataSet n
majorantDominates dataSet zero =
  subst
    (λ right → K dataSet zero ≤ right)
    (ℚRing.solve-∀ (K dataSet zero) (forcingAmplitude dataSet))
    ℚP.≤-refl
majorantDominates dataSet (suc n) =
  let
    step = oneStep dataSet n
    scaled = Norm.scaleNonnegative
      theta thetaNonnegative (majorantDominates dataSet n)
    lifted = ℚP.+-mono-≤ scaled ℚP.≤-refl
    combined = ℚP.≤-trans step lifted
  in
  subst
    (λ right → K dataSet (suc n) ≤ right)
    (sym (majorantRecurrence dataSet n))
    combined

majorantClosedForm :
  (dataSet : SeventeenThirtySecondRGRecurrence) → ∀ n →
  majorant dataSet n
  ≡ thetaPower n * K dataSet zero
    + (thirtyTwo * forcingAmplitude dataSet)
        * (thetaPower n - halfPower n)
majorantClosedForm dataSet n
  rewrite convolutionClosedForm n =
  ℚRing.solve-∀
    (thetaPower n)
    (halfPower n)
    (K dataSet zero)
    (forcingAmplitude dataSet)

allDepthClosedFormBound :
  (dataSet : SeventeenThirtySecondRGRecurrence) → ∀ n →
  K dataSet n
  ≤ thetaPower n * K dataSet zero
    + (thirtyTwo * forcingAmplitude dataSet)
        * (thetaPower n - halfPower n)
allDepthClosedFormBound dataSet n =
  subst
    (λ right → K dataSet n ≤ right)
    (majorantClosedForm dataSet n)
    (majorantDominates dataSet n)

seventeenThirtySecondIterationAlgebraLevel : ProofLevel
seventeenThirtySecondIterationAlgebraLevel = machineChecked

-- Physical theorem-8 seam after Round66: establish the one-step recurrence in
-- the corrected unified YM norm, uniformly in lattice volume and cutoff.  The
-- all-depth iteration above is then exact downstream algebra.
physicalUnifiedOneStepRecurrenceLevel : ProofLevel
physicalUnifiedOneStepRecurrenceLevel = conditional
