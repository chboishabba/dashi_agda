module DASHI.Physics.Closure.NSTriadKNCubicQuadraticUniformAbsorptionNoGoRound99Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes Equations
-- in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- ROUND99 / UNIVERSAL HOMOGENEITY NO-GO
--
-- Round91 observed that the high-shell nonlinear consumer is cubic in velocity
-- while literal viscous dissipation is quadratic.  The earlier calibration at
-- amplitude 2 showed the mismatch but did not quantify the universal failure.
--
-- Here the no-go is exact: for EVERY proposed nonnegative cutoff-independent
-- constant C, choose amplitude
--
--     a = C + 1.
--
-- Then a>0, C<a, and multiplication by a twice gives
--
--     C a^2 < a^3.
--
-- Thus no estimate of the form
--
--     nonlinear(a) <= C * dissipation(a)
--
-- can follow from homogeneity alone uniformly over amplitude.  Any successful
-- final Clay producer must use additional same-trajectory Navier--Stokes
-- dynamics (signed transfer variation, occupation/escape, or another genuine
-- coercive mechanism); a static HH norm bound cannot close the programme.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _<_; _≤_; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst₂)
open import Relation.Nullary.Decidable.Core using (toWitness)
open ℚP using (_<?_)

square cube : ℚ → ℚ
square a = a * a
cube a = a * a * a

onePositive : 0ℚ < 1ℚ
onePositive = toWitness {a? = 0ℚ <? 1ℚ} _

witnessAmplitude : ℚ → ℚ
witnessAmplitude C = C + 1ℚ

nonnegativeConstantBelowWitness :
  ∀ C → 0ℚ ≤ C → C < witnessAmplitude C
nonnegativeConstantBelowWitness C Cnn =
  let
    shifted : 0ℚ + C < 1ℚ + C
    shifted = ℚP.+-monoʳ-< C onePositive
  in
  subst₂ _<_
    (solve (C ∷ []))
    (solve (C ∷ []))
    shifted

witnessAmplitudePositive :
  ∀ C → 0ℚ ≤ C → 0ℚ < witnessAmplitude C
witnessAmplitudePositive C Cnn =
  ℚP.≤-<-trans Cnn (nonnegativeConstantBelowWitness C Cnn)

cubicStrictlyBeatsAnyFixedQuadraticCoefficient :
  ∀ C → 0ℚ ≤ C →
  C * square (witnessAmplitude C) < cube (witnessAmplitude C)
cubicStrictlyBeatsAnyFixedQuadraticCoefficient C Cnn =
  let
    a = witnessAmplitude C
    C<a : C < a
    C<a = nonnegativeConstantBelowWitness C Cnn
    aPos : 0ℚ < a
    aPos = witnessAmplitudePositive C Cnn

    first : C * a < a * a
    first =
      let instance aPositive = positive aPos
      in ℚP.*-monoˡ-<-pos a C<a

    second : (C * a) * a < (a * a) * a
    second =
      let instance aPositive = positive aPos
      in ℚP.*-monoˡ-<-pos a first
  in
  subst₂ _<_
    (solve (C ∷ a ∷ []))
    (solve (a ∷ []))
    second

uniformAmplitudeFreeCubicAbsorptionFailsAtExplicitWitness :
  ∀ C → 0ℚ ≤ C →
  ¬ (cube (witnessAmplitude C) ≤ C * square (witnessAmplitude C))
uniformAmplitudeFreeCubicAbsorptionFailsAtExplicitWitness C Cnn assumed =
  ℚP.<-irrefl _
    (ℚP.<-≤-trans
      (cubicStrictlyBeatsAnyFixedQuadraticCoefficient C Cnn)
      assumed)

round99StaticHHBoundCanSupplyUniformAmplitudeFreeAbsorption : Bool
round99StaticHHBoundCanSupplyUniformAmplitudeFreeAbsorption = false

round99TrajectoryDynamicsRequiredBeyondCubicQuadraticHomogeneity : Bool
round99TrajectoryDynamicsRequiredBeyondCubicQuadraticHomogeneity = true

round99StaticHHBoundCanSupplyUniformAmplitudeFreeAbsorptionIsFalse :
  round99StaticHHBoundCanSupplyUniformAmplitudeFreeAbsorption ≡ false
round99StaticHHBoundCanSupplyUniformAmplitudeFreeAbsorptionIsFalse = refl
