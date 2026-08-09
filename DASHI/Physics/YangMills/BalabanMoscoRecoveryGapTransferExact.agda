module DASHI.Physics.YangMills.BalabanMoscoRecoveryGapTransferExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Umberto Mosco,
-- "Convergence of Convex Sets and of Solutions of Variational
-- Inequalities", Advances in Mathematics 3 (1969), 510--585.
-- DOI: 10.1016/0001-8708(69)90009-7.
--
-- Kazuhiro Kuwae; Takashi Shioya,
-- "Convergence of Spectral Structures: A Functional Analytic Theory and Its
-- Applications to Spectral Geometry", Communications in Analysis and
-- Geometry 11 (2003), 599--673.
-- DOI: 10.4310/cag.2003.v11.n4.a1.
--
-- DASHI CONTRIBUTION
--
-- Isolate the order direction needed to transport a uniform spectral-form
-- gap.  A Mosco liminf inequality alone has the wrong direction: it says the
-- limit energy is no larger than a liminf and therefore cannot prevent the
-- limit form from dropping below the finite gap.  A recovery (Mosco upper)
-- sequence gives the needed chain
--
--   m ||u||^2 <= m ||u_n||^2 <= Q_n(u_n) <= Q_infinity(u).
--
-- The first theorem formalizes this chain exactly over the rational order.
-- The second construction gives a literal liminf-only countermodel whose
-- desired gap conclusion reduces to 1 <= 0.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _/_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record UniformGapRecoveryStep : Set where
  field
    gapConstant : ℚ
    gapConstantNonnegative : 0ℚ ≤ gapConstant

    limitOrthogonalNormSq recoveryOrthogonalNormSq : ℚ
    recoveryEnergy limitEnergy : ℚ

    normRecovered :
      limitOrthogonalNormSq ≤ recoveryOrthogonalNormSq

    finiteUniformGap :
      gapConstant * recoveryOrthogonalNormSq ≤ recoveryEnergy

    recoveryEnergyUpper : recoveryEnergy ≤ limitEnergy
open UniformGapRecoveryStep public

recoveryStepTransfersUniformGap :
  (step : UniformGapRecoveryStep) →
  gapConstant step * limitOrthogonalNormSq step
  ≤ limitEnergy step
recoveryStepTransfersUniformGap step =
  let
    instance
      gapNN : NonNegative (gapConstant step)
      gapNN = nonNegative (gapConstantNonnegative step)

    normScaled :
      gapConstant step * limitOrthogonalNormSq step
      ≤ gapConstant step * recoveryOrthogonalNormSq step
    normScaled =
      ℚP.*-monoˡ-≤-nonNeg
        (gapConstant step) (normRecovered step)
  in
  ℚP.≤-trans normScaled
    (ℚP.≤-trans
      (finiteUniformGap step)
      (recoveryEnergyUpper step))

record LiminfOnlyStep : Set where
  field
    gapConstant : ℚ
    finiteOrthogonalNormSq limitOrthogonalNormSq : ℚ
    finiteEnergy limitEnergy : ℚ

    finiteUniformGap :
      gapConstant * finiteOrthogonalNormSq ≤ finiteEnergy

    liminfDirectionOnly : limitEnergy ≤ finiteEnergy
open LiminfOnlyStep public

liminfOnlyCounterexample : LiminfOnlyStep
liminfOnlyCounterexample = record
  { gapConstant = 1ℚ
  ; finiteOrthogonalNormSq = 1ℚ
  ; limitOrthogonalNormSq = 1ℚ
  ; finiteEnergy = 1ℚ
  ; limitEnergy = 0ℚ
  ; finiteUniformGap = ℚP.≤-refl
  ; liminfDirectionOnly = ℚP.0≤p }

liminfOnlyCounterexampleFiniteGapExact :
  gapConstant liminfOnlyCounterexample
    * finiteOrthogonalNormSq liminfOnlyCounterexample
  ≡ finiteEnergy liminfOnlyCounterexample
liminfOnlyCounterexampleFiniteGapExact = refl

liminfOnlyCounterexampleLimitGapWouldBeOneBelowZero :
  gapConstant liminfOnlyCounterexample
    * limitOrthogonalNormSq liminfOnlyCounterexample
  ≤ limitEnergy liminfOnlyCounterexample →
  1ℚ ≤ 0ℚ
liminfOnlyCounterexampleLimitGapWouldBeOneBelowZero conclusion = conclusion

moscoRecoveryGapTransferLevel : ProofLevel
moscoRecoveryGapTransferLevel = machineChecked

moscoLiminfAloneInsufficientLevel : ProofLevel
moscoLiminfAloneInsufficientLevel = machineChecked
