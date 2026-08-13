module DASHI.Physics.YangMills.BalabanYM4RunningCouplingDriftExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- R. F. Dashen and D. J. Gross,
-- "The Relationship between Lattice and Continuum Definitions of the Gauge
-- Theory Coupling",
-- Physical Review D 23 (1981), 2340--2348.
-- DOI: 10.1103/PhysRevD.23.2340.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- RG1e needs more than a symbolic O(g^2).  The remainder must be small enough
-- that the inverse-coupling coordinate still moves in the asymptotically-free
-- direction at every step.  This module isolates the exact robust inequality:
--
--   x' >= x + betaStep - error,
--   2 error <= betaStep
--       ==> x' >= x + betaStep/2.
--
-- Here x is the repository's chosen inverse-squared coupling coordinate.  The
-- physical producer must instantiate betaStep in the exact Dashen--Gross /
-- Bałaban normalization and prove its remainder estimate.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

oneHalf : ℚ
oneHalf = + 1 / 2

inverseCouplingRobustPositiveDrift :
  ∀ current next betaStep error →
  current + betaStep - error ≤ next →
  error + error ≤ betaStep →
  current + oneHalf * betaStep ≤ next
inverseCouplingRobustPositiveDrift current next betaStep error recurrence errorFits =
  let
    scaled :
      oneHalf * (error + error)
      ≤ oneHalf * betaStep
    scaled = Norm.scaleNonnegative oneHalf
      (ℚP.nonNegative⁻¹ oneHalf) errorFits

    errorBelowHalfStep : error ≤ oneHalf * betaStep
    errorBelowHalfStep =
      subst
        (λ lower → lower ≤ oneHalf * betaStep)
        (ℚRing.solve-∀ error)
        scaled

    plusHalf :
      error + oneHalf * betaStep
      ≤ oneHalf * betaStep + oneHalf * betaStep
    plusHalf = ℚP.+-mono-≤ errorBelowHalfStep ℚP.≤-refl

    halfPlusErrorBelowStep :
      oneHalf * betaStep + error ≤ betaStep
    halfPlusErrorBelowStep =
      subst
        (λ lower → lower ≤ betaStep)
        (ℚRing.solve-∀ error betaStep)
        (subst
          (λ upper → error + oneHalf * betaStep ≤ upper)
          (ℚRing.solve-∀ betaStep)
          plusHalf)

    halfPlusErrorBelowCorrectedPlusError :
      oneHalf * betaStep + error
      ≤ (betaStep - error) + error
    halfPlusErrorBelowCorrectedPlusError =
      subst
        (λ upper → oneHalf * betaStep + error ≤ upper)
        (sym (ℚRing.solve-∀ betaStep error))
        halfPlusErrorBelowStep

    halfStepBelowCorrected :
      oneHalf * betaStep ≤ betaStep - error
    halfStepBelowCorrected =
      ℚP.+-cancelʳ-≤ error halfPlusErrorBelowCorrectedPlusError

    translated :
      current + oneHalf * betaStep
      ≤ current + (betaStep - error)
    translated = ℚP.+-monoˡ-≤ current halfStepBelowCorrected
  in
  ℚP.≤-trans
    (subst
      (λ upper → current + oneHalf * betaStep ≤ upper)
      (ℚRing.solve-∀ current betaStep error)
      translated)
    recurrence

ym4RunningCouplingRobustDriftLevel : ProofLevel
ym4RunningCouplingRobustDriftLevel = machineChecked
