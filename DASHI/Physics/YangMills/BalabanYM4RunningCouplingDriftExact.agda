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
-- theorem is normalization-agnostic: the physical producer must instantiate
-- betaStep with the exact Dashen--Gross/Bałaban convention and prove its error
-- estimate, but once that is done the positive UV drift cannot be erased by
-- the remainder.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

oneHalf : ℚ
oneHalf = + 1 / 2

inverseCouplingRobustPositiveDrift :
  ∀ current next betaStep error →
  current + betaStep - error ≤ next →
  error + error ≤ betaStep →
  current + oneHalf * betaStep ≤ next
inverseCouplingRobustPositiveDrift current next betaStep error recurrence errorFits =
  let
    halfStepBelowRemainderCorrected :
      current + oneHalf * betaStep
      ≤ current + betaStep - error
    halfStepBelowRemainderCorrected =
      subst
        (λ lower → current + oneHalf * betaStep ≤ lower)
        (ℚRing.solve-∀ current betaStep error)
        (ℚP.+-monoˡ-≤ current
          (subst
            (λ upper → error + error ≤ upper)
            (ℚRing.solve-∀ betaStep)
            errorFits))
  in
  ℚP.≤-trans halfStepBelowRemainderCorrected recurrence

ym4RunningCouplingRobustDriftLevel : ProofLevel
ym4RunningCouplingRobustDriftLevel = machineChecked
