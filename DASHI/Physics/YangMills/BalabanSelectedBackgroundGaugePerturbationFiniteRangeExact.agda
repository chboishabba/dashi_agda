module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationFiniteRangeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jean-Michel Combes and Lawrence Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- The flat constant projector used to regularize K_0 and K_A is the same on
-- both sides, so it cancels from their difference.  Therefore the perturbation
-- entering
--
--   K_A^reg = K_0^reg + E_A
--
-- is the raw local Gram difference K_A-K_0, not a nonlocal projector defect.
-- This module proves that difference has exactly the same finite spatial range
-- as the selected gauge Gram: if two multiplier rows have disjoint literal
-- stencils, the perturbation matrix entry is zero.
--
-- This matters for the next Combes--Thomas/Neumann step: the remaining issue is
-- quantitative weighted smallness of a *local* E_A, not loss of locality from
-- P_const.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _-_; _+_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramFiniteRangeExact as Gram

gaugeGramPerturbationMatrix :
  Physical.RationalSU2Background4 →
  Rect.RectangularMatrix
    FlatGauge.GaugeCoordinate4 FlatGauge.GaugeCoordinate4
gaugeGramPerturbationMatrix background left right =
  Gram.selectedBackgroundGaugeGram background left right
  - Gram.selectedBackgroundGaugeGram Physical.identityBackground left right

selectedBackgroundGaugeGramPerturbationOutsideRangeZero :
  ∀ background left right →
  Gram.GaugeRowsHaveDisjointStencils left right →
  gaugeGramPerturbationMatrix background left right ≡ 0ℚ
selectedBackgroundGaugeGramPerturbationOutsideRangeZero
    background left right separation =
  trans
    (cong
      (λ flatEntry →
        Gram.selectedBackgroundGaugeGram background left right - flatEntry)
      (Gram.selectedBackgroundGaugeGramOutsideRangeZero
        Physical.identityBackground left right separation))
    (trans
      (cong
        (_- 0ℚ)
        (Gram.selectedBackgroundGaugeGramOutsideRangeZero
          background left right separation))
      (ℚRing.solve []))

regularizedGaugeGramDifference :
  Physical.RationalSU2Background4 →
  Rect.RectangularMatrix
    FlatGauge.GaugeCoordinate4 FlatGauge.GaugeCoordinate4
regularizedGaugeGramDifference = gaugeGramPerturbationMatrix

regularizerCancelsFromBackgroundDifference :
  ∀ background left right (projectorEntry : ℚ) →
  (Gram.selectedBackgroundGaugeGram background left right + projectorEntry)
    - (Gram.selectedBackgroundGaugeGram Physical.identityBackground left right
      + projectorEntry)
  ≡ gaugeGramPerturbationMatrix background left right
regularizerCancelsFromBackgroundDifference
    background left right projectorEntry =
  ℚRing.solve-∀
    (Gram.selectedBackgroundGaugeGram background left right)
    (Gram.selectedBackgroundGaugeGram Physical.identityBackground left right)
    projectorEntry

regularizedGaugeGramDifferenceOutsideRangeZero :
  ∀ background left right →
  Gram.GaugeRowsHaveDisjointStencils left right →
  regularizedGaugeGramDifference background left right ≡ 0ℚ
regularizedGaugeGramDifferenceOutsideRangeZero =
  selectedBackgroundGaugeGramPerturbationOutsideRangeZero

selectedBackgroundGaugePerturbationFiniteRangeLevel : ProofLevel
selectedBackgroundGaugePerturbationFiniteRangeLevel = machineChecked

selectedBackgroundGaugeRegularizerCancellationLevel : ProofLevel
selectedBackgroundGaugeRegularizerCancellationLevel = machineChecked
