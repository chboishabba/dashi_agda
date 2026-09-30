{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact where

------------------------------------------------------------------------
-- PHYSICAL-SOURCE FRONTIER: ONE-POINT METRIC RESPONSE OF LOG Z.
--
-- The first derivative of the effective action is proportional to
-- D_h log Z = D_h Z / Z, NOT to the connected derivative of an arbitrary
-- normalized insertion N/Z. The latter computes D_h <O>, which is a
-- second response only if O itself is physically identified as stress.
--
-- This owner consumes the EXISTING six Wilson plaquette energies, their
-- derived ten action variations, and the same finite measure's density.
-- It retains metric variations of E/R/B/vacuum and of the reference measure,
-- and computes the first partition response as one Haar integral.
--
-- These non-Wilson source variations and the reference-measure score MUST
-- be obtained from the selected complete action. They are explicit
-- outstanding physical inputs rather than inferred negative stresses.
-- Finite rational integration does not establish a Lorentzian T00,
-- locally covariant renormalization, or a continuum Einstein solution.
--
-- Sources:
-- Wilson (1974), DOI 10.1103/PhysRevD.10.2445.
-- Balaban CMP119 (1988), DOI 10.1007/BF01217741.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119ClassicalWilsonTenMetricVariationExact as Wilson
import DASHI.Physics.Foundations.CMP119ClassicalWilsonDiagonalMetricVariationExact as Diag
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

record CompleteFiniteMetricVariation (Configuration : Set) : Set₁ where
  field
    -- The six Wilson orientation energies are genuine quantities
    -- at every finite configuration; their four diagonal variations
    -- are COMPUTED by the existing d=4 conformal Wilson owner.
    wilson : Wilson.ClassicalWilsonTenMetricVariation Configuration

    -- No term may be silently dropped from the published effective action.
    regularVariation : K.SymmetricTensorComponent4 → Configuration → ℚ
    rOperationVariation : K.SymmetricTensorComponent4 → Configuration → ℚ
    boundaryVariation : K.SymmetricTensorComponent4 → Configuration → ℚ
    vacuumVariation : K.SymmetricTensorComponent4 → Configuration → ℚ

    -- D_h ln(dnu_g/dnu_ref), only when a metric-dependent reference
    -- measure really exists. For fixed product Haar this is identically 0.
    referenceMeasureLogVariation :
      K.SymmetricTensorComponent4 → Configuration → ℚ

open CompleteFiniteMetricVariation public

nonWilsonDerivative :
  ∀ {Configuration} →
  CompleteFiniteMetricVariation Configuration →
  K.SymmetricTensorComponent4 → Configuration → ℚ
nonWilsonDerivative d h x =
  regularVariation d h x + rOperationVariation d h x
  + boundaryVariation d h x + vacuumVariation d h x

completeActionDerivative :
  ∀ {Configuration} →
  CompleteFiniteMetricVariation Configuration →
  K.SymmetricTensorComponent4 → Configuration → ℚ
completeActionDerivative d h x =
  Wilson.actionVariationAt (wilson d) h x
  + nonWilsonDerivative d h x

-- A first variation of the unnormalized weight
-- dnu_g exp(-S_g) = dnu_ref exp(-S_g) (1 + score_h * epsilon + ...).
weightedLogDerivative :
  ∀ {Configuration} →
  CompleteFiniteMetricVariation Configuration →
  K.SymmetricTensorComponent4 → Configuration → ℚ
weightedLogDerivative d h x =
  referenceMeasureLogVariation d h x - completeActionDerivative d h x

densityFirstVariation :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) →
  CompleteFiniteMetricVariation Configuration →
  K.SymmetricTensorComponent4 → Configuration → ℚ
densityFirstVariation measure d h x =
  Physical.density measure x * weightedLogDerivative d h x

partitionDerivative :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) →
  CompleteFiniteMetricVariation Configuration →
  K.SymmetricTensorComponent4 → ℚ
partitionDerivative measure d h =
  Physical.haarIntegral measure (densityFirstVariation measure d h)

-- D log Z = DZ/Z once the selected Z is positive.
-- No division or Lorentzian sign is selected in the primary numerator.
partitionLogDerivative :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) →
  CompleteFiniteMetricVariation Configuration →
  K.SymmetricTensorComponent4 → ℚ
partitionLogDerivative measure d h =
  Physical.divide measure
    (partitionDerivative measure d h)
    (Physical.partitionFunction measure)

-- The classical Wilson trace cancels; a non-Wilson / measure contribution
-- is therefore NECESSARY for a nonzero Euclidean Weyl-trace response here.
-- This is pointwise and does NOT assume an integral or an Einstein tensor.
fourDiagonalReferenceMinusSector :
  ∀ {Configuration} →
  CompleteFiniteMetricVariation Configuration →
  Configuration → ℚ
fourDiagonalReferenceMinusSector d x =
  (referenceMeasureLogVariation d K.component00 x
    + referenceMeasureLogVariation d K.component11 x
    + referenceMeasureLogVariation d K.component22 x
    + referenceMeasureLogVariation d K.component33 x)
  -
  (nonWilsonDerivative d K.component00 x
    + nonWilsonDerivative d K.component11 x
    + nonWilsonDerivative d K.component22 x
    + nonWilsonDerivative d K.component33 x)

weightedLogDerivativeWeylTrace :
  ∀ {Configuration}
    (d : CompleteFiniteMetricVariation Configuration) x →
  weightedLogDerivative d K.component00 x
    + weightedLogDerivative d K.component11 x
    + weightedLogDerivative d K.component22 x
    + weightedLogDerivative d K.component33 x
  ≡ fourDiagonalReferenceMinusSector d x
weightedLogDerivativeWeylTrace d x
  rewrite Wilson.diagonalActionVariationTraceZero (wilson d) x =
  Ring.solve-∀
    (referenceMeasureLogVariation d K.component00 x)
    (referenceMeasureLogVariation d K.component11 x)
    (referenceMeasureLogVariation d K.component22 x)
    (referenceMeasureLogVariation d K.component33 x)
    (nonWilsonDerivative d K.component00 x)
    (nonWilsonDerivative d K.component11 x)
    (nonWilsonDerivative d K.component22 x)
    (nonWilsonDerivative d K.component33 x)
    (Wilson.actionVariationAt (wilson d) K.component00 x)
    (Wilson.actionVariationAt (wilson d) K.component11 x)
    (Wilson.actionVariationAt (wilson d) K.component22 x)
    (Wilson.actionVariationAt (wilson d) K.component33 x)

-- Separate from Gibbs C_h = (D_h N)Z - N (D_h Z), which yields
-- D_h(N/Z)=C_h/Z² and is NOT automatically the gravitational one-point
-- source. A stress two-point response needs a second actual derivative.
