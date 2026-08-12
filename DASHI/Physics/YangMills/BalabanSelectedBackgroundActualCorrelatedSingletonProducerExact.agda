module DASHI.Physics.YangMills.BalabanSelectedBackgroundActualCorrelatedSingletonProducerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Rename the remaining P3 seam by its actual mathematical content.  The
-- finite pair/deep estimates are already closed.  What the endpoint needs is a
-- family of literal selected single-plaquette witnesses at the SAME selected
-- background and tangent field.  Such a family is converted, without any
-- extra scalar receipt, through
--
--   literal plaquette family
--     -> correlated singleton selector
--     -> PhysicalWilsonSignedLocal
--     -> physical tangent Wilson Hessian >= 1/32 ||h||^2.
--
-- Thus the source-level leaf is exactly construction of
-- `LiteralSelectedPlaquetteFamily`; no caller can reopen the six-pair or deep
-- remainder budgets or substitute a second local Wilson object afterwards.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Radius
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedSinglePlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanSelectedPhysicalTangentHessianExact as Tangent
import DASHI.Physics.YangMills.BalabanP33SelectedBackgroundFiniteCoercivityExact as Selected
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33

actualCorrelatedSingletonFamilyGivesPhysicalWilsonSignedLocal :
  ∀ {background bondField} →
  Radius.RelaxedInverseLinkRadius background →
  Plaquette.LiteralSelectedPlaquetteFamily background bondField →
  Wilson.PhysicalWilsonSignedLocal background bondField
actualCorrelatedSingletonFamilyGivesPhysicalWilsonSignedLocal radius family =
  Selector.selectorAndRadiusGivePhysicalWLocal
    radius
    (Plaquette.literalSelectedPlaquetteFamilyToPhysicalSelector family)

selectedActualCorrelatedSingletonPhysicalWilsonOneThirtySecond :
  ∀ {Perturbation ConstraintIndex}
    (model : Selected.SelectedBackgroundPerturbationModel
      Perturbation ConstraintIndex)
    h →
  Radius.RelaxedInverseLinkRadius (Selected.backgroundOf model h) →
  Plaquette.LiteralSelectedPlaquetteFamily
    (Selected.backgroundOf model h)
    (Selected.physicalFieldOf model h) →
  Tangent.SelectedPhysicalConstraintTangent model h →
  P33.p33PhysicalFloor
      * Coordinates.physicalSU2BondNormSq (Selected.physicalFieldOf model h)
  ≤ Jets.wilsonSecondVariation
      (Selected.selectedLiteralSecondVariation model h)
selectedActualCorrelatedSingletonPhysicalWilsonOneThirtySecond
    model h radius family tangent =
  Tangent.selectedPhysicalWilsonHessianOneThirtySecond
    model h radius
    (actualCorrelatedSingletonFamilyGivesPhysicalWilsonSignedLocal radius family)
    tangent

selectedActualCorrelatedSingletonToWLocalLevel : ProofLevel
selectedActualCorrelatedSingletonToWLocalLevel = machineChecked

selectedActualCorrelatedSingletonPhysicalWilsonHessianLevel : ProofLevel
selectedActualCorrelatedSingletonPhysicalWilsonHessianLevel = machineChecked

-- The remaining source leaf is now deliberately singular: construct the
-- literal selected plaquette family at the selected minimizer.  All downstream
-- Wilson coefficients and tangent collapse are already owned by this module.
selectedActualCorrelatedSingletonFamilyProducerLevel : ProofLevel
selectedActualCorrelatedSingletonFamilyProducerLevel = conditional
