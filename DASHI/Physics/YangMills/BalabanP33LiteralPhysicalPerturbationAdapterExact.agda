module DASHI.Physics.YangMills.BalabanP33LiteralPhysicalPerturbationAdapterExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CORRECTION AND CONTRIBUTION
--
-- Bind every representation in the corrected Hodge comparison to one actual
-- three-component SU(2) perturbation h.  The former adapter used a scalar bond
-- field even though the Wilson second variation and the 3072-coordinate norm
-- are physical three-component quantities.
--
-- A model now maps the same h to:
--
--   * its literal PhysicalSU2BondField4;
--   * its rational Wilson/gauge/CMP109 second-variation data;
--   * its physical norm and open reference difference energy;
--   * its selected flat curl and flat divergence energies.
--
-- Pointwise exact laws identify those values.  The final theorem consumes
-- separate sharp Wilson and gauge defect estimates and transports them to the
-- literal total Hessian generated from the same non-phantom h.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; -_; _-_; _≤_)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2HodgeCoercivityExact as PhysicalHodge
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintCancellationExact as Cancel
import DASHI.Physics.YangMills.BalabanP33WilsonSharpDuhamelBudgetExact as Sharp
import DASHI.Physics.YangMills.BalabanP33WilsonSharpBudgetCoercivityExact as SharpPromotion

------------------------------------------------------------------------
-- One physical perturbation model and its exact compatibility laws.
------------------------------------------------------------------------

record LiteralPhysicalPerturbationModel
    (Perturbation Plaquette GaugeIndex ConstraintIndex : Set) : Set₁ where
  field
    physicalFieldOf : Perturbation → Physical.PhysicalSU2BondField4

    secondVariationOf : Perturbation →
      Jets.LiteralPhysicalSecondVariation
        Plaquette GaugeIndex ConstraintIndex

    physicalNormSqOf : Perturbation → ℚ
    physicalReferenceDifferenceOf : Perturbation → ℚ
    physicalWilsonSecondVariationOf : Perturbation → ℚ
    physicalGaugeSecondVariationOf : Perturbation → ℚ
    physicalFlatCurlEnergyOf : Perturbation → ℚ
    physicalFlatDivergenceEnergyOf : Perturbation → ℚ

    normMatchesPhysicalField : ∀ h →
      Physical.physicalSU2BondNormSq (physicalFieldOf h)
      ≡ physicalNormSqOf h

    referenceDifferenceMatchesPhysicalField : ∀ h →
      PhysicalHodge.physicalReferenceDifferenceEnergy (physicalFieldOf h)
      ≡ physicalReferenceDifferenceOf h

    flatHodgeMatchesReference : ∀ h →
      physicalReferenceDifferenceOf h
      ≡ physicalFlatCurlEnergyOf h
        + physicalFlatDivergenceEnergyOf h

    wilsonSecondVariationMatchesPhysical : ∀ h →
      Jets.wilsonSecondVariation (secondVariationOf h)
      ≡ physicalWilsonSecondVariationOf h

    gaugeSecondVariationMatchesPhysical : ∀ h →
      Cancel.gaugeFirstEnergy (secondVariationOf h)
      ≡ physicalGaugeSecondVariationOf h

    componentMeanZero : ∀ h →
      PhysicalHodge.PhysicalBondComponentMeanZero (physicalFieldOf h)

    gaugeExact : ∀ h →
      Jets.ExactResidualBackground
        (Jets.gaugeResidual (secondVariationOf h))

    constraintExact : ∀ h →
      Jets.ExactResidualBackground
        (Jets.constraintResidual (secondVariationOf h))

open LiteralPhysicalPerturbationModel public

physicalWilsonDefect :
  ∀ {Perturbation Plaquette GaugeIndex ConstraintIndex} →
  LiteralPhysicalPerturbationModel
    Perturbation Plaquette GaugeIndex ConstraintIndex →
  Perturbation → ℚ
physicalWilsonDefect model h =
  physicalWilsonSecondVariationOf model h
  - physicalFlatCurlEnergyOf model h

physicalGaugeDefect :
  ∀ {Perturbation Plaquette GaugeIndex ConstraintIndex} →
  LiteralPhysicalPerturbationModel
    Perturbation Plaquette GaugeIndex ConstraintIndex →
  Perturbation → ℚ
physicalGaugeDefect model h =
  physicalGaugeSecondVariationOf model h
  - physicalFlatDivergenceEnergyOf model h

physicalReferenceIsFlatHodge :
  ∀ {Perturbation Plaquette GaugeIndex ConstraintIndex}
    (model : LiteralPhysicalPerturbationModel
      Perturbation Plaquette GaugeIndex ConstraintIndex)
    h →
  PhysicalHodge.physicalReferenceDifferenceEnergy (physicalFieldOf model h)
  ≡ physicalFlatCurlEnergyOf model h
    + physicalFlatDivergenceEnergyOf model h
physicalReferenceIsFlatHodge model h =
  trans
    (referenceDifferenceMatchesPhysicalField model h)
    (flatHodgeMatchesReference model h)

------------------------------------------------------------------------
-- Physical sharp Wilson and gauge bounds to the literal Hessian.
------------------------------------------------------------------------

literalHessianCoerciveFromPhysicalSharpWilsonGaugeBudgets :
  ∀ {Perturbation Plaquette GaugeIndex ConstraintIndex}
    (model : LiteralPhysicalPerturbationModel
      Perturbation Plaquette GaugeIndex ConstraintIndex)
    h →
  - (Sharp.sharpSixteenAtomBudget * physicalNormSqOf model h)
    ≤ physicalWilsonDefect model h →
  - (SharpPromotion.configuredGaugeHodgeBudget
      * physicalNormSqOf model h)
    ≤ physicalGaugeDefect model h →
  P33.p33PhysicalFloor * physicalNormSqOf model h
    ≤ Jets.literalTotalSecondVariation (secondVariationOf model h)
literalHessianCoerciveFromPhysicalSharpWilsonGaugeBudgets
    model h physicalWilsonLower physicalGaugeLower =
  let
    field = physicalFieldOf model h
    dataSet = secondVariationOf model h

    internalWilsonLower :
      - (Sharp.sharpSixteenAtomBudget
          * Physical.physicalSU2BondNormSq field)
      ≤ Jets.wilsonSecondVariation dataSet
          - physicalFlatCurlEnergyOf model h
    internalWilsonLower =
      subst
        (λ lower →
          lower
          ≤ Jets.wilsonSecondVariation dataSet
              - physicalFlatCurlEnergyOf model h)
        (cong
          (λ normSq → - (Sharp.sharpSixteenAtomBudget * normSq))
          (sym (normMatchesPhysicalField model h)))
        (subst
          (λ upper →
            - (Sharp.sharpSixteenAtomBudget * physicalNormSqOf model h)
            ≤ upper)
          (sym
            (cong
              (_- physicalFlatCurlEnergyOf model h)
              (wilsonSecondVariationMatchesPhysical model h)))
          physicalWilsonLower)

    internalGaugeLower :
      - (SharpPromotion.configuredGaugeHodgeBudget
          * Physical.physicalSU2BondNormSq field)
      ≤ Cancel.gaugeFirstEnergy dataSet
          - physicalFlatDivergenceEnergyOf model h
    internalGaugeLower =
      subst
        (λ lower →
          lower
          ≤ Cancel.gaugeFirstEnergy dataSet
              - physicalFlatDivergenceEnergyOf model h)
        (cong
          (λ normSq →
            - (SharpPromotion.configuredGaugeHodgeBudget * normSq))
          (sym (normMatchesPhysicalField model h)))
        (subst
          (λ upper →
            - (SharpPromotion.configuredGaugeHodgeBudget
                * physicalNormSqOf model h)
            ≤ upper)
          (sym
            (cong
              (_- physicalFlatDivergenceEnergyOf model h)
              (gaugeSecondVariationMatchesPhysical model h)))
          physicalGaugeLower)

    internalCoercive :
      P33.p33PhysicalFloor * Physical.physicalSU2BondNormSq field
      ≤ Jets.literalTotalSecondVariation dataSet
    internalCoercive =
      SharpPromotion.literalHessianCoerciveFromSharpWilsonGaugeBudgets
        field dataSet
        (physicalFlatCurlEnergyOf model h)
        (physicalFlatDivergenceEnergyOf model h)
        (componentMeanZero model h)
        (gaugeExact model h)
        (constraintExact model h)
        (physicalReferenceIsFlatHodge model h)
        internalWilsonLower internalGaugeLower
  in
  subst
    (λ lower → lower ≤ Jets.literalTotalSecondVariation dataSet)
    (cong (P33.p33PhysicalFloor *_)
      (normMatchesPhysicalField model h))
    internalCoercive

literalPhysicalPerturbationAdapterLevel : ProofLevel
literalPhysicalPerturbationAdapterLevel = machineChecked

literalPhysicalFlatHodgeCompatibilityLevel : ProofLevel
literalPhysicalFlatHodgeCompatibilityLevel = machineChecked

literalPhysicalSharpWilsonGaugeCoercivityLevel : ProofLevel
literalPhysicalSharpWilsonGaugeCoercivityLevel = machineChecked
