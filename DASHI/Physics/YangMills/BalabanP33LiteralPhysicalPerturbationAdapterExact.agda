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
-- Bind every representation in the corrected Hodge comparison to the same
-- physical perturbation h.  In addition to the literal bond field and residual
-- jets, the model owns the flat curl and flat divergence energies separately.
-- Their sum is identified pointwise with the repository's full reference
-- difference energy.
--
-- The two physical defects are therefore
--
--   WilsonDefect(h) = H_W(A)[h,h] - H_curl(0)[h,h],
--   GaugeDefect(h)  = H_gf(A)[h,h] - H_div(0)[h,h].
--
-- The final theorem consumes separate sharp bounds on these two defects and
-- transports them to the literal Hessian generated from the same non-phantom
-- h.  An invalid Wilson-minus-full-gradient quantity is no longer present.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _*_; -_; _-_; _≤_)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Hodge
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
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
    bondFieldOf : Perturbation → Hodge.RationalBondField4

    secondVariationOf : Perturbation →
      Jets.LiteralPhysicalSecondVariation
        Plaquette GaugeIndex ConstraintIndex

    physicalNormSqOf : Perturbation → ℚ
    physicalReferenceDifferenceOf : Perturbation → ℚ
    physicalWilsonSecondVariationOf : Perturbation → ℚ
    physicalGaugeSecondVariationOf : Perturbation → ℚ
    physicalFlatCurlEnergyOf : Perturbation → ℚ
    physicalFlatDivergenceEnergyOf : Perturbation → ℚ

    bondNormMatchesPhysical : ∀ h →
      Hodge.bondNormSq (bondFieldOf h) ≡ physicalNormSqOf h

    referenceDifferenceMatchesPhysical : ∀ h →
      Hodge.bondReferenceDifferenceEnergy (bondFieldOf h)
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
      Hodge.BondComponentMeanZero (bondFieldOf h)

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
  Hodge.bondReferenceDifferenceEnergy (bondFieldOf model h)
  ≡ physicalFlatCurlEnergyOf model h
    + physicalFlatDivergenceEnergyOf model h
physicalReferenceIsFlatHodge model h =
  Relation.Binary.PropositionalEquality.trans
    (referenceDifferenceMatchesPhysical model h)
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
    internalWilsonLower :
      - (Sharp.sharpSixteenAtomBudget
          * Hodge.bondNormSq (bondFieldOf model h))
      ≤ Jets.wilsonSecondVariation (secondVariationOf model h)
          - physicalFlatCurlEnergyOf model h
    internalWilsonLower =
      subst
        (λ lower →
          lower
          ≤ Jets.wilsonSecondVariation (secondVariationOf model h)
              - physicalFlatCurlEnergyOf model h)
        (cong
          (λ normSq → - (Sharp.sharpSixteenAtomBudget * normSq))
          (sym (bondNormMatchesPhysical model h)))
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
          * Hodge.bondNormSq (bondFieldOf model h))
      ≤ Cancel.gaugeFirstEnergy (secondVariationOf model h)
          - physicalFlatDivergenceEnergyOf model h
    internalGaugeLower =
      subst
        (λ lower →
          lower
          ≤ Cancel.gaugeFirstEnergy (secondVariationOf model h)
              - physicalFlatDivergenceEnergyOf model h)
        (cong
          (λ normSq →
            - (SharpPromotion.configuredGaugeHodgeBudget * normSq))
          (sym (bondNormMatchesPhysical model h)))
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
      P33.p33PhysicalFloor
        * Hodge.bondNormSq (bondFieldOf model h)
      ≤ Jets.literalTotalSecondVariation (secondVariationOf model h)
    internalCoercive =
      SharpPromotion.literalHessianCoerciveFromSharpWilsonGaugeBudgets
        (bondFieldOf model h)
        (secondVariationOf model h)
        (physicalFlatCurlEnergyOf model h)
        (physicalFlatDivergenceEnergyOf model h)
        (componentMeanZero model h)
        (gaugeExact model h)
        (constraintExact model h)
        (physicalReferenceIsFlatHodge model h)
        internalWilsonLower internalGaugeLower
  in
  subst
    (λ lower →
      lower ≤ Jets.literalTotalSecondVariation (secondVariationOf model h))
    (cong (P33.p33PhysicalFloor *_)
      (bondNormMatchesPhysical model h))
    internalCoercive

literalPhysicalPerturbationAdapterLevel : ProofLevel
literalPhysicalPerturbationAdapterLevel = machineChecked

literalPhysicalFlatHodgeCompatibilityLevel : ProofLevel
literalPhysicalFlatHodgeCompatibilityLevel = machineChecked

literalPhysicalSharpWilsonGaugeCoercivityLevel : ProofLevel
literalPhysicalSharpWilsonGaugeCoercivityLevel = machineChecked
