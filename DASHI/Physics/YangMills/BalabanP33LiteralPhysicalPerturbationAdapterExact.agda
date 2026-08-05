module DASHI.Physics.YangMills.BalabanP33LiteralPhysicalPerturbationAdapterExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Bind every representation used by the cancellation theorem to one physical
-- perturbation h.  A model owns functions which send the same h to:
--
--   * its literal side-four bond field;
--   * its literal Wilson/gauge/CMP109 second-variation data;
--   * its physical norm, reference-difference and Wilson-second-variation
--     scalars.
--
-- The model also owns exact pointwise identifications between those physical
-- scalars and the values computed from the bond field and jet data.  The index
-- h is therefore not phantom: every component in the theorem is obtained by
-- applying one declared producer family to that same h.
--
-- This prevents an arbitrary bond field from being paired with unrelated jet
-- data.  Once a physical implementation constructs this model, the exact
-- cancellation theorem transports a physical Wilson-minus-difference estimate
-- to the literal Hessian without any additional compatibility premise.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; 0ℚ; _*_; -_; _-_; _≤_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym)

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

    bondNormMatchesPhysical : ∀ h →
      Hodge.bondNormSq (bondFieldOf h) ≡ physicalNormSqOf h

    referenceDifferenceMatchesPhysical : ∀ h →
      Hodge.bondReferenceDifferenceEnergy (bondFieldOf h)
      ≡ physicalReferenceDifferenceOf h

    wilsonSecondVariationMatchesPhysical : ∀ h →
      Jets.wilsonSecondVariation (secondVariationOf h)
      ≡ physicalWilsonSecondVariationOf h

    componentMeanZero : ∀ h →
      Hodge.BondComponentMeanZero (bondFieldOf h)

    gaugeExact : ∀ h →
      Jets.ExactResidualBackground
        (Jets.gaugeResidual (secondVariationOf h))

    constraintExact : ∀ h →
      Jets.ExactResidualBackground
        (Jets.constraintResidual (secondVariationOf h))

open LiteralPhysicalPerturbationModel public

physicalWilsonDifference :
  ∀ {Perturbation Plaquette GaugeIndex ConstraintIndex} →
  LiteralPhysicalPerturbationModel
    Perturbation Plaquette GaugeIndex ConstraintIndex →
  Perturbation → ℚ
physicalWilsonDifference model h =
  physicalWilsonSecondVariationOf model h
  - physicalReferenceDifferenceOf model h

literalWilsonDifferenceMatchesPhysical :
  ∀ {Perturbation Plaquette GaugeIndex ConstraintIndex}
    (model : LiteralPhysicalPerturbationModel
      Perturbation Plaquette GaugeIndex ConstraintIndex)
    h →
  Jets.wilsonSecondVariation (secondVariationOf model h)
    - Hodge.bondReferenceDifferenceEnergy (bondFieldOf model h)
  ≡ physicalWilsonDifference model h
literalWilsonDifferenceMatchesPhysical model h =
  cong₂ _-_
    (wilsonSecondVariationMatchesPhysical model h)
    (referenceDifferenceMatchesPhysical model h)

------------------------------------------------------------------------
-- Physical 1/32 Wilson comparison to the literal Hessian.
------------------------------------------------------------------------

literalHessianCoerciveFromPhysicalWilsonDifference :
  ∀ {Perturbation Plaquette GaugeIndex ConstraintIndex}
    (model : LiteralPhysicalPerturbationModel
      Perturbation Plaquette GaugeIndex ConstraintIndex)
    h →
  - (P33.p33PhysicalFloor * physicalNormSqOf model h)
    ≤ physicalWilsonDifference model h →
  P33.p33PhysicalFloor * physicalNormSqOf model h
    ≤ Jets.literalTotalSecondVariation (secondVariationOf model h)
literalHessianCoerciveFromPhysicalWilsonDifference
    model h physicalLower =
  let
    internalLower :
      - (P33.p33PhysicalFloor
          * Hodge.bondNormSq (bondFieldOf model h))
      ≤ Jets.wilsonSecondVariation (secondVariationOf model h)
          - Hodge.bondReferenceDifferenceEnergy (bondFieldOf model h)
    internalLower =
      subst
        (λ lower →
          lower
          ≤ Jets.wilsonSecondVariation (secondVariationOf model h)
              - Hodge.bondReferenceDifferenceEnergy (bondFieldOf model h))
        (cong
          (λ normSq → - (P33.p33PhysicalFloor * normSq))
          (sym (bondNormMatchesPhysical model h)))
        (subst
          (λ upper →
            - (P33.p33PhysicalFloor * physicalNormSqOf model h)
            ≤ upper)
          (sym (literalWilsonDifferenceMatchesPhysical model h))
          physicalLower)

    internalCoercive :
      P33.p33PhysicalFloor
        * Hodge.bondNormSq (bondFieldOf model h)
      ≤ Jets.literalTotalSecondVariation (secondVariationOf model h)
    internalCoercive =
      Cancel.literalHessianCoerciveFromWilsonDifference
        (bondFieldOf model h)
        (secondVariationOf model h)
        (componentMeanZero model h)
        (gaugeExact model h)
        (constraintExact model h)
        internalLower
  in
  subst
    (λ lower →
      lower ≤ Jets.literalTotalSecondVariation (secondVariationOf model h))
    (cong (P33.p33PhysicalFloor *_)
      (bondNormMatchesPhysical model h))
    internalCoercive

------------------------------------------------------------------------
-- Sharp sixteen-atom physical Wilson comparison to the literal Hessian.
------------------------------------------------------------------------

literalHessianCoerciveFromPhysicalSharpWilsonBudget :
  ∀ {Perturbation Plaquette GaugeIndex ConstraintIndex}
    (model : LiteralPhysicalPerturbationModel
      Perturbation Plaquette GaugeIndex ConstraintIndex)
    h →
  - (Sharp.sharpSixteenAtomBudget * physicalNormSqOf model h)
    ≤ physicalWilsonDifference model h →
  P33.p33PhysicalFloor * physicalNormSqOf model h
    ≤ Jets.literalTotalSecondVariation (secondVariationOf model h)
literalHessianCoerciveFromPhysicalSharpWilsonBudget
    model h physicalSharpLower =
  literalHessianCoerciveFromPhysicalWilsonDifference
    model h
    (SharpPromotion.sharpSignedLowerImpliesPhysicalSignedLower
      (physicalNormSqOf model h)
      (physicalWilsonDifference model h)
      (subst
        (λ normSq → 0ℚ ≤ normSq)
        (bondNormMatchesPhysical model h)
        (SharpPromotion.bondNormSqNonnegative (bondFieldOf model h)))
      physicalSharpLower)

literalPhysicalPerturbationAdapterLevel : ProofLevel
literalPhysicalPerturbationAdapterLevel = machineChecked

literalPhysicalWilsonDifferenceLevel : ProofLevel
literalPhysicalWilsonDifferenceLevel = machineChecked

literalPhysicalSharpWilsonCoercivityLevel : ProofLevel
literalPhysicalSharpWilsonCoercivityLevel = machineChecked
