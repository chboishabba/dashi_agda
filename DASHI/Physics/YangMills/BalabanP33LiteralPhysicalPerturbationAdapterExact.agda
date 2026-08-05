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
-- perturbation h.  The adapter is indexed by h and owns:
--
--   * its literal side-four bond field;
--   * its literal Wilson/gauge/CMP109 second-variation data;
--   * the physical norm, reference-difference and Wilson-second-variation
--     scalars;
--   * exact equalities identifying those physical scalars with the values
--     computed from the bond field and jet data.
--
-- This prevents an arbitrary bond field from being paired with unrelated jet
-- data.  The physical producer must construct this record from its single h;
-- after that construction, the exact cancellation theorem transports a
-- physical Wilson-minus-difference estimate to the literal Hessian without any
-- further compatibility premise.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _*_; -_; _-_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Hodge
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintCancellationExact as Cancel
import DASHI.Physics.YangMills.BalabanP33WilsonSharpDuhamelBudgetExact as Sharp
import DASHI.Physics.YangMills.BalabanP33WilsonSharpBudgetCoercivityExact as SharpPromotion

------------------------------------------------------------------------
-- One-perturbation compatibility bundle.
------------------------------------------------------------------------

record LiteralPhysicalPerturbation
    (Perturbation Plaquette GaugeIndex ConstraintIndex : Set)
    (h : Perturbation) : Set₁ where
  field
    bondField : Hodge.RationalBondField4

    secondVariation :
      Jets.LiteralPhysicalSecondVariation
        Plaquette GaugeIndex ConstraintIndex

    physicalNormSq : ℚ
    physicalReferenceDifference : ℚ
    physicalWilsonSecondVariation : ℚ

    bondNormMatchesPhysical :
      Hodge.bondNormSq bondField ≡ physicalNormSq

    referenceDifferenceMatchesPhysical :
      Hodge.bondReferenceDifferenceEnergy bondField
      ≡ physicalReferenceDifference

    wilsonSecondVariationMatchesPhysical :
      Jets.wilsonSecondVariation secondVariation
      ≡ physicalWilsonSecondVariation

    componentMeanZero : Hodge.BondComponentMeanZero bondField

    gaugeExact :
      Jets.ExactResidualBackground
        (Jets.gaugeResidual secondVariation)

    constraintExact :
      Jets.ExactResidualBackground
        (Jets.constraintResidual secondVariation)

open LiteralPhysicalPerturbation public

physicalWilsonDifference :
  ∀ {Perturbation Plaquette GaugeIndex ConstraintIndex h} →
  LiteralPhysicalPerturbation
    Perturbation Plaquette GaugeIndex ConstraintIndex h → ℚ
physicalWilsonDifference adapter =
  physicalWilsonSecondVariation adapter
  - physicalReferenceDifference adapter

literalWilsonDifferenceMatchesPhysical :
  ∀ {Perturbation Plaquette GaugeIndex ConstraintIndex h}
    (adapter : LiteralPhysicalPerturbation
      Perturbation Plaquette GaugeIndex ConstraintIndex h) →
  Jets.wilsonSecondVariation (secondVariation adapter)
    - Hodge.bondReferenceDifferenceEnergy (bondField adapter)
  ≡ physicalWilsonDifference adapter
literalWilsonDifferenceMatchesPhysical adapter =
  cong₂ _-_
    (wilsonSecondVariationMatchesPhysical adapter)
    (referenceDifferenceMatchesPhysical adapter)

------------------------------------------------------------------------
-- Physical 1/32 Wilson comparison to the literal Hessian.
------------------------------------------------------------------------

literalHessianCoerciveFromPhysicalWilsonDifference :
  ∀ {Perturbation Plaquette GaugeIndex ConstraintIndex h}
    (adapter : LiteralPhysicalPerturbation
      Perturbation Plaquette GaugeIndex ConstraintIndex h) →
  - (P33.p33PhysicalFloor * physicalNormSq adapter)
    ≤ physicalWilsonDifference adapter →
  P33.p33PhysicalFloor * physicalNormSq adapter
    ≤ Jets.literalTotalSecondVariation (secondVariation adapter)
literalHessianCoerciveFromPhysicalWilsonDifference adapter physicalLower =
  let
    internalLower :
      - (P33.p33PhysicalFloor
          * Hodge.bondNormSq (bondField adapter))
      ≤ Jets.wilsonSecondVariation (secondVariation adapter)
          - Hodge.bondReferenceDifferenceEnergy (bondField adapter)
    internalLower =
      subst
        (λ lower →
          lower
          ≤ Jets.wilsonSecondVariation (secondVariation adapter)
              - Hodge.bondReferenceDifferenceEnergy (bondField adapter))
        (cong
          (λ normSq → - (P33.p33PhysicalFloor * normSq))
          (sym (bondNormMatchesPhysical adapter)))
        (subst
          (λ upper →
            - (P33.p33PhysicalFloor * physicalNormSq adapter)
            ≤ upper)
          (sym (literalWilsonDifferenceMatchesPhysical adapter))
          physicalLower)

    internalCoercive :
      P33.p33PhysicalFloor
        * Hodge.bondNormSq (bondField adapter)
      ≤ Jets.literalTotalSecondVariation (secondVariation adapter)
    internalCoercive =
      Cancel.literalHessianCoerciveFromWilsonDifference
        (bondField adapter)
        (secondVariation adapter)
        (componentMeanZero adapter)
        (gaugeExact adapter)
        (constraintExact adapter)
        internalLower
  in
  subst
    (λ lower →
      lower ≤ Jets.literalTotalSecondVariation (secondVariation adapter))
    (cong (P33.p33PhysicalFloor *_)
      (bondNormMatchesPhysical adapter))
    internalCoercive

------------------------------------------------------------------------
-- Sharp sixteen-atom physical Wilson comparison to the literal Hessian.
------------------------------------------------------------------------

literalHessianCoerciveFromPhysicalSharpWilsonBudget :
  ∀ {Perturbation Plaquette GaugeIndex ConstraintIndex h}
    (adapter : LiteralPhysicalPerturbation
      Perturbation Plaquette GaugeIndex ConstraintIndex h) →
  - (Sharp.sharpSixteenAtomBudget * physicalNormSq adapter)
    ≤ physicalWilsonDifference adapter →
  P33.p33PhysicalFloor * physicalNormSq adapter
    ≤ Jets.literalTotalSecondVariation (secondVariation adapter)
literalHessianCoerciveFromPhysicalSharpWilsonBudget
    adapter physicalSharpLower =
  literalHessianCoerciveFromPhysicalWilsonDifference
    adapter
    (SharpPromotion.sharpSignedLowerImpliesPhysicalSignedLower
      (physicalNormSq adapter)
      (physicalWilsonDifference adapter)
      (subst
        (λ normSq → 0ℚ ≤ normSq)
        (bondNormMatchesPhysical adapter)
        (SharpPromotion.bondNormSqNonnegative (bondField adapter)))
      physicalSharpLower)

literalPhysicalPerturbationAdapterLevel : ProofLevel
literalPhysicalPerturbationAdapterLevel = machineChecked

literalPhysicalWilsonDifferenceLevel : ProofLevel
literalPhysicalWilsonDifferenceLevel = machineChecked

literalPhysicalSharpWilsonCoercivityLevel : ProofLevel
literalPhysicalSharpWilsonCoercivityLevel = machineChecked
