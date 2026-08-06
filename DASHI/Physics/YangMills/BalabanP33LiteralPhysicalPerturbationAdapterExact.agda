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
-- DASHI CONTRIBUTION
--
-- Eliminate the remaining same-h coherence socket.  A model no longer accepts
-- an arbitrary `secondVariationOf h` alongside an unrelated physical field.
-- Instead it owns the physical background and perturbation producers, together
-- with the actual gauge and CMP109 residual-jet constructors.  The complete
-- literal Hessian data are then constructed definitionally:
--
--   plaquette jets = right-exponential jets of backgroundOf h and fieldOf h;
--   gauge jet      = gaugeResidualAt (backgroundOf h) (fieldOf h);
--   constraint jet = constraintResidualAt (backgroundOf h) (fieldOf h).
--
-- Thus the Wilson value in the final theorem is literally the physical
-- rational Wilson plaquette sum for that same background and h.  The model may
-- still choose the repository's concrete gauge/CMP109 constructors, but it can
-- no longer pair their output with a separately supplied Wilson Hessian.
--
-- The final theorem consumes exactly two analytic defects on these computed
-- quantities:
--
--   H_W(A;h)-H_W(1;h),
--   H_gf(A;h)-H_div(1;h),
--
-- and returns the literal 1/32 Hessian floor.  No duplicated norm, reference,
-- curl, divergence, Wilson, gauge, or Hessian scalar receipt remains.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.Rational.Base as ℚ using (ℚ; _*_; -_; _-_; _≤_)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2HodgeCoercivityExact as PhysicalHodge
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintCancellationExact as Cancel
import DASHI.Physics.YangMills.BalabanP33WilsonSharpDuhamelBudgetExact as Sharp
import DASHI.Physics.YangMills.BalabanP33WilsonSharpBudgetCoercivityExact as Budget
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonGaugeBoundaryCoercivityExact as Endgame
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as WilsonPhysical

------------------------------------------------------------------------
-- Concrete producer family.
------------------------------------------------------------------------

record LiteralPhysicalPerturbationModel
    (Perturbation GaugeIndex ConstraintIndex : Set) : Set₁ where
  field
    backgroundOf :
      Perturbation → WilsonPhysical.RationalSU2Background4

    physicalFieldOf :
      Perturbation → Physical.PhysicalSU2BondField4

    gaugeResidualAt :
      WilsonPhysical.RationalSU2Background4 →
      Physical.PhysicalSU2BondField4 →
      Jets.FiniteResidualSecondJet GaugeIndex

    constraintResidualAt :
      WilsonPhysical.RationalSU2Background4 →
      Physical.PhysicalSU2BondField4 →
      Jets.FiniteResidualSecondJet ConstraintIndex

    componentMeanZero : ∀ h →
      PhysicalHodge.PhysicalBondComponentMeanZero (physicalFieldOf h)

    gaugeExact : ∀ h →
      Jets.ExactResidualBackground
        (gaugeResidualAt (backgroundOf h) (physicalFieldOf h))

    constraintExact : ∀ h →
      Jets.ExactResidualBackground
        (constraintResidualAt (backgroundOf h) (physicalFieldOf h))

open LiteralPhysicalPerturbationModel public

literalSecondVariationOf :
  ∀ {Perturbation GaugeIndex ConstraintIndex} →
  LiteralPhysicalPerturbationModel
    Perturbation GaugeIndex ConstraintIndex →
  Perturbation →
  Jets.LiteralPhysicalSecondVariation
    WilsonPhysical.Plaquette4 GaugeIndex ConstraintIndex
literalSecondVariationOf model h = record
  { Jets.LiteralPhysicalSecondVariation.plaquettes =
      WilsonPhysical.plaquettes4
  ; Jets.LiteralPhysicalSecondVariation.plaquetteJetData =
      WilsonPhysical.plaquetteJetData
        (backgroundOf model h) (physicalFieldOf model h)
  ; Jets.LiteralPhysicalSecondVariation.gaugeResidual =
      gaugeResidualAt model
        (backgroundOf model h) (physicalFieldOf model h)
  ; Jets.LiteralPhysicalSecondVariation.constraintResidual =
      constraintResidualAt model
        (backgroundOf model h) (physicalFieldOf model h)
  }

literalGaugeResidualIsProducedResidual :
  ∀ {Perturbation GaugeIndex ConstraintIndex}
    (model : LiteralPhysicalPerturbationModel
      Perturbation GaugeIndex ConstraintIndex) h →
  Jets.gaugeResidual (literalSecondVariationOf model h)
  ≡ gaugeResidualAt model
      (backgroundOf model h) (physicalFieldOf model h)
literalGaugeResidualIsProducedResidual model h = refl

literalConstraintResidualIsProducedResidual :
  ∀ {Perturbation GaugeIndex ConstraintIndex}
    (model : LiteralPhysicalPerturbationModel
      Perturbation GaugeIndex ConstraintIndex) h →
  Jets.constraintResidual (literalSecondVariationOf model h)
  ≡ constraintResidualAt model
      (backgroundOf model h) (physicalFieldOf model h)
literalConstraintResidualIsProducedResidual model h = refl

------------------------------------------------------------------------
-- The literal Wilson fold is the concrete physical Wilson fold.
------------------------------------------------------------------------

literalMapSumEqualsIndexedSum :
  ∀ {A : Set} (values : List A) (term : A → ℚ) →
  Jets.sumRational (map term values)
  ≡ Sums.sumRational values term
literalMapSumEqualsIndexedSum [] term = refl
literalMapSumEqualsIndexedSum (value ∷ values) term =
  cong (term value +_)
    (literalMapSumEqualsIndexedSum values term)

literalWilsonIsPhysicalWilson :
  ∀ {Perturbation GaugeIndex ConstraintIndex}
    (model : LiteralPhysicalPerturbationModel
      Perturbation GaugeIndex ConstraintIndex) h →
  Jets.wilsonSecondVariation (literalSecondVariationOf model h)
  ≡ WilsonPhysical.physicalWilsonSecondVariation
      (backgroundOf model h) (physicalFieldOf model h)
literalWilsonIsPhysicalWilson model h =
  literalMapSumEqualsIndexedSum
    WilsonPhysical.plaquettes4
    (WilsonPhysical.plaquetteWilsonSecondVariation
      (backgroundOf model h) (physicalFieldOf model h))

literalWilsonDefectIsPhysicalDefect :
  ∀ {Perturbation GaugeIndex ConstraintIndex}
    (model : LiteralPhysicalPerturbationModel
      Perturbation GaugeIndex ConstraintIndex) h →
  Jets.wilsonSecondVariation (literalSecondVariationOf model h)
    - Endgame.flatCurlEnergy (physicalFieldOf model h)
  ≡ WilsonPhysical.physicalWilsonDefect
      (backgroundOf model h) (physicalFieldOf model h)
literalWilsonDefectIsPhysicalDefect model h =
  trans
    (cong
      (_- Endgame.flatCurlEnergy (physicalFieldOf model h))
      (literalWilsonIsPhysicalWilson model h))
    (sym
      (WilsonPhysical.physicalWilsonDefectIsBackgroundMinusFlatCurl
        (backgroundOf model h) (physicalFieldOf model h)))

------------------------------------------------------------------------
-- The corrected same-background/same-h coercivity theorem.
------------------------------------------------------------------------

literalHessianCoerciveFromSamePhysicalPerturbation :
  ∀ {Perturbation GaugeIndex ConstraintIndex}
    (model : LiteralPhysicalPerturbationModel
      Perturbation GaugeIndex ConstraintIndex)
    h →
  - (Sharp.sharpSixteenAtomBudget
      * Physical.physicalSU2BondNormSq (physicalFieldOf model h))
    ≤ WilsonPhysical.physicalWilsonDefect
        (backgroundOf model h) (physicalFieldOf model h) →
  - (Budget.configuredGaugeHodgeBudget
      * Physical.physicalSU2BondNormSq (physicalFieldOf model h))
    ≤ Cancel.gaugeFirstEnergy (literalSecondVariationOf model h)
      - Endgame.flatDivergenceEnergy (physicalFieldOf model h) →
  P33.p33PhysicalFloor
    * Physical.physicalSU2BondNormSq (physicalFieldOf model h)
  ≤ Jets.literalTotalSecondVariation (literalSecondVariationOf model h)
literalHessianCoerciveFromSamePhysicalPerturbation
    model h physicalWilsonLower gaugeLower =
  let
    dataSet = literalSecondVariationOf model h

    literalWilsonLower :
      - (Sharp.sharpSixteenAtomBudget
          * Physical.physicalSU2BondNormSq (physicalFieldOf model h))
      ≤ Jets.wilsonSecondVariation dataSet
          - Endgame.flatCurlEnergy (physicalFieldOf model h)
    literalWilsonLower =
      subst
        (λ selected →
          - (Sharp.sharpSixteenAtomBudget
              * Physical.physicalSU2BondNormSq (physicalFieldOf model h))
          ≤ selected)
        (sym (literalWilsonDefectIsPhysicalDefect model h))
        physicalWilsonLower
  in
  Endgame.literalHessianCoerciveFromPhysicalWilsonGaugeDefects
    (physicalFieldOf model h)
    dataSet
    (componentMeanZero model h)
    (subst Jets.ExactResidualBackground
      (sym (literalGaugeResidualIsProducedResidual model h))
      (gaugeExact model h))
    (subst Jets.ExactResidualBackground
      (sym (literalConstraintResidualIsProducedResidual model h))
      (constraintExact model h))
    literalWilsonLower
    gaugeLower

literalPhysicalPerturbationAdapterLevel : ProofLevel
literalPhysicalPerturbationAdapterLevel = machineChecked

literalPhysicalWilsonCoherenceLevel : ProofLevel
literalPhysicalWilsonCoherenceLevel = machineChecked

literalSamePerturbationWilsonGaugeCoercivityLevel : ProofLevel
literalSamePerturbationWilsonGaugeCoercivityLevel = machineChecked
