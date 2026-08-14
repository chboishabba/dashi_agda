module DASHI.Physics.YangMills.BalabanP33SelectedBackgroundFiniteCoercivityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Assemble the finite-volume endpoint with a single perturbation object.  The
-- literal Wilson fold, physical background, physical tangent field, covariant
-- gauge residual and constraint residual all belong to the same h.  The gauge
-- residual is constructed canonically from that background and h; callers
-- cannot replace it by an unrelated scalar or independently supplied jet.
--
-- Inputs left to the selected-background construction are precisely:
--
--   * the relaxed inverse-link radius N(U_b^-1-1) <= 4 rho^2;
--   * the actual plaquette-local signed Wilson theorem for the same U and h;
--   * componentwise mean zero and the literal constraint residual.
--
-- From these, this module produces the actual literal Hessian bounds
--
--   H_A[h,h] >= (10739/196608) ||h||^2
--              >= (1/32) ||h||^2.
--
-- The preceding counterexample proves that the first input alone cannot
-- manufacture the second.  This theorem therefore closes all algebra and
-- same-h wiring after, but not before, the genuine selected-background W-local
-- producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (_*_; -_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2HodgeCoercivityExact as Hodge
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintCancellationExact as Cancel
import DASHI.Physics.YangMills.BalabanP33LiteralPhysicalPerturbationAdapterExact as SameH
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeResidualExact as GaugeResidual
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeSignedLowerExact as SignedGauge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as RelaxedGauge
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as WilsonGlobal
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLocalToSharpDefectExact as WilsonSharp
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonGaugeBoundaryCoercivityExact as Boundary
import DASHI.Physics.YangMills.BalabanP33WilsonSharpDuhamelBudgetExact as Sharp
import DASHI.Physics.YangMills.BalabanP33WilsonSharpBudgetCoercivityExact as Budget
import DASHI.Physics.YangMills.BalabanP33PhysicalTerminalHessianCoercivityExact as Terminal
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33

record SelectedBackgroundPerturbationModel
    (Perturbation ConstraintIndex : Set) : Set₁ where
  field
    backgroundOf : Perturbation → Physical.RationalSU2Background4
    physicalFieldOf : Perturbation → Coordinates.PhysicalSU2BondField4
    constraintResidualAt :
      Perturbation → Jets.FiniteResidualSecondJet ConstraintIndex
    meanZero : ∀ h → Hodge.PhysicalBondComponentMeanZero (physicalFieldOf h)
    constraintExact : ∀ h →
      Jets.ExactResidualBackground (constraintResidualAt h)

open SelectedBackgroundPerturbationModel public

samePhysicalModel :
  ∀ {Perturbation ConstraintIndex} →
  SelectedBackgroundPerturbationModel Perturbation ConstraintIndex →
  SameH.LiteralPhysicalPerturbationModel
    Perturbation FlatGauge.GaugeCoordinate4 ConstraintIndex
samePhysicalModel model = record
  { SameH.LiteralPhysicalPerturbationModel.backgroundOf = backgroundOf model
  ; SameH.LiteralPhysicalPerturbationModel.physicalFieldOf = physicalFieldOf model
  ; SameH.LiteralPhysicalPerturbationModel.gaugeResidualAt = λ h →
      GaugeResidual.backgroundGaugeResidual
        (backgroundOf model h) (physicalFieldOf model h)
  ; SameH.LiteralPhysicalPerturbationModel.constraintResidualAt =
      constraintResidualAt model
  ; SameH.LiteralPhysicalPerturbationModel.meanZero = meanZero model
  ; SameH.LiteralPhysicalPerturbationModel.gaugeExact = λ h →
      GaugeResidual.backgroundGaugeResidualExact
        (backgroundOf model h) (physicalFieldOf model h)
  ; SameH.LiteralPhysicalPerturbationModel.constraintExact =
      constraintExact model
  }

selectedLiteralSecondVariation :
  ∀ {Perturbation ConstraintIndex}
    (model : SelectedBackgroundPerturbationModel
      Perturbation ConstraintIndex) →
  Perturbation →
  Jets.LiteralPhysicalSecondVariation
    Physical.Plaquette4 FlatGauge.GaugeCoordinate4 ConstraintIndex
selectedLiteralSecondVariation model =
  SameH.literalSecondVariationOf (samePhysicalModel model)

configuredGaugeCoefficientExact :
  (+ 64 / 1) * SignedGauge.rho
  ≡ Budget.configuredGaugeHodgeBudget
configuredGaugeCoefficientExact = ℚRing.solve []

selectedGaugeFirstLower :
  ∀ {Perturbation ConstraintIndex}
    (model : SelectedBackgroundPerturbationModel
      Perturbation ConstraintIndex)
    h →
  RelaxedGauge.RelaxedInverseLinkRadius (backgroundOf model h) →
  - (Budget.configuredGaugeHodgeBudget
      * Coordinates.physicalSU2BondNormSq (physicalFieldOf model h))
  ≤ Cancel.gaugeFirstEnergy (selectedLiteralSecondVariation model h)
      - Boundary.flatDivergenceEnergy (physicalFieldOf model h)
selectedGaugeFirstLower model h radius =
  let
    background = backgroundOf model h
    fieldValue = physicalFieldOf model h
    residual = GaugeResidual.backgroundGaugeResidual background fieldValue

    secondLower =
      RelaxedGauge.backgroundGaugeResidualSignedLowerSixtyFourRelaxed
        background fieldValue radius

    firstLower :
      - (((+ 64 / 1) * SignedGauge.rho)
          * Coordinates.physicalSU2BondNormSq fieldValue)
      ≤ Jets.residualFirstNormSquared residual
          - Boundary.flatDivergenceEnergy fieldValue
    firstLower =
      subst
        (λ selectedGauge →
          - (((+ 64 / 1) * SignedGauge.rho)
              * Coordinates.physicalSU2BondNormSq fieldValue)
          ≤ selectedGauge - Boundary.flatDivergenceEnergy fieldValue)
        (Jets.residualSecondVariationAtExactBackground residual
          (GaugeResidual.backgroundGaugeResidualExact background fieldValue))
        secondLower
  in
  subst
    (λ coefficient →
      - (coefficient * Coordinates.physicalSU2BondNormSq fieldValue)
      ≤ Cancel.gaugeFirstEnergy (selectedLiteralSecondVariation model h)
          - Boundary.flatDivergenceEnergy fieldValue)
    configuredGaugeCoefficientExact
    firstLower

selectedWilsonLower :
  ∀ {Perturbation ConstraintIndex}
    (model : SelectedBackgroundPerturbationModel
      Perturbation ConstraintIndex)
    h →
  WilsonGlobal.PhysicalWilsonSignedLocal
    (backgroundOf model h) (physicalFieldOf model h) →
  - (Sharp.sharpSixteenAtomBudget
      * Coordinates.physicalSU2BondNormSq (physicalFieldOf model h))
  ≤ Jets.wilsonSecondVariation (selectedLiteralSecondVariation model h)
      - Boundary.flatCurlEnergy (physicalFieldOf model h)
selectedWilsonLower model h local =
  WilsonSharp.samePhysicalPerturbationWLocalImpliesSharpDefect
    (samePhysicalModel model) h local

selectedBackgroundLiteralHessianTerminalCoefficient :
  ∀ {Perturbation ConstraintIndex}
    (model : SelectedBackgroundPerturbationModel
      Perturbation ConstraintIndex)
    h →
  RelaxedGauge.RelaxedInverseLinkRadius (backgroundOf model h) →
  WilsonGlobal.PhysicalWilsonSignedLocal
    (backgroundOf model h) (physicalFieldOf model h) →
  Terminal.terminalPhysicalCoefficient
      * Coordinates.physicalSU2BondNormSq (physicalFieldOf model h)
  ≤ Jets.literalTotalSecondVariation (selectedLiteralSecondVariation model h)
selectedBackgroundLiteralHessianTerminalCoefficient
    model h radius local =
  let
    fieldValue = physicalFieldOf model h
    dataSet = selectedLiteralSecondVariation model h
    wilsonLower = selectedWilsonLower model h local
    gaugeLower = selectedGaugeFirstLower model h radius
    sharpCoupled = Boundary.boundaryAssistedSharpLower
      fieldValue dataSet wilsonLower gaugeLower
  in
  Terminal.literalHessianCoerciveAtTerminalCoefficient
    fieldValue dataSet
    (meanZero model h)
    (GaugeResidual.backgroundGaugeResidualExact
      (backgroundOf model h) fieldValue)
    (constraintExact model h)
    sharpCoupled

selectedBackgroundLiteralHessianOneThirtySecond :
  ∀ {Perturbation ConstraintIndex}
    (model : SelectedBackgroundPerturbationModel
      Perturbation ConstraintIndex)
    h →
  RelaxedGauge.RelaxedInverseLinkRadius (backgroundOf model h) →
  WilsonGlobal.PhysicalWilsonSignedLocal
    (backgroundOf model h) (physicalFieldOf model h) →
  P33.p33PhysicalFloor
      * Coordinates.physicalSU2BondNormSq (physicalFieldOf model h)
  ≤ Jets.literalTotalSecondVariation (selectedLiteralSecondVariation model h)
selectedBackgroundLiteralHessianOneThirtySecond
    model h radius local =
  let
    fieldValue = physicalFieldOf model h
    dataSet = selectedLiteralSecondVariation model h
    wilsonLower = selectedWilsonLower model h local
    gaugeLower = selectedGaugeFirstLower model h radius
    sharpCoupled = Boundary.boundaryAssistedSharpLower
      fieldValue dataSet wilsonLower gaugeLower
  in
  Terminal.literalHessianCoerciveAtOneThirtySecond
    fieldValue dataSet
    (meanZero model h)
    (GaugeResidual.backgroundGaugeResidualExact
      (backgroundOf model h) fieldValue)
    (constraintExact model h)
    sharpCoupled

selectedBackgroundSameHAssemblyLevel : ProofLevel
selectedBackgroundSameHAssemblyLevel = machineChecked

selectedBackgroundTerminalCoefficientLevel : ProofLevel
selectedBackgroundTerminalCoefficientLevel = machineChecked

selectedBackgroundOneThirtySecondLevel : ProofLevel
selectedBackgroundOneThirtySecondLevel = machineChecked
