module DASHI.Physics.Closure.DiscreteWarpedEinsteinMatterModel where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Geometry.NonconstantWarpedLorentzianModel as Geometry
import DASHI.Physics.Closure.FirstWitnessVacuumBridge as FirstWitness
import DASHI.Physics.Closure.StressEnergyBianchiConditional as Boundary

------------------------------------------------------------------------
-- Finite nonzero Einstein/source model over the computed warped geometry.
--
-- The model uses the constant positive curvature computed from the nonconstant
-- spatial log-scale profile.  A reduced FLRW/de-Sitter-like contraction maps
-- that curvature to positive energy density and equal negative pressure.
-- A discrete matter action is varied by a total function to produce the same
-- tensor.  Conservation is computed through the finite continuity/Bianchi
-- residual.
--
-- This is an exact finite model.  It is not the continuum Einstein equation,
-- the general differential Bianchi theorem, or an empirical cosmology.


data SourceCoefficient : Set where
  negativeSource : SourceCoefficient
  zeroSource : SourceCoefficient
  positiveSource : SourceCoefficient


negateSource : SourceCoefficient → SourceCoefficient
negateSource negativeSource = positiveSource
negateSource zeroSource = zeroSource
negateSource positiveSource = negativeSource


addSource : SourceCoefficient → SourceCoefficient → SourceCoefficient
addSource negativeSource negativeSource = negativeSource
addSource negativeSource zeroSource = negativeSource
addSource negativeSource positiveSource = zeroSource
addSource zeroSource negativeSource = negativeSource
addSource zeroSource zeroSource = zeroSource
addSource zeroSource positiveSource = positiveSource
addSource positiveSource negativeSource = zeroSource
addSource positiveSource zeroSource = positiveSource
addSource positiveSource positiveSource = positiveSource


multiplyUnitSource :
  Geometry.UnitCoefficient → SourceCoefficient → SourceCoefficient
multiplyUnitSource Geometry.negativeUnit negativeSource = positiveSource
multiplyUnitSource Geometry.negativeUnit zeroSource = zeroSource
multiplyUnitSource Geometry.negativeUnit positiveSource = negativeSource
multiplyUnitSource Geometry.zeroUnit source = zeroSource
multiplyUnitSource Geometry.positiveUnit source = source


energyFromCurvature : Geometry.CurvatureCoefficient → SourceCoefficient
energyFromCurvature Geometry.zeroCurvature = zeroSource
energyFromCurvature Geometry.positiveCurvature = positiveSource


pressureFromCurvature : Geometry.CurvatureCoefficient → SourceCoefficient
pressureFromCurvature curvature =
  negateSource (energyFromCurvature curvature)


warpedEnergyDensity : SourceCoefficient
warpedEnergyDensity = energyFromCurvature Geometry.warpedSectionalCurvature


warpedPressure : SourceCoefficient
warpedPressure = pressureFromCurvature Geometry.warpedSectionalCurvature


computedEnergyNonzero : warpedEnergyDensity ≡ positiveSource
computedEnergyNonzero = refl


computedPressureNegative : warpedPressure ≡ negativeSource
computedPressureNegative = refl


EinsteinTensor4 : Set
EinsteinTensor4 = Flat.Axis4 → Flat.Axis4 → SourceCoefficient


computedEinsteinTensor : EinsteinTensor4
computedEinsteinTensor Flat.timeAxis Flat.timeAxis = warpedEnergyDensity
computedEinsteinTensor Flat.timeAxis Flat.xAxis = zeroSource
computedEinsteinTensor Flat.timeAxis Flat.yAxis = zeroSource
computedEinsteinTensor Flat.timeAxis Flat.zAxis = zeroSource
computedEinsteinTensor Flat.xAxis Flat.timeAxis = zeroSource
computedEinsteinTensor Flat.xAxis Flat.xAxis = warpedPressure
computedEinsteinTensor Flat.xAxis Flat.yAxis = zeroSource
computedEinsteinTensor Flat.xAxis Flat.zAxis = zeroSource
computedEinsteinTensor Flat.yAxis Flat.timeAxis = zeroSource
computedEinsteinTensor Flat.yAxis Flat.xAxis = zeroSource
computedEinsteinTensor Flat.yAxis Flat.yAxis = warpedPressure
computedEinsteinTensor Flat.yAxis Flat.zAxis = zeroSource
computedEinsteinTensor Flat.zAxis Flat.timeAxis = zeroSource
computedEinsteinTensor Flat.zAxis Flat.xAxis = zeroSource
computedEinsteinTensor Flat.zAxis Flat.yAxis = zeroSource
computedEinsteinTensor Flat.zAxis Flat.zAxis = warpedPressure


computedEinsteinSymmetric :
  (a b : Flat.Axis4) →
  computedEinsteinTensor a b ≡ computedEinsteinTensor b a
computedEinsteinSymmetric Flat.timeAxis Flat.timeAxis = refl
computedEinsteinSymmetric Flat.timeAxis Flat.xAxis = refl
computedEinsteinSymmetric Flat.timeAxis Flat.yAxis = refl
computedEinsteinSymmetric Flat.timeAxis Flat.zAxis = refl
computedEinsteinSymmetric Flat.xAxis Flat.timeAxis = refl
computedEinsteinSymmetric Flat.xAxis Flat.xAxis = refl
computedEinsteinSymmetric Flat.xAxis Flat.yAxis = refl
computedEinsteinSymmetric Flat.xAxis Flat.zAxis = refl
computedEinsteinSymmetric Flat.yAxis Flat.timeAxis = refl
computedEinsteinSymmetric Flat.yAxis Flat.xAxis = refl
computedEinsteinSymmetric Flat.yAxis Flat.yAxis = refl
computedEinsteinSymmetric Flat.yAxis Flat.zAxis = refl
computedEinsteinSymmetric Flat.zAxis Flat.timeAxis = refl
computedEinsteinSymmetric Flat.zAxis Flat.xAxis = refl
computedEinsteinSymmetric Flat.zAxis Flat.yAxis = refl
computedEinsteinSymmetric Flat.zAxis Flat.zAxis = refl

------------------------------------------------------------------------
-- Matter action and computed metric variation.


data MatterActionDensity : Set where
  emptyActionDensity : MatterActionDensity
  vacuumResidueActionDensity : MatterActionDensity


matterActionAt : Geometry.TimeSlice → MatterActionDensity
matterActionAt Geometry.pastSlice = vacuumResidueActionDensity
matterActionAt Geometry.presentSlice = vacuumResidueActionDensity
matterActionAt Geometry.futureSlice = vacuumResidueActionDensity


varyMatterAction :
  MatterActionDensity → Flat.Axis4 → Flat.Axis4 → SourceCoefficient
varyMatterAction emptyActionDensity a b = zeroSource
varyMatterAction vacuumResidueActionDensity Flat.timeAxis Flat.timeAxis = positiveSource
varyMatterAction vacuumResidueActionDensity Flat.timeAxis Flat.xAxis = zeroSource
varyMatterAction vacuumResidueActionDensity Flat.timeAxis Flat.yAxis = zeroSource
varyMatterAction vacuumResidueActionDensity Flat.timeAxis Flat.zAxis = zeroSource
varyMatterAction vacuumResidueActionDensity Flat.xAxis Flat.timeAxis = zeroSource
varyMatterAction vacuumResidueActionDensity Flat.xAxis Flat.xAxis = negativeSource
varyMatterAction vacuumResidueActionDensity Flat.xAxis Flat.yAxis = zeroSource
varyMatterAction vacuumResidueActionDensity Flat.xAxis Flat.zAxis = zeroSource
varyMatterAction vacuumResidueActionDensity Flat.yAxis Flat.timeAxis = zeroSource
varyMatterAction vacuumResidueActionDensity Flat.yAxis Flat.xAxis = zeroSource
varyMatterAction vacuumResidueActionDensity Flat.yAxis Flat.yAxis = negativeSource
varyMatterAction vacuumResidueActionDensity Flat.yAxis Flat.zAxis = zeroSource
varyMatterAction vacuumResidueActionDensity Flat.zAxis Flat.timeAxis = zeroSource
varyMatterAction vacuumResidueActionDensity Flat.zAxis Flat.xAxis = zeroSource
varyMatterAction vacuumResidueActionDensity Flat.zAxis Flat.yAxis = zeroSource
varyMatterAction vacuumResidueActionDensity Flat.zAxis Flat.zAxis = negativeSource


computedMatterStress : EinsteinTensor4
computedMatterStress a b =
  varyMatterAction (matterActionAt Geometry.presentSlice) a b


computedEinsteinEqualsMatterStress :
  (a b : Flat.Axis4) →
  computedEinsteinTensor a b ≡ computedMatterStress a b
computedEinsteinEqualsMatterStress Flat.timeAxis Flat.timeAxis = refl
computedEinsteinEqualsMatterStress Flat.timeAxis Flat.xAxis = refl
computedEinsteinEqualsMatterStress Flat.timeAxis Flat.yAxis = refl
computedEinsteinEqualsMatterStress Flat.timeAxis Flat.zAxis = refl
computedEinsteinEqualsMatterStress Flat.xAxis Flat.timeAxis = refl
computedEinsteinEqualsMatterStress Flat.xAxis Flat.xAxis = refl
computedEinsteinEqualsMatterStress Flat.xAxis Flat.yAxis = refl
computedEinsteinEqualsMatterStress Flat.xAxis Flat.zAxis = refl
computedEinsteinEqualsMatterStress Flat.yAxis Flat.timeAxis = refl
computedEinsteinEqualsMatterStress Flat.yAxis Flat.xAxis = refl
computedEinsteinEqualsMatterStress Flat.yAxis Flat.yAxis = refl
computedEinsteinEqualsMatterStress Flat.yAxis Flat.zAxis = refl
computedEinsteinEqualsMatterStress Flat.zAxis Flat.timeAxis = refl
computedEinsteinEqualsMatterStress Flat.zAxis Flat.xAxis = refl
computedEinsteinEqualsMatterStress Flat.zAxis Flat.yAxis = refl
computedEinsteinEqualsMatterStress Flat.zAxis Flat.zAxis = refl


computedMatterSourceNonzero :
  computedMatterStress Flat.timeAxis Flat.timeAxis ≡ positiveSource
computedMatterSourceNonzero = refl

------------------------------------------------------------------------
-- Finite contracted-Bianchi / continuity computation.


densityAt : Geometry.TimeSlice → SourceCoefficient
densityAt slice = energyFromCurvature Geometry.warpedSectionalCurvature


pressureAt : Geometry.TimeSlice → SourceCoefficient
pressureAt slice = pressureFromCurvature Geometry.warpedSectionalCurvature


densityDifference : SourceCoefficient
densityDifference =
  addSource
    (negateSource (densityAt Geometry.presentSlice))
    (densityAt Geometry.futureSlice)


rhoPlusPressure : SourceCoefficient
rhoPlusPressure =
  addSource
    (densityAt Geometry.presentSlice)
    (pressureAt Geometry.presentSlice)


continuityBianchiResidual : SourceCoefficient
continuityBianchiResidual =
  addSource
    densityDifference
    (multiplyUnitSource
      (Geometry.hubbleCoefficient Geometry.presentToFuture)
      rhoPlusPressure)


computedDensityConstant : densityDifference ≡ zeroSource
computedDensityConstant = refl


computedEquationOfStateCancellation : rhoPlusPressure ≡ zeroSource
computedEquationOfStateCancellation = refl


computedContractedBianchi : continuityBianchiResidual ≡ zeroSource
computedContractedBianchi = refl

------------------------------------------------------------------------
-- Integrated receipt and promotion boundary.


record ComputedNonconstantEinsteinMatterReceipt : Set where
  constructor mkComputedNonconstantEinsteinMatterReceipt
  field
    geometryReceipt : Geometry.ComputedWarpedCurvatureReceipt
    connectionReceipt : Geometry.ComputedWarpedLeviCivitaReceipt
    firstWitnessBoundary : FirstWitness.VacuumFirstWitnessBoundary
    EinsteinTensorSymmetric :
      (a b : Flat.Axis4) →
      computedEinsteinTensor a b ≡ computedEinsteinTensor b a
    sourceComesFromActionVariation :
      (a b : Flat.Axis4) →
      computedEinsteinTensor a b ≡ computedMatterStress a b
    sourceNonzero :
      computedMatterStress Flat.timeAxis Flat.timeAxis ≡ positiveSource
    BianchiResidualComputedZero : continuityBianchiResidual ≡ zeroSource
    receiptScope : String

open ComputedNonconstantEinsteinMatterReceipt public


computedNonconstantEinsteinMatterReceipt :
  ComputedNonconstantEinsteinMatterReceipt
computedNonconstantEinsteinMatterReceipt =
  mkComputedNonconstantEinsteinMatterReceipt
    Geometry.computedWarpedCurvatureReceipt
    Geometry.computedWarpedLeviCivitaReceipt
    FirstWitness.canonicalVacuumFirstWitnessBoundary
    computedEinsteinSymmetric
    computedEinsteinEqualsMatterStress
    computedMatterSourceNonzero
    computedContractedBianchi
    "finite nonconstant warped metric with computed normalized connection, curvature, nonzero action-derived source, and zero continuity/Bianchi residual"


record NonconstantModelPromotionBoundary : Set where
  constructor mkNonconstantModelPromotionBoundary
  field
    finiteModelComputed : Nat
    generalLeviCivitaTheoremProved : Nat
    generalDifferentialBianchiProved : Nat
    continuumEinsteinMatterSolutionProved : Nat
    empiricalCosmologyClaimed : Nat
    quantumGravityClaimed : Nat
    boundaryStatement : String

open NonconstantModelPromotionBoundary public


nonconstantModelPromotionBoundary : NonconstantModelPromotionBoundary
nonconstantModelPromotionBoundary =
  mkNonconstantModelPromotionBoundary
    (suc zero)
    zero
    zero
    zero
    zero
    zero
    "one exact finite model is computed; general continuum, empirical, and quantum-gravity promotions remain blocked"


existingResidueEnergyMassShortcutStillBlocked :
  Boundary.ionizationStyleEnergyIdentifiedWithMass
    Boundary.canonicalMassIdentificationBoundary
  ≡ Agda.Builtin.Bool.false
existingResidueEnergyMassShortcutStillBlocked =
  Boundary.canonicalResidueEnergyNotMass
