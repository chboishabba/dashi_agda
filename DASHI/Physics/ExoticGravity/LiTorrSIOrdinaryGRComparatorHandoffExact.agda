module DASHI.Physics.ExoticGravity.LiTorrSIOrdinaryGRComparatorHandoffExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.LiTorrSIStressEnergyCompilerWeldExact as SIStress
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryStressEnergyCompilationExact as StressCompile
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryStressEnergyScopeBidiExact as Stress
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryGRComparatorCompilationExact as GRCompile
import DASHI.Physics.ExoticGravity.LiTorrGeometryAcquisitionBidiExact as Geometry
import DASHI.Physics.ExoticGravity.LiTorrStandardGRRotatingSourceKernelExact as GR

------------------------------------------------------------------------
-- SI STRESS-ENERGY -> ORDINARY GR COMPARATOR HANDOFF
--
-- A completed SI stress-energy compilation is not itself a GR prediction.
-- Exact geometry, weak-field validity, convention normalization, and numerical
-- evaluation remain explicit downstream obligations.
------------------------------------------------------------------------

compileSIStressEnergyReceipt :
  SIStress.SIStressEnergyWeldInput → Stress.LaboratoryStressEnergyReceipt
compileSIStressEnergyReceipt input =
  StressCompile.compileLaboratoryStressEnergy
    (SIStress.compileSIStressEnergyInput input)

record SIOrdinaryGRHandoffInput : Set₂ where
  constructor si-ordinary-gr-handoff-input
  field
    siStressInput : SIStress.SIStressEnergyWeldInput
    geometryState : Geometry.GeometryClosureState
    geometryIsClosed : Geometry.firstOpenGeometryLeaf geometryState ≡ Geometry.closedGeometry
    rotatingGeometry : GR.RotatingSourceGeometry
    weakFieldKernel : GR.WeakFieldGRKernel rotatingGeometry
    SameApparatusStressGeometryReceipt : Set
    sameApparatusStressGeometryReceipt : SameApparatusStressGeometryReceipt
    ExactGeometryInstantiationReceipt : Set
    exactGeometryInstantiationReceipt : ExactGeometryInstantiationReceipt
    WeakFieldValidityReceipt : Set
    weakFieldValidityReceipt : WeakFieldValidityReceipt
    ConventionNormalizationReceipt : Set
    conventionNormalizationReceipt : ConventionNormalizationReceipt

open SIOrdinaryGRHandoffInput public

compileSIOrdinaryGRRequest :
  SIOrdinaryGRHandoffInput → GRCompile.OrdinaryGREvaluationRequest
compileSIOrdinaryGRRequest input =
  GRCompile.compileOrdinaryGREvaluationRequest
    (GRCompile.same-apparatus-gr-comparator-input
      (SIStress.SIStressEnergyWeldInput.apparatusIdentity
        (SIOrdinaryGRHandoffInput.siStressInput input))
      (compileSIStressEnergyReceipt
        (SIOrdinaryGRHandoffInput.siStressInput input))
      (SIOrdinaryGRHandoffInput.geometryState input)
      (SIOrdinaryGRHandoffInput.geometryIsClosed input)
      (SIOrdinaryGRHandoffInput.rotatingGeometry input)
      (SIOrdinaryGRHandoffInput.weakFieldKernel input)
      (SIOrdinaryGRHandoffInput.SameApparatusStressGeometryReceipt input)
      (SIOrdinaryGRHandoffInput.sameApparatusStressGeometryReceipt input)
      (SIOrdinaryGRHandoffInput.ExactGeometryInstantiationReceipt input)
      (SIOrdinaryGRHandoffInput.exactGeometryInstantiationReceipt input)
      (SIOrdinaryGRHandoffInput.WeakFieldValidityReceipt input)
      (SIOrdinaryGRHandoffInput.weakFieldValidityReceipt input)
      (SIOrdinaryGRHandoffInput.ConventionNormalizationReceipt input)
      (SIOrdinaryGRHandoffInput.conventionNormalizationReceipt input))

record SIOrdinaryGRHandoffBoundary : Set where
  constructor si-ordinary-gr-handoff-boundary
  field
    siStressEnergyEqualsOrdinaryGRPrediction : Bool
    closedGeometryRequired : Bool
    weakFieldValidityRequired : Bool
    conventionNormalizationRequired : Bool
    numericalEvaluationStillRequiredAfterHandoff : Bool
    sameInputPredictionIdentityStillRequired : Bool
    ordinaryGRRequestEqualsResidualAnomaly : Bool
    residualAnomalyEqualsNegativeEffectiveG : Bool

canonicalSIOrdinaryGRHandoffBoundary : SIOrdinaryGRHandoffBoundary
canonicalSIOrdinaryGRHandoffBoundary =
  si-ordinary-gr-handoff-boundary
    false true true true true true false false
