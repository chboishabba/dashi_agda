{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsConcreteT4SemanticsRound519Exact where

------------------------------------------------------------------------
-- GOAL-1 T4 / ROUND519:
-- RESEMANTICIZE ONE CANONICAL C SOURCE INTO CONCRETE LOCAL-QFT ENDPOINTS
--
-- Goal1CanonicalCSource already certifies one literal object's local observable,
-- curvature family, AF/OPE data and stress tensor.  Do not ask a second
-- LiteralYangMillsSemantics to rediscover those facts under opaque predicates.
--
-- Instead define the new T4 predicates extensionally by SAME-OBJECT membership
-- in that certified source object, then copy the literal construction fields
-- unchanged into the new semantics.  All eight T4 endpoint receipts are then
-- constructor/equality facts.
--
-- The physical bill is not deleted: constructing Goal1CanonicalCSource remains
-- the C-source theorem package (R475).  This module only removes the second
-- endpoint-interpretation wall.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; Σ; _,_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayGoal1CanonicalCSourceRound437Exact as CSource

concreteT4Semantics :
  ∀ {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) →
  CSource.Goal1CanonicalCSource Y →
  Top.LiteralYangMillsSemantics C
concreteT4Semantics {C = C} {S = S} Y source = record
  { Top.LiteralYangMillsSemantics.IsCompactSimple =
      Top.IsCompactSimple S
  ; Top.LiteralYangMillsSemantics.IsFourDimensionalEuclidean =
      Top.IsFourDimensionalEuclidean S
  ; Top.LiteralYangMillsSemantics.IsFiniteVolumeCutoffMeasure =
      Top.IsFiniteVolumeCutoffMeasure S
  ; Top.LiteralYangMillsSemantics.IsReflectionPositiveRegularization =
      Top.IsReflectionPositiveRegularization S
  ; Top.LiteralYangMillsSemantics.HasUltravioletYangMillsNormalization =
      Top.HasUltravioletYangMillsNormalization S
  ; Top.LiteralYangMillsSemantics.HasAsymptoticallyFreeScaleTrajectory =
      Top.HasAsymptoticallyFreeScaleTrajectory S

  ; Top.LiteralYangMillsSemantics.IsGaugeInvariantObservable =
      λ observable →
        Σ (Top.CompactSimpleGroup C) λ group →
        Σ (Top.Position C) λ position →
        observable ≡ Top.localObservable Y group position

  ; Top.LiteralYangMillsSemantics.IsLocalObservable =
      λ observable position →
        Σ (Top.CompactSimpleGroup C) λ group →
        observable ≡ Top.localObservable Y group position

  ; Top.LiteralYangMillsSemantics.IsContinuumLimitOf =
      Top.IsContinuumLimitOf S
  ; Top.LiteralYangMillsSemantics.SchwingerBelongsToMeasure =
      Top.SchwingerBelongsToMeasure S
  ; Top.LiteralYangMillsSemantics.IsNontrivialQuantumYangMills =
      Top.IsNontrivialQuantumYangMills S

  ; Top.LiteralYangMillsSemantics.CurvatureOperatorCorrespondence =
      λ group operator →
        ∀ polynomial →
        operator polynomial ≡ Top.curvatureOperator Y group polynomial

  ; Top.LiteralYangMillsSemantics.IsGaugeInvariantLocalOperator =
      λ operator →
        Σ (Top.CompactSimpleGroup C) λ group →
        Σ (Top.CurvaturePolynomial C) λ polynomial →
        operator ≡ Top.curvatureOperator Y group polynomial

  ; Top.LiteralYangMillsSemantics.IsLocalOperator =
      λ operator position →
        Σ (Top.CompactSimpleGroup C) λ group →
        Σ (Top.CurvaturePolynomial C) λ polynomial →
        operator ≡ Top.curvatureOperator Y group polynomial

  ; Top.LiteralYangMillsSemantics.IsPhysicalOPECoefficient =
      λ group left right output position coefficient →
        coefficient
        ≡ Top.opeCoefficient Y group left right output position

  ; Top.LiteralYangMillsSemantics.IsPhysicalOPERemainder =
      λ group left right position depth remainder →
        remainder
        ≡ Top.opeRemainder Y group left right position depth

  ; Top.LiteralYangMillsSemantics.HasShortDistanceAsymptoticFreedom =
      λ group schwinger →
        schwinger ≡ Top.schwinger Y group

  ; Top.LiteralYangMillsSemantics.HasStressTensorAndOPE =
      λ group schwinger stress →
        schwinger ≡ Top.schwinger Y group
        × stress ≡ Top.stressTensor Y group

  ; Top.LiteralYangMillsSemantics.SatisfiesAcceptedWightmanOrOSAxioms =
      Top.SatisfiesAcceptedWightmanOrOSAxioms S
  ; Top.LiteralYangMillsSemantics.IsReconstructedHilbertSpace =
      Top.IsReconstructedHilbertSpace S
  ; Top.LiteralYangMillsSemantics.IsPositiveSelfAdjointHamiltonian =
      Top.IsPositiveSelfAdjointHamiltonian S
  ; Top.LiteralYangMillsSemantics.IsVacuumSectorAndPositiveEnergyComplement =
      Top.IsVacuumSectorAndPositiveEnergyComplement S
  ; Top.LiteralYangMillsSemantics.IsStrictlyPositiveFiniteMassGap =
      Top.IsStrictlyPositiveFiniteMassGap S
  ; Top.LiteralYangMillsSemantics.GaugeSymmetryPreservedAlongConstruction =
      Top.GaugeSymmetryPreservedAlongConstruction S
  ; Top.LiteralYangMillsSemantics.LocalityPreservedAlongConstruction =
      Top.LocalityPreservedAlongConstruction S
  ; Top.LiteralYangMillsSemantics.EuclideanCovariancePreservedAlongConstruction =
      Top.EuclideanCovariancePreservedAlongConstruction S
  ; Top.LiteralYangMillsSemantics.ReflectionPositivityPreservedAlongConstruction =
      Top.ReflectionPositivityPreservedAlongConstruction S
  ; Top.LiteralYangMillsSemantics.PositivityNormalizationPreservedAlongConstruction =
      Top.PositivityNormalizationPreservedAlongConstruction S
  ; Top.LiteralYangMillsSemantics.VolumeCutoffCompatibilityPreserved =
      Top.VolumeCutoffCompatibilityPreserved S
  ; Top.LiteralYangMillsSemantics.PhysicalScaleLowerBoundUniform =
      Top.PhysicalScaleLowerBoundUniform S
  ; Top.LiteralYangMillsSemantics.NoSpectralPollutionBelowGap =
      Top.NoSpectralPollutionBelowGap S
  ; Top.LiteralYangMillsSemantics.NontrivialityPreservedInLimit =
      Top.NontrivialityPreservedInLimit S
  ; Top.LiteralYangMillsSemantics.GapAndClusteringAreDerivedNotAssumed =
      Top.GapAndClusteringAreDerivedNotAssumed S
  ; Top.LiteralYangMillsSemantics.CompactSimpleParameterizationPreserved =
      Top.CompactSimpleParameterizationPreserved S
  }

resemanticizedConstruction :
  ∀ {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (source : CSource.Goal1CanonicalCSource Y) →
  Top.LiteralYangMillsConstruction C
    (concreteT4Semantics Y source)
resemanticizedConstruction Y source = record
  { Top.LiteralYangMillsConstruction.spacetime =
      Top.spacetime Y
  ; Top.LiteralYangMillsConstruction.finiteMeasure =
      Top.finiteMeasure Y
  ; Top.LiteralYangMillsConstruction.continuumMeasure =
      Top.continuumMeasure Y
  ; Top.LiteralYangMillsConstruction.schwinger =
      Top.schwinger Y
  ; Top.LiteralYangMillsConstruction.localObservable =
      Top.localObservable Y
  ; Top.LiteralYangMillsConstruction.curvatureOperator =
      Top.curvatureOperator Y
  ; Top.LiteralYangMillsConstruction.opeCoefficient =
      Top.opeCoefficient Y
  ; Top.LiteralYangMillsConstruction.opeRemainder =
      Top.opeRemainder Y
  ; Top.LiteralYangMillsConstruction.stressTensor =
      Top.stressTensor Y
  ; Top.LiteralYangMillsConstruction.hilbertSpace =
      Top.hilbertSpace Y
  ; Top.LiteralYangMillsConstruction.hamiltonian =
      Top.hamiltonian Y
  ; Top.LiteralYangMillsConstruction.vacuum =
      Top.vacuum Y
  ; Top.LiteralYangMillsConstruction.massGap =
      Top.massGap Y
  }

concreteGaugeInvariantLocalObservable :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : CSource.Goal1CanonicalCSource Y)
    group position →
  Top.IsGaugeInvariantObservable
    (concreteT4Semantics Y source)
    (Top.localObservable (resemanticizedConstruction Y source) group position)
concreteGaugeInvariantLocalObservable source group position =
  group , (position , refl)

concreteLocalObservable :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : CSource.Goal1CanonicalCSource Y)
    group position →
  Top.IsLocalObservable
    (concreteT4Semantics Y source)
    (Top.localObservable (resemanticizedConstruction Y source) group position)
    position
concreteLocalObservable source group position =
  group , refl

concreteCurvatureCorrespondence :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : CSource.Goal1CanonicalCSource Y)
    group →
  Top.CurvatureOperatorCorrespondence
    (concreteT4Semantics Y source)
    group
    (Top.curvatureOperator (resemanticizedConstruction Y source) group)
concreteCurvatureCorrespondence source group polynomial = refl

concreteCurvatureGaugeInvariant :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : CSource.Goal1CanonicalCSource Y)
    group polynomial →
  Top.IsGaugeInvariantLocalOperator
    (concreteT4Semantics Y source)
    (Top.curvatureOperator
      (resemanticizedConstruction Y source) group polynomial)
concreteCurvatureGaugeInvariant source group polynomial =
  group , (polynomial , refl)

concreteCurvatureLocal :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : CSource.Goal1CanonicalCSource Y)
    group polynomial position →
  Top.IsLocalOperator
    (concreteT4Semantics Y source)
    (Top.curvatureOperator
      (resemanticizedConstruction Y source) group polynomial)
    position
concreteCurvatureLocal source group polynomial position =
  group , (polynomial , refl)

concreteShortDistanceAF :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : CSource.Goal1CanonicalCSource Y)
    group →
  Top.HasShortDistanceAsymptoticFreedom
    (concreteT4Semantics Y source)
    group
    (Top.schwinger (resemanticizedConstruction Y source) group)
concreteShortDistanceAF source group = refl

concreteStressAndOPE :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : CSource.Goal1CanonicalCSource Y)
    group →
  Top.HasStressTensorAndOPE
    (concreteT4Semantics Y source)
    group
    (Top.schwinger (resemanticizedConstruction Y source) group)
    (Top.stressTensor (resemanticizedConstruction Y source) group)
concreteStressAndOPE source group = refl , refl

concretePhysicalOPECoefficient :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : CSource.Goal1CanonicalCSource Y)
    group left right output position →
  Top.IsPhysicalOPECoefficient
    (concreteT4Semantics Y source)
    group left right output position
    (Top.opeCoefficient
      (resemanticizedConstruction Y source)
      group left right output position)
concretePhysicalOPECoefficient source group left right output position = refl

concretePhysicalOPERemainder :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : CSource.Goal1CanonicalCSource Y)
    group left right position depth →
  Top.IsPhysicalOPERemainder
    (concreteT4Semantics Y source)
    group left right position depth
    (Top.opeRemainder
      (resemanticizedConstruction Y source)
      group left right position depth)
concretePhysicalOPERemainder source group left right position depth = refl

round519ConcreteT4SemanticsCompilerLevel : ProofLevel
round519ConcreteT4SemanticsCompilerLevel = machineChecked

round519T4EndpointInterpretationLevel : ProofLevel
round519T4EndpointInterpretationLevel = machineChecked

-- The physical theorem package remains exactly the canonical C source.
literalRound519CanonicalCSourceLevel : ProofLevel
literalRound519CanonicalCSourceLevel =
  CSource.literalRound437Goal1CSourceLevel
