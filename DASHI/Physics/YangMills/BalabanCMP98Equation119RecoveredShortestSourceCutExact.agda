{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119RecoveredShortestSourceCutExact where

------------------------------------------------------------------------
-- CMP98 EQ. (119): RECOVERED SHORTEST SOURCE CUT
--
-- Physical side 13 uses historical periodic index 12.  The repaired Path13
-- realization, signed perturbation projection, local scalar action, two-carrier
-- selected-bond Eq.(119), and generic field assembly are already constructed.
--
-- This round further removes the opaque "global/local perturbation semantics"
-- seam.  The repository now has a direct Path13 family compiler that constructs
-- from narrow inputs:
--
--   realization -> erased literal relative contour -> principal Y_x
--   -> outer Y -> Federbush g/Jminus/Ad -> selected-bond Eq.(119)
--   -> positive-bond field derivative.
--
-- Its surviving input frontier is exactly five independently typed payments:
--   1. selected variational/physical Path13 background;
--   2. rational-real ring embedding;
--   3. an ExistingFederbushConventionFamily inhabitant;
--   4. radius-six minus embedding centred for every selected positive bond;
--   5. principal-image admission of each erased literal relative contour.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Equation119DisjunctivePhysicalSourceCutExact as Eq119Cut
import DASHI.Physics.YangMills.BalabanCMP98Equation120RecoveredSourceFrontierRound218Exact as R218
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as Path13Target
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as PerturbationTarget
import DASHI.Physics.YangMills.BalabanCMP98Equation119TwoCarrierSelectedBondExact as TwoCarrier
import DASHI.Physics.YangMills.BalabanRationalUnitQuaternionRealLieAdjointExact as UnitAdjoint
import DASHI.Physics.YangMills.BalabanCMP98Equation119GeometryRelativeContourExact as Geometry
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Path13Family

Path13SelectedPhysicalBackgroundProducer : Set → Set → Set₁
Path13SelectedPhysicalBackgroundProducer =
  Path13Target.SelectedPhysicalBackground13Instantiation

Path13PerturbationCoordinateProducer : Set₁
Path13PerturbationCoordinateProducer =
  PerturbationTarget.Path13GlobalLocalPerturbationSemantics

record RecoveredEq119ShortestSourceStatus : Set where
  field
    pointwiseSemanticFallbackCompilerClosed : Bool
    principalYFederbushIndexPruned : Bool
    selectedCutRadiusPrunedOnShortestRoute : Bool
    selectedPhysicalPeriodicRealizationPruned : Bool
    rawUnitPathRepresentationPruned : Bool
    path13HistoricalPeriodicIndexRepairClosed : Bool
    path13PeriodicRealizationPruned : Bool

    path13PositiveBondPerturbationProjectionClosed : Bool
    path13RationalSignedBondPerturbationProjectionClosed : Bool
    path13CanonicalLocalScalarActionClosed : Bool
    rationalUnitRealLieAdjointCompilerClosed : Bool
    twoCarrierSelectedBondEq119CompilerClosed : Bool
    twoCarrierCoarseBondFieldAssemblyClosed : Bool
    geometryOnlyRelativeContourCompilerClosed : Bool
    path13PrincipalYCompilerClosed : Bool
    path13OuterYCompilerClosed : Bool
    path13TwoCarrierSourceFamilyCompilerClosed : Bool
    path13TwoCarrierFieldDerivativeCompilerClosed : Bool

    path13SelectedPhysicalBackground13Constructed : Bool
    rationalRealRingEmbeddingConstructed : Bool
    federbushConventionFamilyConstructed : Bool
    path13BondCenteredMinusEmbeddingsConstructed : Bool
    path13RelativeContoursPrincipalImageAdmitted : Bool
    path13TwoCarrierSourceFamilyInputsConstructed : Bool
    path13GlobalLocalPerturbationSemanticsConstructed : Bool
    recoveredShortestPhysicalEq119SourceClosed : Bool

    pointwiseSemanticFallbackCompilerClosedIsTrue : pointwiseSemanticFallbackCompilerClosed ≡ true
    principalYFederbushIndexPrunedIsTrue : principalYFederbushIndexPruned ≡ true
    selectedCutRadiusPrunedOnShortestRouteIsTrue : selectedCutRadiusPrunedOnShortestRoute ≡ true
    selectedPhysicalPeriodicRealizationPrunedIsTrue : selectedPhysicalPeriodicRealizationPruned ≡ true
    rawUnitPathRepresentationPrunedIsTrue : rawUnitPathRepresentationPruned ≡ true
    path13HistoricalPeriodicIndexRepairClosedIsTrue : path13HistoricalPeriodicIndexRepairClosed ≡ true
    path13PeriodicRealizationPrunedIsTrue : path13PeriodicRealizationPruned ≡ true
    path13PositiveBondPerturbationProjectionClosedIsTrue : path13PositiveBondPerturbationProjectionClosed ≡ true
    path13RationalSignedBondPerturbationProjectionClosedIsTrue : path13RationalSignedBondPerturbationProjectionClosed ≡ true
    path13CanonicalLocalScalarActionClosedIsTrue : path13CanonicalLocalScalarActionClosed ≡ true
    rationalUnitRealLieAdjointCompilerClosedIsTrue : rationalUnitRealLieAdjointCompilerClosed ≡ true
    twoCarrierSelectedBondEq119CompilerClosedIsTrue : twoCarrierSelectedBondEq119CompilerClosed ≡ true
    twoCarrierCoarseBondFieldAssemblyClosedIsTrue : twoCarrierCoarseBondFieldAssemblyClosed ≡ true
    geometryOnlyRelativeContourCompilerClosedIsTrue : geometryOnlyRelativeContourCompilerClosed ≡ true
    path13PrincipalYCompilerClosedIsTrue : path13PrincipalYCompilerClosed ≡ true
    path13OuterYCompilerClosedIsTrue : path13OuterYCompilerClosed ≡ true
    path13TwoCarrierSourceFamilyCompilerClosedIsTrue : path13TwoCarrierSourceFamilyCompilerClosed ≡ true
    path13TwoCarrierFieldDerivativeCompilerClosedIsTrue : path13TwoCarrierFieldDerivativeCompilerClosed ≡ true

    path13SelectedPhysicalBackground13ConstructedIsFalse : path13SelectedPhysicalBackground13Constructed ≡ false
    rationalRealRingEmbeddingConstructedIsFalse : rationalRealRingEmbeddingConstructed ≡ false
    federbushConventionFamilyConstructedIsFalse : federbushConventionFamilyConstructed ≡ false
    path13BondCenteredMinusEmbeddingsConstructedIsFalse : path13BondCenteredMinusEmbeddingsConstructed ≡ false
    path13RelativeContoursPrincipalImageAdmittedIsFalse : path13RelativeContoursPrincipalImageAdmitted ≡ false
    path13TwoCarrierSourceFamilyInputsConstructedIsFalse : path13TwoCarrierSourceFamilyInputsConstructed ≡ false
    path13GlobalLocalPerturbationSemanticsConstructedIsFalse : path13GlobalLocalPerturbationSemanticsConstructed ≡ false
    recoveredShortestPhysicalEq119SourceClosedIsFalse : recoveredShortestPhysicalEq119SourceClosed ≡ false

open RecoveredEq119ShortestSourceStatus public

canonicalRecoveredEq119ShortestSourceStatus : RecoveredEq119ShortestSourceStatus
canonicalRecoveredEq119ShortestSourceStatus = record
  { pointwiseSemanticFallbackCompilerClosed =
      Eq119Cut.pointwiseSemanticSelectedCutCompilerClosed
        Eq119Cut.canonicalEq119DisjunctivePhysicalSourceStatus
  ; principalYFederbushIndexPruned = true
  ; selectedCutRadiusPrunedOnShortestRoute = true
  ; selectedPhysicalPeriodicRealizationPruned = true
  ; rawUnitPathRepresentationPruned = true
  ; path13HistoricalPeriodicIndexRepairClosed = true
  ; path13PeriodicRealizationPruned = true
  ; path13PositiveBondPerturbationProjectionClosed = true
  ; path13RationalSignedBondPerturbationProjectionClosed = true
  ; path13CanonicalLocalScalarActionClosed = true
  ; rationalUnitRealLieAdjointCompilerClosed = true
  ; twoCarrierSelectedBondEq119CompilerClosed = true
  ; twoCarrierCoarseBondFieldAssemblyClosed = true
  ; geometryOnlyRelativeContourCompilerClosed = true
  ; path13PrincipalYCompilerClosed = true
  ; path13OuterYCompilerClosed = true
  ; path13TwoCarrierSourceFamilyCompilerClosed = true
  ; path13TwoCarrierFieldDerivativeCompilerClosed = true
  ; path13SelectedPhysicalBackground13Constructed = false
  ; rationalRealRingEmbeddingConstructed = false
  ; federbushConventionFamilyConstructed = false
  ; path13BondCenteredMinusEmbeddingsConstructed = false
  ; path13RelativeContoursPrincipalImageAdmitted = false
  ; path13TwoCarrierSourceFamilyInputsConstructed = false
  ; path13GlobalLocalPerturbationSemanticsConstructed = false
  ; recoveredShortestPhysicalEq119SourceClosed = false
  ; pointwiseSemanticFallbackCompilerClosedIsTrue =
      Eq119Cut.pointwiseSemanticSelectedCutCompilerClosedIsTrue
        Eq119Cut.canonicalEq119DisjunctivePhysicalSourceStatus
  ; principalYFederbushIndexPrunedIsTrue = refl
  ; selectedCutRadiusPrunedOnShortestRouteIsTrue = refl
  ; selectedPhysicalPeriodicRealizationPrunedIsTrue = refl
  ; rawUnitPathRepresentationPrunedIsTrue = refl
  ; path13HistoricalPeriodicIndexRepairClosedIsTrue = refl
  ; path13PeriodicRealizationPrunedIsTrue = refl
  ; path13PositiveBondPerturbationProjectionClosedIsTrue = refl
  ; path13RationalSignedBondPerturbationProjectionClosedIsTrue = refl
  ; path13CanonicalLocalScalarActionClosedIsTrue = refl
  ; rationalUnitRealLieAdjointCompilerClosedIsTrue = refl
  ; twoCarrierSelectedBondEq119CompilerClosedIsTrue = refl
  ; twoCarrierCoarseBondFieldAssemblyClosedIsTrue = refl
  ; geometryOnlyRelativeContourCompilerClosedIsTrue = refl
  ; path13PrincipalYCompilerClosedIsTrue = refl
  ; path13OuterYCompilerClosedIsTrue = refl
  ; path13TwoCarrierSourceFamilyCompilerClosedIsTrue = refl
  ; path13TwoCarrierFieldDerivativeCompilerClosedIsTrue = refl
  ; path13SelectedPhysicalBackground13ConstructedIsFalse = refl
  ; rationalRealRingEmbeddingConstructedIsFalse = refl
  ; federbushConventionFamilyConstructedIsFalse = refl
  ; path13BondCenteredMinusEmbeddingsConstructedIsFalse = refl
  ; path13RelativeContoursPrincipalImageAdmittedIsFalse = refl
  ; path13TwoCarrierSourceFamilyInputsConstructedIsFalse = refl
  ; path13GlobalLocalPerturbationSemanticsConstructedIsFalse = refl
  ; recoveredShortestPhysicalEq119SourceClosedIsFalse = refl
  }

path13BackgroundIsSelectedPhysicalBackgroundClosed : RecoveredEq119ShortestSourceStatus → Bool
path13BackgroundIsSelectedPhysicalBackgroundClosed = path13SelectedPhysicalBackground13Constructed

path13BackgroundIsSelectedPhysicalBackgroundClosedIsFalse :
  path13BackgroundIsSelectedPhysicalBackgroundClosed canonicalRecoveredEq119ShortestSourceStatus ≡ false
path13BackgroundIsSelectedPhysicalBackgroundClosedIsFalse =
  path13SelectedPhysicalBackground13ConstructedIsFalse canonicalRecoveredEq119ShortestSourceStatus

perturbationCoordinateSemanticsClosed : RecoveredEq119ShortestSourceStatus → Bool
perturbationCoordinateSemanticsClosed = path13GlobalLocalPerturbationSemanticsConstructed

perturbationCoordinateSemanticsClosedIsFalse :
  perturbationCoordinateSemanticsClosed canonicalRecoveredEq119ShortestSourceStatus ≡ false
perturbationCoordinateSemanticsClosedIsFalse =
  path13GlobalLocalPerturbationSemanticsConstructedIsFalse canonicalRecoveredEq119ShortestSourceStatus

principalYFederbushIndexPruningLevel : ProofLevel
principalYFederbushIndexPruningLevel = R218.cmp98PrincipalYFrontierPrunedRound218Level

selectedCutRadiusPruningLevel : ProofLevel
selectedCutRadiusPruningLevel = R218.cmp98SelectedCutRadiusFrontierPrunedRound218Level

path13HistoricalPeriodicIndexRepairLevel : ProofLevel
path13HistoricalPeriodicIndexRepairLevel = R192.cmp98Path13PhysicalPeriodicIndexRepairRound192Level

pathRealizationPruningLevel : ProofLevel
pathRealizationPruningLevel = R218.cmp98PathRealizationFrontierPrunedRound218Level

recoveredSourceFrontierLevel : ProofLevel
recoveredSourceFrontierLevel = R218.cmp98Equation120RecoveredSourceFrontierRound218Level

path13SelectedPhysicalBackgroundTargetLevel : ProofLevel
path13SelectedPhysicalBackgroundTargetLevel = Path13Target.cmp98Path13SelectedPhysicalBackgroundTargetLevel

path13PositiveBondPerturbationProjectionLevel : ProofLevel
path13PositiveBondPerturbationProjectionLevel = PerturbationTarget.cmp98Path13PositiveBondPerturbationProjectionLevel

path13RationalSignedBondPerturbationProjectionLevel : ProofLevel
path13RationalSignedBondPerturbationProjectionLevel = PerturbationTarget.cmp98Path13RationalSignedBondProjectionLevel

path13CanonicalLocalScalarActionLevel : ProofLevel
path13CanonicalLocalScalarActionLevel = PerturbationTarget.cmp98Path13CanonicalLocalScalarActionLevel

rationalUnitRealLieAdjointCompilerLevel : ProofLevel
rationalUnitRealLieAdjointCompilerLevel = UnitAdjoint.rationalUnitQuaternionRealLieAdjointCompilerLevel

twoCarrierSelectedBondEq119CompilerLevel : ProofLevel
twoCarrierSelectedBondEq119CompilerLevel = TwoCarrier.cmp98Equation119TwoCarrierSelectedBondLevel

twoCarrierCoarseBondFieldAssemblyLevel : ProofLevel
twoCarrierCoarseBondFieldAssemblyLevel = TwoCarrier.cmp98Equation119TwoCarrierFieldAssemblyLevel

geometryOnlyRelativeContourCompilerLevel : ProofLevel
geometryOnlyRelativeContourCompilerLevel = Geometry.cmp98Equation119GeometryOnlyRelativeContourLevel

path13PrincipalYCompilerLevel : ProofLevel
path13PrincipalYCompilerLevel = Path13Family.cmp98Path13PrincipalYCompilerLevel

path13OuterYCompilerLevel : ProofLevel
path13OuterYCompilerLevel = Path13Family.cmp98Path13OuterYCompilerLevel

path13TwoCarrierSourceFamilyCompilerLevel : ProofLevel
path13TwoCarrierSourceFamilyCompilerLevel = Path13Family.cmp98Path13TwoCarrierSourceFamilyCompilerLevel

path13TwoCarrierFieldDerivativeCompilerLevel : ProofLevel
path13TwoCarrierFieldDerivativeCompilerLevel = Path13Family.cmp98Path13TwoCarrierFieldDerivativeCompilerLevel

literalCMP98RecoveredPath13BackgroundSameObjectLevel : ProofLevel
literalCMP98RecoveredPath13BackgroundSameObjectLevel = Path13Target.literalCMP98Path13SelectedPhysicalBackgroundProducerLevel

literalCMP98RecoveredPerturbationCoordinateSemanticsLevel : ProofLevel
literalCMP98RecoveredPerturbationCoordinateSemanticsLevel = Path13Family.literalCMP98Path13TwoCarrierSourceFamilyInputsLevel
