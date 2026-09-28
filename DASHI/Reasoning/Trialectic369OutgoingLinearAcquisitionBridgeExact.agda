module DASHI.Reasoning.Trialectic369OutgoingLinearAcquisitionBridgeExact where

------------------------------------------------------------------------
-- TRIALECTIC OUTGOING RECOGNITION -> ACTUAL LINEAR MULTIPLICITY ACQUISITION
--
-- DASHI CONTRIBUTION
--
-- The corrected Monster 3B representation lane already owns the Pareto target:
--
--   ActualLinearMultiplicityAcquisition
--
-- which packages on one same-object route:
--
--   * the literal Monster VOA/action weld,
--   * linearity on that literal action,
--   * grade-2 / weight-two linear realization,
--   * the literal linear zeta sector W_zeta,
--   * S_zeta = Hom_E(H_zeta,W_zeta),
--   * source-native multiplicity action/intertwiner obligations.
--
-- The trialectic outgoing residual should therefore consume ONE such
-- acquisition object, not independently ask for a Fin90 permutation action,
-- a Hom-space, an evaluation map, and an inertia lift.
--
-- This module compiles the canonical linear multiplicity route from an
-- acquisition and keeps the optional finite 10x9/9/18 basis route behind the
-- repo's explicit basis-preservation receipt.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimMonster3BActualLinearMultiplicityAcquisitionExact as Acquisition
import DASHI.Wikimedia.IbrahimMonster3BLinearMultiplicityHomSpaceExact as Hom
import DASHI.Moonshine.Monster3BNormalizerCocycleCancellationExact as Cocycle
import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as LinearZeta
import DASHI.Wikimedia.IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact as WrongType
import DASHI.Reasoning.Trialectic369LinearMultiplicityBasisSpecialisationCompilerExact as FiniteCompiler

------------------------------------------------------------------------
-- 1. One acquisition owns the actual linear multiplicity Hom-space.
------------------------------------------------------------------------

acquiredHomSpace :
  ∀ {Monster K : Set} ->
  Acquisition.ActualLinearMultiplicityAcquisition {Monster} {K} ->
  Hom.ActualLinearMultiplicityHomSpace
acquiredHomSpace =
  Acquisition.multiplicityHomSpace

acquiredLinearZetaProducer :
  ∀ {Monster K : Set} ->
  Acquisition.ActualLinearMultiplicityAcquisition {Monster} {K} ->
  LinearZeta.LinearSingleActionProducer
acquiredLinearZetaProducer =
  Acquisition.linearZetaProducer

------------------------------------------------------------------------
-- 2. Compile the canonical linear multiplicity route.
------------------------------------------------------------------------

canonicalLinearRouteFromAcquisition :
  ∀ {Monster K : Set} ->
  Acquisition.ActualLinearMultiplicityAcquisition {Monster} {K} ->
  WrongType.CanonicalLinearMultiplicityRoute
canonicalLinearRouteFromAcquisition acquisition =
  record
    { linearRepresentation =
        Hom.sameObjectLinearRepresentation
          (acquiredHomSpace acquisition)

    ; sourcePaidTwelvePlusSeventyEightCharacter =
        Hom.sourcePaidCharacterOnSameMultiplicity
          (acquiredHomSpace acquisition)

    ; sameObjectWithChosenZetaMultiplicity =
        Cocycle.Multiplicity
          (Hom.cocycleCompensatedAction
            (acquiredHomSpace acquisition))
        ≡
        Linear.Vector
          (WrongType.linearCarrier
            (Hom.sameObjectLinearRepresentation
              (acquiredHomSpace acquisition)))

    ; linearEvaluationIntertwiner =
        Hom.evaluationIsLinearIntertwiner
          (acquiredHomSpace acquisition)
    }

------------------------------------------------------------------------
-- 3. The linear route does NOT itself construct a basis specialisation.
------------------------------------------------------------------------

data AcquisitionCreatesPermutationBasisReceipt : Set where
data AcquisitionCreatesSheet9LinearSubrepresentation : Set where
data AcquisitionCreatesModeBlock18LinearSubrepresentation : Set where

acquisitionDoesNotCreatePermutationBasisReceipt :
  AcquisitionCreatesPermutationBasisReceipt -> ⊥
acquisitionDoesNotCreatePermutationBasisReceipt ()

acquisitionDoesNotCreateSheet9LinearSubrepresentation :
  AcquisitionCreatesSheet9LinearSubrepresentation -> ⊥
acquisitionDoesNotCreateSheet9LinearSubrepresentation ()

acquisitionDoesNotCreateModeBlock18LinearSubrepresentation :
  AcquisitionCreatesModeBlock18LinearSubrepresentation -> ⊥
acquisitionDoesNotCreateModeBlock18LinearSubrepresentation ()

------------------------------------------------------------------------
-- 4. If a separate basis-preservation receipt is supplied, the finite
--    trialectic coordinate compilers become available on THIS SAME route.
------------------------------------------------------------------------

OptionalFiniteBasisRoute :
  ∀ {Monster K : Set} ->
  (acquisition :
    Acquisition.ActualLinearMultiplicityAcquisition {Monster} {K}) ->
  Set₁
OptionalFiniteBasisRoute acquisition =
  WrongType.PermutationBasisPromotionReceipt
    (canonicalLinearRouteFromAcquisition acquisition)

optionalFiniteBasisCompilerBoundary :
  FiniteCompiler.Trialectic369LinearMultiplicityBasisSpecialisationBoundary
optionalFiniteBasisCompilerBoundary =
  FiniteCompiler.canonicalTrialectic369LinearMultiplicityBasisSpecialisationBoundary

finiteNineSheetCompilerAvailableConditionally :
  FiniteCompiler.selectedNineSheetCompilerAvailable
    optionalFiniteBasisCompilerBoundary
  ≡ true
finiteNineSheetCompilerAvailableConditionally = refl

finiteModeBlock18CompilerAvailableConditionally :
  FiniteCompiler.frickeStableEighteenBlockCompilerAvailable
    optionalFiniteBasisCompilerBoundary
  ≡ true
finiteModeBlock18CompilerAvailableConditionally = refl

basisSpecialisationNotManufactured :
  FiniteCompiler.basisSpecialisationInhabitedHere
    optionalFiniteBasisCompilerBoundary
  ≡ false
basisSpecialisationNotManufactured = refl

------------------------------------------------------------------------
-- 5. The acquisition frontier is now the one external/same-object target.
------------------------------------------------------------------------

acquisitionFrontier :
  Acquisition.ActualLinearMultiplicityAcquisitionFrontier
acquisitionFrontier =
  Acquisition.currentActualLinearMultiplicityAcquisitionFrontier

canonicalLinearHomTargetNamed :
  Acquisition.canonicalLinearHomTargetNamed acquisitionFrontier
  ≡ true
canonicalLinearHomTargetNamed = refl

finiteNinetyPermutationRouteNotCanonical :
  Acquisition.finiteNinetyPermutationRouteIsCanonical acquisitionFrontier
  ≡ false
finiteNinetyPermutationRouteNotCanonical = refl

actualLinearActionStillOpen :
  Acquisition.actualLinearActionPaid acquisitionFrontier
  ≡ false
actualLinearActionStillOpen = refl

sourceNativeInertiaSameActionStillOpen :
  Acquisition.sourceNativeInertiaSameActionPaid acquisitionFrontier
  ≡ false
sourceNativeInertiaSameActionStillOpen = refl

actualTwelveSeventyEightIntertwinerStillOpen :
  Acquisition.actualTwelveSeventyEightIntertwinerPaid acquisitionFrontier
  ≡ false
actualTwelveSeventyEightIntertwinerStillOpen = refl

------------------------------------------------------------------------
-- 6. Machine-readable boundary.
------------------------------------------------------------------------

record Trialectic369OutgoingLinearAcquisitionBridgeBoundary : Set where
  constructor trialectic-369-outgoing-linear-acquisition-bridge-boundary
  field
    oneAcquisitionOwnsLinearZetaAndHomSpace : Bool
    canonicalLinearRouteCompiledFromAcquisition : Bool
    finiteNinetyPermutationRouteNotCanonical : Bool
    basisSpecialisationSeparateReceiptRequired : Bool
    finiteNineSheetCompilerAvailableAfterReceipt : Bool
    finiteEighteenBlockCompilerAvailableAfterReceipt : Bool

    acquisitionInhabitedHere : Bool
    actualLinearActionPaid : Bool
    sourceNativeInertiaSameActionPaid : Bool
    actualTwelveSeventyEightIntertwinerPaid : Bool

canonicalTrialectic369OutgoingLinearAcquisitionBridgeBoundary :
  Trialectic369OutgoingLinearAcquisitionBridgeBoundary
canonicalTrialectic369OutgoingLinearAcquisitionBridgeBoundary =
  trialectic-369-outgoing-linear-acquisition-bridge-boundary
    true true true true true true
    false false false false
