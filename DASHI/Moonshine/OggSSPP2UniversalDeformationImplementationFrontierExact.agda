module DASHI.Moonshine.OggSSPP2UniversalDeformationImplementationFrontierExact where

------------------------------------------------------------------------
-- p=2 UNIVERSAL-DEFORMATION IMPLEMENTATION FRONTIER
--
-- REPO AUDIT RESULT
--
-- The universal-deformation source socket requires an actual complete local
-- Witt-vector power-series base W(k)[[t]] before the elliptic family and
-- Gamma_0(4) marked states can be implemented.
--
-- The strongest existing repository Witt/Frobenius owner,
--
--   DASHI.Physics.Closure.ArithmeticCohomologyReceiptSurface
--
-- explicitly records crystalline/Witt/Frobenius as a TARGET SURFACE ONLY and
-- states that no Witt-vector construction is proved there.
--
-- Therefore that receipt cannot be used to instantiate the universal
-- deformation base by provenance/name alone.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.ArithmeticCohomologyReceiptSurface as Cohomology
import DASHI.Moonshine.OggSSPP2SupersingularUniversalDeformationSourceExact as Universal
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Existing Witt receipt is explicitly nonconstructive.
------------------------------------------------------------------------

existingWittComparisonProved :
  Cohomology.crystallineComparisonProved
    Cohomology.canonicalCrystallineWittFrobeniusReceiptSurface
  ≡ false
existingWittComparisonProved =
  Cohomology.crystallineComparisonProvedIsFalse
    Cohomology.canonicalCrystallineWittFrobeniusReceiptSurface

data TargetSurfaceCreatesWittVectorRing : Set where

targetSurfaceDoesNotCreateWittVectorRing :
  TargetSurfaceCreatesWittVectorRing -> ⊥
targetSurfaceDoesNotCreateWittVectorRing ()

------------------------------------------------------------------------
-- 2. Exact implementation dependency chain.
------------------------------------------------------------------------

data UniversalDeformationImplementationResidual : Set where
  missingWittVectorRingCarrier :
    UniversalDeformationImplementationResidual

  missingCompleteLocalPowerSeriesBase :
    UniversalDeformationImplementationResidual

  missingSupersingularUniversalEllipticFamily :
    UniversalDeformationImplementationResidual

  missingGamma0FourMarkedDeformationStates :
    UniversalDeformationImplementationResidual

  missingTenStateClassificationBidi :
    UniversalDeformationImplementationResidual

firstImplementationResidual :
  UniversalDeformationImplementationResidual
firstImplementationResidual =
  missingWittVectorRingCarrier

------------------------------------------------------------------------
-- 3. What would count as paying the first two foundations.
------------------------------------------------------------------------

record WittPowerSeriesBaseImplementation : Set₁ where
  field
    ResidueField : Set
    WittRing : Set
    FormalParameter : Set
    PowerSeriesBase : Set

    wittRingConstructed : Bool
    wittRingConstructedIsTrue :
      wittRingConstructed ≡ true

    powerSeriesBaseConstructed : Bool
    powerSeriesBaseConstructedIsTrue :
      powerSeriesBaseConstructed ≡ true

    completeLocalStructureConstructed : Bool
    completeLocalStructureConstructedIsTrue :
      completeLocalStructureConstructed ≡ true

open WittPowerSeriesBaseImplementation public

record UniversalDeformationImplementation
  (base : WittPowerSeriesBaseImplementation) : Set₁ where
  field
    sourceDatum :
      Universal.SupersingularUniversalDeformationDatum

    sourceUsesImplementedBase : Bool
    sourceUsesImplementedBaseIsTrue :
      sourceUsesImplementedBase ≡ true

open UniversalDeformationImplementation public

------------------------------------------------------------------------
-- 4. Promotion firewall.
------------------------------------------------------------------------

data ArithmeticCohomologyTargetReceiptPaysUniversalDeformationBase : Set where

cohomologyTargetReceiptDoesNotPayUniversalDeformationBase :
  ArithmeticCohomologyTargetReceiptPaysUniversalDeformationBase -> ⊥
cohomologyTargetReceiptDoesNotPayUniversalDeformationBase ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record UniversalDeformationImplementationFrontierBoundary : Set where
  constructor universal-deformation-implementation-frontier-boundary
  field
    existingWittReceiptInspected : Bool
    existingWittReceiptIsTargetOnly : Bool
    existingWittReceiptPromotedToConstruction : Bool
    wittVectorRingCarrierRequired : Bool
    completeLocalPowerSeriesBaseRequired : Bool
    universalEllipticFamilyRequiredAfterBase : Bool
    gamma0FourMarkedStatesRequiredAfterFamily : Bool
    tenStateBidiRequiredAfterMarkedStates : Bool
    firstResidualIsWittVectorRingCarrier : Bool

canonicalUniversalDeformationImplementationFrontierBoundary :
  UniversalDeformationImplementationFrontierBoundary
canonicalUniversalDeformationImplementationFrontierBoundary =
  universal-deformation-implementation-frontier-boundary
    true true false true true true true true true
