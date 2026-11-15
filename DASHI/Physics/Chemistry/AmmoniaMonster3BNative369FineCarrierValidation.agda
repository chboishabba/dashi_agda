module DASHI.Physics.Chemistry.AmmoniaMonster3BNative369FineCarrierValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaMonster3BNative369FineCarrierExact as N

nativeRoundTrip :
  (n : N.Native369ZetaCoordinate) → N.modelToNative369 (N.native369ToModel n) ≡ n
nativeRoundTrip = N.native369RoundTrip

modelRoundTrip :
  (m : N.MonsterZetaModelBasis) → N.native369ToModel (N.modelToNative369 m) ≡ m
modelRoundTrip = N.model369RoundTrip

nativeBasisLabelChartPaid :
  N.Native369FineCarrierBoundary.fullMonsterZetaModelHasNative369CarrierChart
    N.canonicalNative369FineCarrierBoundary ≡ true
nativeBasisLabelChartPaid = refl

finiteChartIsBasisLabels :
  N.Native369FineCarrierBoundary.native369FiniteChartIsBasisLabelChart
    N.canonicalNative369FineCarrierBoundary ≡ true
finiteChartIsBasisLabels = refl

finiteChartIsNotWholeVOAStateBijection :
  N.Native369FineCarrierBoundary.native369FiniteChartIsWholeVOAStateBijection
    N.canonicalNative369FineCarrierBoundary ≡ false
finiteChartIsNotWholeVOAStateBijection = refl

physicalStateAssignmentStillOpen :
  N.Native369FineCarrierBoundary.physicalNH3StateToNative369FineCoordinatePaid
    N.canonicalNative369FineCarrierBoundary ≡ false
physicalStateAssignmentStillOpen = refl

physicalMonsterActionStillOpen :
  N.Native369FineCarrierBoundary.native369CarrierChartCreatesPhysicalMonsterAction
    N.canonicalNative369FineCarrierBoundary ≡ false
physicalMonsterActionStillOpen = refl
