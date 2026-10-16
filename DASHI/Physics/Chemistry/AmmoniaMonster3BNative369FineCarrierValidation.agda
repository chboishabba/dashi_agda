module DASHI.Physics.Chemistry.AmmoniaMonster3BNative369FineCarrierValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaMonster3BNative369FineCarrierExact as N

nativeRoundTrip :
  (n : N.Native369ZetaCoordinate) → N.modelToNative369 (N.native369ToModel n) ≡ n
nativeRoundTrip = N.native369RoundTrip

modelRoundTrip :
  (m : N.MonsterZetaModelBasis) → N.native369ToModel (N.modelToNative369 m) ≡ m
modelRoundTrip = N.model369RoundTrip

nativeCarrierPaid :
  N.Native369FineCarrierBoundary.fullMonsterZetaModelHasNative369CarrierChart
    N.canonicalNative369FineCarrierBoundary ≡ true
nativeCarrierPaid = refl

physicalStateAssignmentStillOpen :
  N.Native369FineCarrierBoundary.physicalNH3StateToNative369FineCoordinatePaid
    N.canonicalNative369FineCarrierBoundary ≡ false
physicalStateAssignmentStillOpen = refl
