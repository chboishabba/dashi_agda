module DASHI.Moonshine.OggSSPSmallCharacteristicCrossAmbientTransportPaymentExact where

------------------------------------------------------------------------
-- CROSS-AMBIENT TRANSPORT PAYMENT FOR THE 10/2 WILD-LAYER CANDIDATE
--
-- The arithmetic product identities
--
--   p=2 : 2 wild layers x 5 full-stack unoriented inertia sectors = 10
--   p=3 : 1 wild layer  x 2 X0(3) local-incidence orbit sectors   =  2
--
-- are exact, but the factors do not initially live on the same moduli object.
--
-- Required p=2 transport:
--   X(1)^rig wild-root analytic object
--     -> full X(1) central-gerbe refinement,
--   distinguishing the two pairs collapsed by 2T -> A4 rigidification.
--
-- Required p=3 transport:
--   X(1)^rig wild-root analytic object
--     -> bad-level X0(3) supersingular neighbourhood,
--   distinguishing node from Frobenius/Verschiebung branch-pair.
--
-- Only after BOTH transports are paid is the layer x sector multiplicity rule
-- geometrically well-typed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPP2BinaryTetrahedralRigidificationQuotientExact as P2Transport
import DASHI.Moonshine.OggSSPP3DeligneRapoportDegeneracyTransportCutsetExact as P3Transport
import DASHI.Moonshine.OggSSPSmallCharacteristicWildLayerSectorProductCandidateExact as LayerSector
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Joint transport payment.
------------------------------------------------------------------------

record CrossAmbientTransportAuthority : Set₁ where
  field
    p2FullInertiaLift :
      P2Transport.FullInertiaLiftTransportAuthority

    p3BadLevelBranchLift :
      P3Transport.P3BadLevelBranchTransportAuthority

    p2TransportPreservesFiveSectorResolution :
      Bool
    p2TransportPreservesFiveSectorResolutionIsTrue :
      p2TransportPreservesFiveSectorResolution ≡ true

    p3TransportPreservesTwoOrbitResolution :
      Bool
    p3TransportPreservesTwoOrbitResolutionIsTrue :
      p3TransportPreservesTwoOrbitResolution ≡ true

    bothTransportsLiveOverSameWildBaseGeometry :
      Bool
    bothTransportsLiveOverSameWildBaseGeometryIsTrue :
      bothTransportsLiveOverSameWildBaseGeometry ≡ true

    transportIndependentOfMonsterGap :
      Bool
    transportIndependentOfMonsterGapIsTrue :
      transportIndependentOfMonsterGap ≡ true

open CrossAmbientTransportAuthority public

------------------------------------------------------------------------
-- 2. Valuation authority after transport.
------------------------------------------------------------------------

record TransportedWildLayerSectorValuationAuthority : Set₁ where
  field
    transport :
      CrossAmbientTransportAuthority

    transportedLayerSectorAuthority :
      LayerSector.WildLayerSectorValuationAuthority

    valuationTermsUseTransportedP2Refinements :
      Bool
    valuationTermsUseTransportedP2RefinementsIsTrue :
      valuationTermsUseTransportedP2Refinements ≡ true

    valuationTermsUseTransportedP3BranchData :
      Bool
    valuationTermsUseTransportedP3BranchDataIsTrue :
      valuationTermsUseTransportedP3BranchData ≡ true

    sameAnalyticConstructionBeforeReadingMonsterTarget :
      Bool
    sameAnalyticConstructionBeforeReadingMonsterTargetIsTrue :
      sameAnalyticConstructionBeforeReadingMonsterTarget ≡ true

open TransportedWildLayerSectorValuationAuthority public

------------------------------------------------------------------------
-- 3. Existing candidate alone cannot inhabit the transported theorem.
------------------------------------------------------------------------

data ArithmeticProductCreatesTransportAuthority : Set where
data RigidifiedLayerCountCreatesFullStackLift : Set where
data BaseRootStackCreatesX03BranchLift : Set where
data ExistingLayerSectorAuthorityCanIgnoreAmbientMismatch : Set where

arithmeticProductDoesNotCreateTransport :
  ArithmeticProductCreatesTransportAuthority -> ⊥
arithmeticProductDoesNotCreateTransport ()

rigidifiedLayerCountDoesNotCreateFullStackLift :
  RigidifiedLayerCountCreatesFullStackLift -> ⊥
rigidifiedLayerCountDoesNotCreateFullStackLift ()

baseRootStackDoesNotCreateX03BranchLift :
  BaseRootStackCreatesX03BranchLift -> ⊥
baseRootStackDoesNotCreateX03BranchLift ()

layerSectorAuthorityCannotIgnoreAmbientMismatch :
  ExistingLayerSectorAuthorityCanIgnoreAmbientMismatch -> ⊥
layerSectorAuthorityCannotIgnoreAmbientMismatch ()

------------------------------------------------------------------------
-- 4. Live status.
------------------------------------------------------------------------

data CrossAmbientTransportAuthorityInhabited : Set where
data TransportedWildLayerSectorValuationAuthorityInhabited : Set where

crossAmbientTransportStillOpen :
  CrossAmbientTransportAuthorityInhabited -> ⊥
crossAmbientTransportStillOpen ()

transportedValuationAuthorityStillOpen :
  TransportedWildLayerSectorValuationAuthorityInhabited -> ⊥
transportedValuationAuthorityStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record CrossAmbientTransportPaymentBoundary : Set where
  constructor cross-ambient-transport-payment-boundary
  field
    p2AmbientMismatchExposed : Bool
    p3AmbientMismatchExposed : Bool
    p2FiveToThreeRigidificationCollapseProved : Bool
    p3ThreeStrataToOneBasePointCollapseProved : Bool
    jointTransportAuthoritySpecified : Bool
    transportedValuationAuthoritySpecified : Bool
    crossAmbientTransportInhabited : Bool
    transportedLayerSectorValuationInhabited : Bool
    rawTenTwoProductPromotedWithoutTransport : Bool

canonicalCrossAmbientTransportPaymentBoundary :
  CrossAmbientTransportPaymentBoundary
canonicalCrossAmbientTransportPaymentBoundary =
  cross-ambient-transport-payment-boundary
    true true true true true true false false false
