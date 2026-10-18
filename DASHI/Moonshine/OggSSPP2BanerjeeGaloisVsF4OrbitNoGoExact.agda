module DASHI.Moonshine.OggSSPP2BanerjeeGaloisVsF4OrbitNoGoExact where

------------------------------------------------------------------------
-- BANERJEE GAL(F4/F2) SHEET != RAW F4 FROBENIUS-ORBIT ACTION
--
-- The source-native Banerjee Galois involution toggles the binary Galois
-- sheet.  Under the current ten-state rechart this swaps the two centre
-- states, hence swaps the raw coarse strata zero-fixed and one-fixed.
--
-- On all four noncentral inertia sectors both sheets lie over the conjugate
-- raw F4 orbit, so the coarse orbit is preserved there.
--
-- Therefore the Banerjee Galois involution cannot directly inhabit any source
-- interface that requires the CURRENT raw-F4 orbit classifier to be globally
-- invariant.  The mismatch is exactly centre-local.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSPP2BanerjeeF4UniversalDeformationSourceExact as Banerjee
import DASHI.Moonshine.OggSSPP2F4FrobeniusCandidateNoGoExact as F4
import DASHI.Moonshine.OggSSPP2F4AntipodalStratifiedRefinementExact as Target
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Inertia
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

galoisInvolution :
  Banerjee.GaloisInertiaState ->
  Banerjee.GaloisInertiaState
galoisInvolution
  (Banerjee.identityGaloisSheet , inertia) =
  Banerjee.frobeniusGaloisSheet , inertia
galoisInvolution
  (Banerjee.frobeniusGaloisSheet , inertia) =
  Banerjee.identityGaloisSheet , inertia

galoisInvolutionInvolutive :
  (state : Banerjee.GaloisInertiaState) ->
  galoisInvolution (galoisInvolution state) ≡ state
galoisInvolutionInvolutive
  (Banerjee.identityGaloisSheet , inertia) = refl
galoisInvolutionInvolutive
  (Banerjee.frobeniusGaloisSheet , inertia) = refl

coarseOrbit :
  Banerjee.GaloisInertiaState ->
  F4.F4FrobeniusOrbit
coarseOrbit state =
  Target.stratumOf (Banerjee.toTarget state)

identityCentreOrbit :
  coarseOrbit
    (Banerjee.identityGaloisSheet , Inertia.identityInertiaOrbit)
  ≡ F4.zeroFixedOrbit
identityCentreOrbit = refl

frobeniusCentreOrbit :
  coarseOrbit
    (Banerjee.frobeniusGaloisSheet , Inertia.identityInertiaOrbit)
  ≡ F4.oneFixedOrbit
frobeniusCentreOrbit = refl

centreOrbitChangesUnderGalois :
  coarseOrbit
    (galoisInvolution
      (Banerjee.identityGaloisSheet , Inertia.identityInertiaOrbit))
  ≡
  coarseOrbit
    (Banerjee.identityGaloisSheet , Inertia.identityInertiaOrbit)
  ->
  ⊥
centreOrbitChangesUnderGalois ()

noncentralCentralMinusOneInvariant :
  (sheet : Banerjee.GaloisSheet) ->
  coarseOrbit
    (galoisInvolution (sheet , Inertia.centralMinusOneInertiaOrbit))
  ≡
  coarseOrbit
    (sheet , Inertia.centralMinusOneInertiaOrbit)
noncentralCentralMinusOneInvariant Banerjee.identityGaloisSheet = refl
noncentralCentralMinusOneInvariant Banerjee.frobeniusGaloisSheet = refl

noncentralOrderFourInvariant :
  (sheet : Banerjee.GaloisSheet) ->
  coarseOrbit
    (galoisInvolution (sheet , Inertia.orderFourInertiaOrbit))
  ≡
  coarseOrbit
    (sheet , Inertia.orderFourInertiaOrbit)
noncentralOrderFourInvariant Banerjee.identityGaloisSheet = refl
noncentralOrderFourInvariant Banerjee.frobeniusGaloisSheet = refl

noncentralOrderThreeInvariant :
  (sheet : Banerjee.GaloisSheet) ->
  coarseOrbit
    (galoisInvolution (sheet , Inertia.orderThreePairInertiaOrbit))
  ≡
  coarseOrbit
    (sheet , Inertia.orderThreePairInertiaOrbit)
noncentralOrderThreeInvariant Banerjee.identityGaloisSheet = refl
noncentralOrderThreeInvariant Banerjee.frobeniusGaloisSheet = refl

noncentralOrderSixInvariant :
  (sheet : Banerjee.GaloisSheet) ->
  coarseOrbit
    (galoisInvolution (sheet , Inertia.orderSixPairInertiaOrbit))
  ≡
  coarseOrbit
    (sheet , Inertia.orderSixPairInertiaOrbit)
noncentralOrderSixInvariant Banerjee.identityGaloisSheet = refl
noncentralOrderSixInvariant Banerjee.frobeniusGaloisSheet = refl

record GloballyInvariantCoarseOrbit : Set where
  field
    invariant :
      (state : Banerjee.GaloisInertiaState) ->
      coarseOrbit (galoisInvolution state)
      ≡ coarseOrbit state

open GloballyInvariantCoarseOrbit public

naturalGaloisCannotPreserveCurrentCoarseOrbit :
  GloballyInvariantCoarseOrbit ->
  ⊥
naturalGaloisCannotPreserveCurrentCoarseOrbit global =
  centreOrbitChangesUnderGalois
    (invariant global
      (Banerjee.identityGaloisSheet , Inertia.identityInertiaOrbit))

data GaloisActionIsRawF4FrobeniusAction : Set where

galoisActionDoesNotBecomeRawF4FrobeniusAction :
  GaloisActionIsRawF4FrobeniusAction -> ⊥
galoisActionDoesNotBecomeRawF4FrobeniusAction ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record BanerjeeGaloisVsF4OrbitNoGoBoundary : Set where
  constructor banerjee-galois-vs-f4-orbit-no-go-boundary
  field
    naturalGaloisInvolutionOwned : Bool
    involutivityPaid : Bool
    centreCoarseOrbitChanges : Bool
    fourNoncentralSectorsPreserveCoarseOrbit : Bool
    globalCurrentF4OrbitInvariancePossible : Bool
    mismatchLocalizedToDuplicatedCentre : Bool
    galoisActionIdentifiedWithRawF4Frobenius : Bool

canonicalBanerjeeGaloisVsF4OrbitNoGoBoundary :
  BanerjeeGaloisVsF4OrbitNoGoBoundary
canonicalBanerjeeGaloisVsF4OrbitNoGoBoundary =
  banerjee-galois-vs-f4-orbit-no-go-boundary
    true true true true false true false
