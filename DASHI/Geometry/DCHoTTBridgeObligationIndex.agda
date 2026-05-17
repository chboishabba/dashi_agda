module DASHI.Geometry.DCHoTTBridgeObligationIndex where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (ℕ; suc; _≤_)

------------------------------------------------------------------------
-- DCHoTT B0 bridge obligation index.
--
-- This module is a Paper 2 scaffold only.  It records the bridge sockets
-- that must be discharged before a B0 claim can be promoted.  It deliberately
-- does not import DCHoTT-Agda, does not construct a torsion-free G-structure,
-- and does not prove B0.

record ProObjectCarrier : Set₁ where
  field
    -- The finite refinement tower X_d.
    depthCarrier :
      ℕ →
      Set

    -- Compatible refinement maps phi_{d+1,d} : X_{d+1} -> X_d.
    refinementMap :
      (d : ℕ) →
      depthCarrier (suc d) →
      depthCarrier d

    -- Lightweight depth-indexed bound for transport-defect decay.
    -- This intentionally uses the repo's constructive Nat-valued bound
    -- convention instead of importing a real-analysis dependency here.
    waveCoherenceBound :
      ℕ →
      ℕ

    waveCoherenceDecay :
      (d : ℕ) →
      waveCoherenceBound (suc d)
      ≤
      waveCoherenceBound d

    -- The inverse-limit/pro-object target.  Constructing this from the
    -- tower is B0.1's obligation; this index only names the socket.
    proObjectLimit :
      Set

open ProObjectCarrier public

data DCHoTTB0BridgeStatus : Set where
  indexedObligationsOnlyNoB0Proof :
    DCHoTTB0BridgeStatus

data DCHoTTB0BridgeObligation : Set where
  carrierToDSpace :
    DCHoTTB0BridgeObligation

  waveCoherentToFlat :
    DCHoTTB0BridgeObligation

  refinementToGStr :
    DCHoTTB0BridgeObligation

  gStrToLeviCivita :
    DCHoTTB0BridgeObligation

canonicalDCHoTTB0BridgeObligations :
  List DCHoTTB0BridgeObligation
canonicalDCHoTTB0BridgeObligations =
  carrierToDSpace
  ∷ waveCoherentToFlat
  ∷ refinementToGStr
  ∷ gStrToLeviCivita
  ∷ []

data DCHoTTB0BridgeBlocker : Set where
  missingCarrierToDSpace :
    DCHoTTB0BridgeBlocker

  missingWaveCoherentToFlat :
    DCHoTTB0BridgeBlocker

  missingRefinementToGStr :
    DCHoTTB0BridgeBlocker

  missingGStrToLeviCivita :
    DCHoTTB0BridgeBlocker

canonicalDCHoTTB0BridgeBlockers :
  List DCHoTTB0BridgeBlocker
canonicalDCHoTTB0BridgeBlockers =
  missingCarrierToDSpace
  ∷ missingWaveCoherentToFlat
  ∷ missingRefinementToGStr
  ∷ missingGStrToLeviCivita
  ∷ []

-- Constructorless: no value of this type is manufactured by this index.
data DCHoTTB0PromotionReceipt : Set where

dchottB0PromotionReceiptImpossibleHere :
  DCHoTTB0PromotionReceipt →
  Set
dchottB0PromotionReceiptImpossibleHere ()

record DCHoTTBridgeSocket : Set where
  field
    obligation :
      DCHoTTB0BridgeObligation

    sourceModule :
      String

    sourceName :
      String

    dashiTarget :
      String

    adapterObligation :
      String

open DCHoTTBridgeSocket public

canonicalCarrierToDSpaceSocket :
  DCHoTTBridgeSocket
canonicalCarrierToDSpaceSocket =
  record
    { obligation =
        carrierToDSpace
    ; sourceModule =
        "Formal-D-space"
    ; sourceName =
        "formal D -space"
    ; dashiTarget =
        "DASHI carrier -> DCHoTT formal D-space"
    ; adapterObligation =
        "construct ProObjectCarrier.proObjectLimit from the refinement tower and bind it to a DCHoTT formal D-space"
    }

canonicalWaveCoherentToFlatSocket :
  DCHoTTBridgeSocket
canonicalWaveCoherentToFlatSocket =
  record
    { obligation =
        waveCoherentToFlat
    ; sourceModule =
        "HomogeneousType / FormalDiskBundle"
    ; sourceName =
        "homogeneous-structure-on_; triviality-of-the-formal-disk-bundle-over-homogeneous-types"
    ; dashiTarget =
        "wave-coherent local model -> flat homogeneous formal-disk chart"
    ; adapterObligation =
        "bind DASHI wave coherence to a homogeneous model whose formal disks are identified with the base disk"
    }

canonicalRefinementToGStrSocket :
  DCHoTTBridgeSocket
canonicalRefinementToGStrSocket =
  record
    { obligation =
        refinementToGStr
    ; sourceModule =
        "G-structure"
    ; sourceName =
        "groups-over-automorphismgroup-of_; G-structures; G-str->"
    ; dashiTarget =
        "DASHI refinement/coarse-graining data -> G-structure lift"
    ; adapterObligation =
        "construct the BG/Bi lift of the formal disk classifying map and prove compatibility under refinement maps"
    }

canonicalGStrToLeviCivitaSocket :
  DCHoTTBridgeSocket
canonicalGStrToLeviCivitaSocket =
  record
    { obligation =
        gStrToLeviCivita
    ; sourceModule =
        "G-structure"
    ; sourceName =
        "no exported torsion-free G-structure or Levi-Civita identifier in local clone"
    ; dashiTarget =
        "G-structure lift -> DASHI Levi-Civita adapter"
    ; adapterObligation =
        "define the missing torsion-free/metric-compatible specialization before any Levi-Civita or B0 promotion"
    }

canonicalDCHoTTBridgeSockets :
  List DCHoTTBridgeSocket
canonicalDCHoTTBridgeSockets =
  canonicalCarrierToDSpaceSocket
  ∷ canonicalWaveCoherentToFlatSocket
  ∷ canonicalRefinementToGStrSocket
  ∷ canonicalGStrToLeviCivitaSocket
  ∷ []

record DCHoTTBridgeObligationIndex : Setω where
  field
    status :
      DCHoTTB0BridgeStatus

    localDependencyPath :
      String

    flatModuleLayout :
      Bool

    flatModuleLayoutIsTrue :
      flatModuleLayout ≡ true

    hasAgdaLib :
      Bool

    hasAgdaLibIsFalse :
      hasAgdaLib ≡ false

    obligations :
      List DCHoTTB0BridgeObligation

    obligationsAreCanonical :
      obligations
      ≡
      canonicalDCHoTTB0BridgeObligations

    sockets :
      List DCHoTTBridgeSocket

    socketsAreCanonical :
      sockets
      ≡
      canonicalDCHoTTBridgeSockets

    blockers :
      List DCHoTTB0BridgeBlocker

    blockersAreCanonical :
      blockers
      ≡
      canonicalDCHoTTB0BridgeBlockers

    firstOpenBlocker :
      DCHoTTB0BridgeBlocker

    firstOpenBlockerIsCarrierToDSpace :
      firstOpenBlocker
      ≡
      missingCarrierToDSpace

    b0ProvedHere :
      Bool

    b0ProvedHereIsFalse :
      b0ProvedHere ≡ false

    noPromotionAuthority :
      Bool

    noPromotionAuthorityIsTrue :
      noPromotionAuthority ≡ true

    futurePromotionReceiptBlocked :
      DCHoTTB0PromotionReceipt →
      Set

    governanceBoundary :
      List String

open DCHoTTBridgeObligationIndex public

canonicalDCHoTTBridgeObligationIndex :
  DCHoTTBridgeObligationIndex
canonicalDCHoTTBridgeObligationIndex =
  record
    { status =
        indexedObligationsOnlyNoB0Proof
    ; localDependencyPath =
        "DCHoTT-Agda"
    ; flatModuleLayout =
        true
    ; flatModuleLayoutIsTrue =
        refl
    ; hasAgdaLib =
        false
    ; hasAgdaLibIsFalse =
        refl
    ; obligations =
        canonicalDCHoTTB0BridgeObligations
    ; obligationsAreCanonical =
        refl
    ; sockets =
        canonicalDCHoTTBridgeSockets
    ; socketsAreCanonical =
        refl
    ; blockers =
        canonicalDCHoTTB0BridgeBlockers
    ; blockersAreCanonical =
        refl
    ; firstOpenBlocker =
        missingCarrierToDSpace
    ; firstOpenBlockerIsCarrierToDSpace =
        refl
    ; b0ProvedHere =
        false
    ; b0ProvedHereIsFalse =
        refl
    ; noPromotionAuthority =
        true
    ; noPromotionAuthorityIsTrue =
        refl
    ; futurePromotionReceiptBlocked =
        dchottB0PromotionReceiptImpossibleHere
    ; governanceBoundary =
        "B0 remains open: this index names sub-obligations only"
        ∷ "ProObjectCarrier records the inverse-limit target for Paper 2; it is not constructed here"
        ∷ "carrierToDSpace must bind DASHI carriers to DCHoTT formal D-spaces"
        ∷ "waveCoherentToFlat must connect DASHI wave coherence to homogeneous formal-disk triviality"
        ∷ "refinementToGStr must construct a G-structure lift compatible with refinement"
        ∷ "gStrToLeviCivita is blocked on a missing torsion-free/metric-compatible DCHoTT specialization"
        ∷ "no DCHoTTB0PromotionReceipt is constructed or promoted here"
        ∷ []
    }
