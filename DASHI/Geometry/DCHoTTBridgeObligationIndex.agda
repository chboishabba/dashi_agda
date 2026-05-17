module DASHI.Geometry.DCHoTTBridgeObligationIndex where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (ℕ; zero; suc; _≤_)

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

-- B0.1 starts with the ordinary inverse-limit surface: a point of the
-- pro-object is a compatible family through all finite refinement depths.
-- This is still DASHI-side structure only; it does not construct a DCHoTT
-- formal D-space, manifold, G-structure, or Levi-Civita receipt.
record ProCompatibleFamily (P : ProObjectCarrier) : Set₁ where
  field
    familyAtDepth :
      (d : ℕ) →
      ProObjectCarrier.depthCarrier P d

    familyCompatible :
      (d : ℕ) →
      ProObjectCarrier.refinementMap P d (familyAtDepth (suc d))
      ≡
      familyAtDepth d

open ProCompatibleFamily public

-- User-facing B0.1 point form.  This is definitionally the same
-- compatible-family idea, but with names matching the pro-object theorem:
-- point d : X_d and coherence d : phi_d(point (suc d)) = point d.
record ProObjectPoint (P : ProObjectCarrier) : Set₁ where
  field
    point :
      (d : ℕ) →
      ProObjectCarrier.depthCarrier P d

    coherence :
      (d : ℕ) →
      ProObjectCarrier.refinementMap P d (point (suc d))
      ≡
      point d

open ProObjectPoint public

proObjectPointAsCompatibleFamily :
  {P : ProObjectCarrier} →
  ProObjectPoint P →
  ProCompatibleFamily P
proObjectPointAsCompatibleFamily x =
  record
    { familyAtDepth =
        ProObjectPoint.point x
    ; familyCompatible =
        ProObjectPoint.coherence x
    }

compatibleFamilyAsProObjectPoint :
  {P : ProObjectCarrier} →
  ProCompatibleFamily P →
  ProObjectPoint P
compatibleFamilyAsProObjectPoint x =
  record
    { point =
        ProCompatibleFamily.familyAtDepth x
    ; coherence =
        ProCompatibleFamily.familyCompatible x
    }

-- B0.1 formal-disk structure induced by the coarsest refinement projection.
-- In this scaffold, Im is the depth-zero projection, formal closeness is
-- equality after that projection, and the disk at x is the Sigma type of
-- formally close pro-object points.
Im :
  {P : ProObjectCarrier} →
  ProObjectPoint P →
  ProObjectCarrier.depthCarrier P zero
Im x =
  ProObjectPoint.point x zero

FormallyClose :
  {P : ProObjectCarrier} →
  ProObjectPoint P →
  ProObjectPoint P →
  Set
FormallyClose x y =
  Im x ≡ Im y

FormalDisk :
  {P : ProObjectCarrier} →
  ProObjectPoint P →
  Set₁
FormalDisk {P} x =
  Σ (ProObjectPoint P) (FormallyClose x)

record ProLimitProjectionSurface (P : ProObjectCarrier) : Set₁ where
  field
    limitProjection :
      (d : ℕ) →
      ProObjectCarrier.proObjectLimit P →
      ProObjectCarrier.depthCarrier P d

    limitProjectionCompatible :
      (d : ℕ) →
      (x : ProObjectCarrier.proObjectLimit P) →
      ProObjectCarrier.refinementMap P d (limitProjection (suc d) x)
      ≡
      limitProjection d x

open ProLimitProjectionSurface public

limitAsCompatibleFamily :
  {P : ProObjectCarrier} →
  ProLimitProjectionSurface P →
  ProObjectCarrier.proObjectLimit P →
  ProCompatibleFamily P
limitAsCompatibleFamily surface x =
  record
    { familyAtDepth =
        λ d →
          ProLimitProjectionSurface.limitProjection surface d x
    ; familyCompatible =
        λ d →
          ProLimitProjectionSurface.limitProjectionCompatible surface d x
    }

limitAsProObjectPoint :
  {P : ProObjectCarrier} →
  ProLimitProjectionSurface P →
  ProObjectCarrier.proObjectLimit P →
  ProObjectPoint P
limitAsProObjectPoint surface x =
  compatibleFamilyAsProObjectPoint
    (limitAsCompatibleFamily surface x)

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

  missingLimitProjectionCompatibility :
    DCHoTTB0BridgeBlocker

  missingWaveCoherentToFlat :
    DCHoTTB0BridgeBlocker

  missingFlatFormalDiskTrivialization :
    DCHoTTB0BridgeBlocker

  missingRefinementToGStr :
    DCHoTTB0BridgeBlocker

  missingGStrToLeviCivita :
    DCHoTTB0BridgeBlocker

canonicalDCHoTTB0BridgeBlockers :
  List DCHoTTB0BridgeBlocker
canonicalDCHoTTB0BridgeBlockers =
  missingCarrierToDSpace
  ∷ missingLimitProjectionCompatibility
  ∷ missingWaveCoherentToFlat
  ∷ missingFlatFormalDiskTrivialization
  ∷ missingRefinementToGStr
  ∷ missingGStrToLeviCivita
  ∷ []

data FlatFormalDiskOpenObligation : Set where
  missingTransportDefectNorm :
    FlatFormalDiskOpenObligation

  missingSummableWaveCoherenceDecay :
    FlatFormalDiskOpenObligation

  missingLimitParallelTransport :
    FlatFormalDiskOpenObligation

  missingDCHoTTFormalDiskTrivialization :
    FlatFormalDiskOpenObligation

canonicalFlatFormalDiskOpenObligations :
  List FlatFormalDiskOpenObligation
canonicalFlatFormalDiskOpenObligations =
  missingTransportDefectNorm
  ∷ missingSummableWaveCoherenceDecay
  ∷ missingLimitParallelTransport
  ∷ missingDCHoTTFormalDiskTrivialization
  ∷ []

record WaveCoherentFlatFormalDiskSurface (P : ProObjectCarrier) : Setω where
  field
    projectionSurface :
      ProLimitProjectionSurface P

    formalDiskAt :
      ProObjectPoint P →
      Set₁

    formalDiskAtIsDepthZeroDisk :
      (x : ProObjectPoint P) →
      formalDiskAt x
      ≡
      FormalDisk x

    curvatureDecayBound :
      ℕ →
      ℕ

    curvatureDecayBoundIsCarrierBound :
      curvatureDecayBound
      ≡
      ProObjectCarrier.waveCoherenceBound P

    flatInLimitClaim :
      String

    flatInLimitClaim-v :
      flatInLimitClaim
      ≡
      "target-only-wave-coherence-decay-should-trivialize-formal-disk-transport-in-the-limit"

    openFlatnessObligations :
      List FlatFormalDiskOpenObligation

    openFlatnessObligationsAreCanonical :
      openFlatnessObligations
      ≡
      canonicalFlatFormalDiskOpenObligations

open WaveCoherentFlatFormalDiskSurface public

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
        "groups-over-automorphismgroup-of_; G-structures; G-str→"
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
        ∷ "ProObjectPoint is the compatible-family type (x_d) with refinement coherence"
        ∷ "Im, FormallyClose, and FormalDisk record the depth-zero formal-disk scaffold for B0.1"
        ∷ "ProCompatibleFamily and ProLimitProjectionSurface record only the DASHI-side compatible-family cone"
        ∷ "limit projection compatibility does not imply a DCHoTT formal D-space, manifold, G-structure, or Levi-Civita adapter"
        ∷ "WaveCoherentFlatFormalDiskSurface records the B0.2 flat-in-the-limit target without proving DCHoTT disk-bundle triviality"
        ∷ "carrierToDSpace must bind DASHI carriers to DCHoTT formal D-spaces"
        ∷ "waveCoherentToFlat must connect DASHI wave coherence to homogeneous formal-disk triviality"
        ∷ "refinementToGStr must construct a G-structure lift compatible with refinement"
        ∷ "gStrToLeviCivita is blocked on a missing torsion-free/metric-compatible DCHoTT specialization"
        ∷ "no DCHoTTB0PromotionReceipt is constructed or promoted here"
        ∷ []
    }
