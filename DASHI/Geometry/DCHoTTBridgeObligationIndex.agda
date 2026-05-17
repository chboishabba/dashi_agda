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

b0-sym :
  {A : Set} →
  {x y : A} →
  x ≡ y →
  y ≡ x
b0-sym refl =
  refl

b0-trans :
  {A : Set} →
  {x y z : A} →
  x ≡ y →
  y ≡ z →
  x ≡ z
b0-trans refl refl =
  refl

b0-cong :
  {A B : Set} →
  {x y : A} →
  (f : A → B) →
  x ≡ y →
  f x ≡ f y
b0-cong _ refl =
  refl

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

proObjectPointCompatibleFamily-to-from :
  {P : ProObjectCarrier} →
  (x : ProObjectPoint P) →
  compatibleFamilyAsProObjectPoint
    (proObjectPointAsCompatibleFamily x)
  ≡
  x
proObjectPointCompatibleFamily-to-from _ =
  refl

proObjectPointCompatibleFamily-from-to :
  {P : ProObjectCarrier} →
  (x : ProCompatibleFamily P) →
  proObjectPointAsCompatibleFamily
    (compatibleFamilyAsProObjectPoint x)
  ≡
  x
proObjectPointCompatibleFamily-from-to _ =
  refl

record B01CompatibleFamilyRoundtripSurface
  (P : ProObjectCarrier) :
  Setω where
  field
    PointSurface :
      Set₁

    PointSurface-v :
      PointSurface
      ≡
      ProObjectPoint P

    CompatibleFamilySurface :
      Set₁

    CompatibleFamilySurface-v :
      CompatibleFamilySurface
      ≡
      ProCompatibleFamily P

    pointToFamily :
      PointSurface →
      CompatibleFamilySurface

    familyToPoint :
      CompatibleFamilySurface →
      PointSurface

    pointRoundtrip :
      (x : PointSurface) →
      familyToPoint (pointToFamily x)
      ≡
      x

    familyRoundtrip :
      (x : CompatibleFamilySurface) →
      pointToFamily (familyToPoint x)
      ≡
      x

open B01CompatibleFamilyRoundtripSurface public

canonicalB01CompatibleFamilyRoundtripSurface :
  (P : ProObjectCarrier) →
  B01CompatibleFamilyRoundtripSurface P
canonicalB01CompatibleFamilyRoundtripSurface P =
  record
    { PointSurface =
        ProObjectPoint P
    ; PointSurface-v =
        refl
    ; CompatibleFamilySurface =
        ProCompatibleFamily P
    ; CompatibleFamilySurface-v =
        refl
    ; pointToFamily =
        proObjectPointAsCompatibleFamily
    ; familyToPoint =
        compatibleFamilyAsProObjectPoint
    ; pointRoundtrip =
        proObjectPointCompatibleFamily-to-from
    ; familyRoundtrip =
        proObjectPointCompatibleFamily-from-to
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

ImFibreAt :
  {P : ProObjectCarrier} →
  ProObjectCarrier.depthCarrier P zero →
  Set₁
ImFibreAt {P} x0 =
  Σ (ProObjectPoint P) (λ y → x0 ≡ Im y)

formalDiskAsImFibre :
  {P : ProObjectCarrier} →
  (x : ProObjectPoint P) →
  FormalDisk x →
  ImFibreAt {P = P} (Im {P = P} x)
formalDiskAsImFibre {P = P} _ disk =
  disk

imFibreAsFormalDisk :
  {P : ProObjectCarrier} →
  (x : ProObjectPoint P) →
  ImFibreAt {P = P} (Im {P = P} x) →
  FormalDisk x
imFibreAsFormalDisk {P = P} _ fibre =
  fibre

ImQuotientEquality :
  {P : ProObjectCarrier} →
  ProObjectPoint P →
  ProObjectPoint P →
  Set
ImQuotientEquality =
  FormallyClose

DepthZeroAgreement :
  {P : ProObjectCarrier} →
  ProObjectPoint P →
  ProObjectPoint P →
  Set
DepthZeroAgreement x y =
  ProObjectPoint.point x zero
  ≡
  ProObjectPoint.point y zero

DepthOneAgreement :
  {P : ProObjectCarrier} →
  ProObjectPoint P →
  ProObjectPoint P →
  Set
DepthOneAgreement x y =
  ProObjectPoint.point x (suc zero)
  ≡
  ProObjectPoint.point y (suc zero)

ImModalEquality :
  {P : ProObjectCarrier} →
  ProObjectPoint P →
  ProObjectPoint P →
  Set
ImModalEquality =
  ImQuotientEquality

depthZeroAgreementToImModalEquality :
  {P : ProObjectCarrier} →
  (x y : ProObjectPoint P) →
  DepthZeroAgreement x y →
  ImModalEquality x y
depthZeroAgreementToImModalEquality _ _ xy =
  xy

depthOneAgreementToDepthZeroAgreement :
  {P : ProObjectCarrier} →
  (x y : ProObjectPoint P) →
  DepthOneAgreement x y →
  DepthZeroAgreement x y
depthOneAgreementToDepthZeroAgreement {P = P} x y xy =
  b0-trans
    (b0-sym (ProObjectPoint.coherence x zero))
    (b0-trans
      (b0-cong (ProObjectCarrier.refinementMap P zero) xy)
      (ProObjectPoint.coherence y zero))

depthOneAgreementToImModalEquality :
  {P : ProObjectCarrier} →
  (x y : ProObjectPoint P) →
  DepthOneAgreement x y →
  ImModalEquality x y
depthOneAgreementToImModalEquality x y xy =
  depthZeroAgreementToImModalEquality x y
    (depthOneAgreementToDepthZeroAgreement x y xy)

record Depth01AgreementImModalSurface
  (P : ProObjectCarrier) :
  Set₁ where
  field
    depthZeroAgreement :
      ProObjectPoint P →
      ProObjectPoint P →
      Set

    depthZeroAgreement-v :
      (x y : ProObjectPoint P) →
      depthZeroAgreement x y
      ≡
      DepthZeroAgreement x y

    depthOneAgreement :
      ProObjectPoint P →
      ProObjectPoint P →
      Set

    depthOneAgreement-v :
      (x y : ProObjectPoint P) →
      depthOneAgreement x y
      ≡
      DepthOneAgreement x y

    imModalEquality :
      ProObjectPoint P →
      ProObjectPoint P →
      Set

    imModalEquality-v :
      (x y : ProObjectPoint P) →
      imModalEquality x y
      ≡
      ImModalEquality x y

    depthZeroImpliesImModal :
      (x y : ProObjectPoint P) →
      depthZeroAgreement x y →
      imModalEquality x y

    depthOneImpliesImModal :
      (x y : ProObjectPoint P) →
      depthOneAgreement x y →
      imModalEquality x y

open Depth01AgreementImModalSurface public

canonicalDepth01AgreementImModalSurface :
  (P : ProObjectCarrier) →
  Depth01AgreementImModalSurface P
canonicalDepth01AgreementImModalSurface P =
  record
    { depthZeroAgreement =
        DepthZeroAgreement
    ; depthZeroAgreement-v =
        λ _ _ →
          refl
    ; depthOneAgreement =
        DepthOneAgreement
    ; depthOneAgreement-v =
        λ _ _ →
          refl
    ; imModalEquality =
        ImModalEquality
    ; imModalEquality-v =
        λ _ _ →
          refl
    ; depthZeroImpliesImModal =
        depthZeroAgreementToImModalEquality
    ; depthOneImpliesImModal =
        depthOneAgreementToImModalEquality
    }

record ReverseLiftData
  (P : ProObjectCarrier) :
  Set₁ where
  field
    liftPointAtIm :
      ProObjectCarrier.depthCarrier P zero →
      ProObjectPoint P

    liftPointAtImSection :
      (x0 : ProObjectCarrier.depthCarrier P zero) →
      x0
      ≡
      Im (liftPointAtIm x0)

open ReverseLiftData public

reverseLiftDataToImFibre :
  {P : ProObjectCarrier} →
  ReverseLiftData P →
  (x0 : ProObjectCarrier.depthCarrier P zero) →
  ImFibreAt {P = P} x0
reverseLiftDataToImFibre lift x0 =
  ReverseLiftData.liftPointAtIm lift x0
  ,
  ReverseLiftData.liftPointAtImSection lift x0

record B01ReverseLiftSurface
  (P : ProObjectCarrier) :
  Setω where
  field
    reverseLiftData :
      Set₁

    reverseLiftData-v :
      reverseLiftData
      ≡
      ReverseLiftData P

    reverseLiftAtIm :
      ReverseLiftData P →
      (x0 : ProObjectCarrier.depthCarrier P zero) →
      ImFibreAt {P = P} x0

    reverseLiftAtIm-v :
      (lift : ReverseLiftData P) →
      (x0 : ProObjectCarrier.depthCarrier P zero) →
      reverseLiftAtIm lift x0
      ≡
      reverseLiftDataToImFibre lift x0

open B01ReverseLiftSurface public

canonicalB01ReverseLiftSurface :
  (P : ProObjectCarrier) →
  B01ReverseLiftSurface P
canonicalB01ReverseLiftSurface P =
  record
    { reverseLiftData =
        ReverseLiftData P
    ; reverseLiftData-v =
        refl
    ; reverseLiftAtIm =
        reverseLiftDataToImFibre
    ; reverseLiftAtIm-v =
        λ _ _ →
          refl
    }

formalDiskImFibre-to-from :
  {P : ProObjectCarrier} →
  (x : ProObjectPoint P) →
  (disk : FormalDisk x) →
  imFibreAsFormalDisk x (formalDiskAsImFibre x disk)
  ≡
  disk
formalDiskImFibre-to-from _ _ =
  refl

formalDiskImFibre-from-to :
  {P : ProObjectCarrier} →
  (x : ProObjectPoint P) →
  (fibre : ImFibreAt {P = P} (Im {P = P} x)) →
  formalDiskAsImFibre x (imFibreAsFormalDisk x fibre)
  ≡
  fibre
formalDiskImFibre-from-to _ _ =
  refl

record B01FormalDiskImFibreRoundtripSurface
  {P : ProObjectCarrier}
  (x : ProObjectPoint P) :
  Setω where
  field
    formalDiskCarrier :
      Set₁

    formalDiskCarrier-v :
      formalDiskCarrier
      ≡
      FormalDisk x

    imFibreCarrier :
      Set₁

    imFibreCarrier-v :
      imFibreCarrier
      ≡
      ImFibreAt {P = P} (Im {P = P} x)

    toImFibre :
      formalDiskCarrier →
      imFibreCarrier

    fromImFibre :
      imFibreCarrier →
      formalDiskCarrier

    toFromRoundtrip :
      (disk : formalDiskCarrier) →
      fromImFibre (toImFibre disk)
      ≡
      disk

    fromToRoundtrip :
      (fibre : imFibreCarrier) →
      toImFibre (fromImFibre fibre)
      ≡
      fibre

open B01FormalDiskImFibreRoundtripSurface public

canonicalB01FormalDiskImFibreRoundtripSurface :
  {P : ProObjectCarrier} →
  (x : ProObjectPoint P) →
  B01FormalDiskImFibreRoundtripSurface x
canonicalB01FormalDiskImFibreRoundtripSurface {P = P} x =
  record
    { formalDiskCarrier =
        FormalDisk x
    ; formalDiskCarrier-v =
        refl
    ; imFibreCarrier =
        ImFibreAt {P = P} (Im {P = P} x)
    ; imFibreCarrier-v =
        refl
    ; toImFibre =
        formalDiskAsImFibre x
    ; fromImFibre =
        imFibreAsFormalDisk x
    ; toFromRoundtrip =
        formalDiskImFibre-to-from x
    ; fromToRoundtrip =
        formalDiskImFibre-from-to x
    }

record B01ImFormalDiskSocket (P : ProObjectCarrier) : Setω where
  field
    imCarrier :
      Set

    imCarrierIsDepthZero :
      imCarrier
      ≡
      ProObjectCarrier.depthCarrier P zero

    formalDiskAt :
      ProObjectPoint P →
      Set₁

    formalDiskAtIsDepthZeroFibre :
      (x : ProObjectPoint P) →
      formalDiskAt x
      ≡
      ImFibreAt {P = P} (Im {P = P} x)

    quotientEquality :
      ProObjectPoint P →
      ProObjectPoint P →
      Set

    quotientEqualityIsImEquality :
      (x y : ProObjectPoint P) →
      quotientEquality x y
      ≡
      ImQuotientEquality {P = P} x y

    depth01AgreementImModalSurface :
      Depth01AgreementImModalSurface P

    reverseLiftAtIm :
      ProObjectCarrier.depthCarrier P zero →
      Set₁

    reverseLiftAtImIsFibre :
      (x0 : ProObjectCarrier.depthCarrier P zero) →
      reverseLiftAtIm x0
      ≡
      ImFibreAt {P = P} x0

    reverseLiftSurface :
      B01ReverseLiftSurface P

    formalDiskImFibreRoundtrip :
      (x : ProObjectPoint P) →
      B01FormalDiskImFibreRoundtripSurface x

    reverseLiftConstructedForAllImPoints :
      Bool

    reverseLiftConstructedForAllImPointsIsFalse :
      reverseLiftConstructedForAllImPoints ≡ false

    imModalQuotientEqualitySocket :
      String

    imModalQuotientEqualitySocket-v :
      imModalQuotientEqualitySocket
      ≡
      "DASHI-side-depth-zero-and-depth-one-agreement-imply-Im-modal-equality; imported-DCHoTT-modal-reflection-remains-open"

open B01ImFormalDiskSocket public

canonicalB01ImFormalDiskSocket :
  (P : ProObjectCarrier) →
  B01ImFormalDiskSocket P
canonicalB01ImFormalDiskSocket P =
  record
    { imCarrier =
        ProObjectCarrier.depthCarrier P zero
    ; imCarrierIsDepthZero =
        refl
    ; formalDiskAt =
        λ x →
          ImFibreAt {P = P} (Im {P = P} x)
    ; formalDiskAtIsDepthZeroFibre =
        λ _ →
          refl
    ; quotientEquality =
        ImQuotientEquality {P = P}
    ; quotientEqualityIsImEquality =
        λ _ _ →
          refl
    ; depth01AgreementImModalSurface =
        canonicalDepth01AgreementImModalSurface P
    ; reverseLiftAtIm =
        ImFibreAt {P = P}
    ; reverseLiftAtImIsFibre =
        λ _ →
          refl
    ; reverseLiftSurface =
        canonicalB01ReverseLiftSurface P
    ; formalDiskImFibreRoundtrip =
        canonicalB01FormalDiskImFibreRoundtripSurface
    ; reverseLiftConstructedForAllImPoints =
        false
    ; reverseLiftConstructedForAllImPointsIsFalse =
        refl
    ; imModalQuotientEqualitySocket =
        "DASHI-side-depth-zero-and-depth-one-agreement-imply-Im-modal-equality; imported-DCHoTT-modal-reflection-remains-open"
    ; imModalQuotientEqualitySocket-v =
        refl
    }

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

data Paper2CarrierGeometryMilestone : Set where
  b01CarrierToFormalDSpace :
    Paper2CarrierGeometryMilestone

  b02WaveCoherentFlatFormalDisk :
    Paper2CarrierGeometryMilestone

  b03WeakBGGStructureBinding :
    Paper2CarrierGeometryMilestone

canonicalPaper2CarrierGeometryMilestones :
  List Paper2CarrierGeometryMilestone
canonicalPaper2CarrierGeometryMilestones =
  b01CarrierToFormalDSpace
  ∷ b02WaveCoherentFlatFormalDisk
  ∷ b03WeakBGGStructureBinding
  ∷ []

data Paper2CarrierGeometrySprintPromotionStatus : Set where
  promoteAfterSprintOnly :
    Paper2CarrierGeometrySprintPromotionStatus

  alreadyPromotedBySafePostulate :
    Paper2CarrierGeometrySprintPromotionStatus

record TierBPaper2CarrierGeometrySprintAccounting : Setω where
  field
    sprintName :
      String

    sprintName-v :
      sprintName
      ≡
      "Tier B / Paper 2 carrier-geometry sprint"

    milestones :
      List Paper2CarrierGeometryMilestone

    milestonesAreCanonical :
      milestones
      ≡
      canonicalPaper2CarrierGeometryMilestones

    b01Status :
      Paper2CarrierGeometrySprintPromotionStatus

    b01Status-v :
      b01Status
      ≡
      promoteAfterSprintOnly

    b02Status :
      Paper2CarrierGeometrySprintPromotionStatus

    b02Status-v :
      b02Status
      ≡
      promoteAfterSprintOnly

    b03Status :
      Paper2CarrierGeometrySprintPromotionStatus

    b03Status-v :
      b03Status
      ≡
      promoteAfterSprintOnly

    weakBGCorrespondenceCitationStatus :
      String

    weakBGCorrespondenceCitationStatus-v :
      weakBGCorrespondenceCitationStatus
      ≡
      "WeakBGCorrespondence needs a precise Wellen DCHoTT thesis theorem/page citation before it can be used as an authority citation"

    flagSplitArchitecture :
      String

    flagSplitArchitecture-v :
      flagSplitArchitecture
      ≡
      "--cohesion and --cubical are incompatible in the current local setup; use separately compiled modules connected by a proof-erasing interface carrying postulates/types"

    noPromotionReceiptConstructed :
      Bool

    noPromotionReceiptConstructedIsTrue :
      noPromotionReceiptConstructed
      ≡
      true

    governanceBoundary :
      List String

open TierBPaper2CarrierGeometrySprintAccounting public

canonicalTierBPaper2CarrierGeometrySprintAccounting :
  TierBPaper2CarrierGeometrySprintAccounting
canonicalTierBPaper2CarrierGeometrySprintAccounting =
  record
    { sprintName =
        "Tier B / Paper 2 carrier-geometry sprint"
    ; sprintName-v =
        refl
    ; milestones =
        canonicalPaper2CarrierGeometryMilestones
    ; milestonesAreCanonical =
        refl
    ; b01Status =
        promoteAfterSprintOnly
    ; b01Status-v =
        refl
    ; b02Status =
        promoteAfterSprintOnly
    ; b02Status-v =
        refl
    ; b03Status =
        promoteAfterSprintOnly
    ; b03Status-v =
        refl
    ; weakBGCorrespondenceCitationStatus =
        "WeakBGCorrespondence needs a precise Wellen DCHoTT thesis theorem/page citation before it can be used as an authority citation"
    ; weakBGCorrespondenceCitationStatus-v =
        refl
    ; flagSplitArchitecture =
        "--cohesion and --cubical are incompatible in the current local setup; use separately compiled modules connected by a proof-erasing interface carrying postulates/types"
    ; flagSplitArchitecture-v =
        refl
    ; noPromotionReceiptConstructed =
        true
    ; noPromotionReceiptConstructedIsTrue =
        refl
    ; governanceBoundary =
        "B0.1, B0.2, and B0.3 are promote-after-sprint targets in this file"
        ∷ "no safe-postulate promotion of B0.1, B0.2, or B0.3 is introduced by this accounting surface"
        ∷ "WeakBGCorrespondence is only a named target until the exact Wellen DCHoTT thesis theorem and page citation are supplied"
        ∷ "carrier/cohesion code and cubical quotient code must remain in separate flag lanes"
        ∷ "the cross-lane bridge may expose erased postulates/types but not a mixed --cohesion/--cubical import"
        ∷ []
    }

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

  missingProFinSetCategoryChain :
    DCHoTTB0BridgeBlocker

  missingCondensedEmbeddingAdapter :
    DCHoTTB0BridgeBlocker

  missingDCHoTTFormalSpaceAdapter :
    DCHoTTB0BridgeBlocker

  missingFormalDiskEquivalenceAdapter :
    DCHoTTB0BridgeBlocker

  missingReverseImLiftAdapter :
    DCHoTTB0BridgeBlocker

  missingImModalQuotientEqualityAdapter :
    DCHoTTB0BridgeBlocker

  missingWaveCoherentToFlat :
    DCHoTTB0BridgeBlocker

  missingFlatFormalDiskTrivialization :
    DCHoTTB0BridgeBlocker

  missingRefinementToGStr :
    DCHoTTB0BridgeBlocker

  missingRefinementStableFrameMetricTower :
    DCHoTTB0BridgeBlocker

  missingDCHoTTGStructureReduction :
    DCHoTTB0BridgeBlocker

  missingGStrToLeviCivita :
    DCHoTTB0BridgeBlocker

canonicalDCHoTTB0BridgeBlockers :
  List DCHoTTB0BridgeBlocker
canonicalDCHoTTB0BridgeBlockers =
  missingCarrierToDSpace
  ∷ missingLimitProjectionCompatibility
  ∷ missingProFinSetCategoryChain
  ∷ missingCondensedEmbeddingAdapter
  ∷ missingDCHoTTFormalSpaceAdapter
  ∷ missingFormalDiskEquivalenceAdapter
  ∷ missingReverseImLiftAdapter
  ∷ missingImModalQuotientEqualityAdapter
  ∷ missingWaveCoherentToFlat
  ∷ missingFlatFormalDiskTrivialization
  ∷ missingRefinementToGStr
  ∷ missingRefinementStableFrameMetricTower
  ∷ missingDCHoTTGStructureReduction
  ∷ missingGStrToLeviCivita
  ∷ []

data FlatFormalDiskOpenObligation : Set where
  missingOperatorNormTransportDefect :
    FlatFormalDiskOpenObligation

  missingTransportDefectNorm :
    FlatFormalDiskOpenObligation

  missingCauchyCompletenessForTransportLimit :
    FlatFormalDiskOpenObligation

  missingSummableWaveCoherenceDecay :
    FlatFormalDiskOpenObligation

  missingLimitParallelTransport :
    FlatFormalDiskOpenObligation

  missingHolonomyLimitTriviality :
    FlatFormalDiskOpenObligation

  missingDCHoTTFormalDiskTrivialization :
    FlatFormalDiskOpenObligation

canonicalFlatFormalDiskOpenObligations :
  List FlatFormalDiskOpenObligation
canonicalFlatFormalDiskOpenObligations =
  missingOperatorNormTransportDefect
  ∷ missingTransportDefectNorm
  ∷ missingCauchyCompletenessForTransportLimit
  ∷ missingSummableWaveCoherenceDecay
  ∷ missingLimitParallelTransport
  ∷ missingHolonomyLimitTriviality
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

    OperatorNormCarrier :
      Set

    transportDefectOperatorNorm :
      ℕ →
      OperatorNormCarrier

    operatorNormCompletenessTarget :
      String

    operatorNormCompletenessTarget-v :
      operatorNormCompletenessTarget
      ≡
      "target-only-complete-operator-norm-space-needed-for-wave-coherence-limit"

    operatorNormLimitTarget :
      String

    operatorNormLimitTarget-v :
      operatorNormLimitTarget
      ≡
      "target-only-transport-defect-operator-norm-tends-to-zero"

    HolonomyLoopAtDepth :
      ℕ →
      Set

    holonomyDefectBound :
      ℕ →
      ℕ

    holonomyDefectBoundRefinesCarrierBound :
      holonomyDefectBound
      ≡
      ProObjectCarrier.waveCoherenceBound P

    holonomyLimitTrivialityTarget :
      String

    holonomyLimitTrivialityTarget-v :
      holonomyLimitTrivialityTarget
      ≡
      "target-only-holonomy-defect-around-refinement-loops-tends-to-trivial"

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

data DiscreteToSmoothRoadmapStatus : Set where
  roadmapIndexedOnlyNoDiscreteSmoothProof :
    DiscreteToSmoothRoadmapStatus

data DiscreteToSmoothRoadmapObligation : Set where
  finiteRefinementCategory :
    DiscreteToSmoothRoadmapObligation

  proFinSetCompletionTarget :
    DiscreteToSmoothRoadmapObligation

  condensedFunctorTarget :
    DiscreteToSmoothRoadmapObligation

  dchottFormalSpaceTarget :
    DiscreteToSmoothRoadmapObligation

  condensedProfiniteEmbedding :
    DiscreteToSmoothRoadmapObligation

  formalDiskEquivalenceTarget :
    DiscreteToSmoothRoadmapObligation

  operatorNormWaveCoherence :
    DiscreteToSmoothRoadmapObligation

  pathIndependenceHolonomyLimit :
    DiscreteToSmoothRoadmapObligation

  ambroseSingerZeroCurvatureTarget :
    DiscreteToSmoothRoadmapObligation

  tangentCategoryLayerTarget :
    DiscreteToSmoothRoadmapObligation

  dchottTangentEquivalenceObligationTarget :
    DiscreteToSmoothRoadmapObligation

canonicalDiscreteToSmoothRoadmapObligations :
  List DiscreteToSmoothRoadmapObligation
canonicalDiscreteToSmoothRoadmapObligations =
  finiteRefinementCategory
  ∷ proFinSetCompletionTarget
  ∷ condensedFunctorTarget
  ∷ dchottFormalSpaceTarget
  ∷ condensedProfiniteEmbedding
  ∷ formalDiskEquivalenceTarget
  ∷ operatorNormWaveCoherence
  ∷ pathIndependenceHolonomyLimit
  ∷ ambroseSingerZeroCurvatureTarget
  ∷ tangentCategoryLayerTarget
  ∷ dchottTangentEquivalenceObligationTarget
  ∷ []

data DiscreteToSmoothRoadmapBlocker : Set where
  missingFiniteRefinementCategory :
    DiscreteToSmoothRoadmapBlocker

  missingProFinSetCompletionFunctor :
    DiscreteToSmoothRoadmapBlocker

  missingCondensedSetFunctor :
    DiscreteToSmoothRoadmapBlocker

  missingCondensedEmbeddingCompatibility :
    DiscreteToSmoothRoadmapBlocker

  missingDCHoTTFormalSpaceCarrier :
    DiscreteToSmoothRoadmapBlocker

  missingDCHoTTFormalDiskFamily :
    DiscreteToSmoothRoadmapBlocker

  missingFormalDiskEquivalenceWitness :
    DiscreteToSmoothRoadmapBlocker

  missingOperatorNormAdapter :
    DiscreteToSmoothRoadmapBlocker

  missingHolonomyLimitAdapter :
    DiscreteToSmoothRoadmapBlocker

  missingZeroCurvatureToFlatnessAdapter :
    DiscreteToSmoothRoadmapBlocker

  missingFirstGradedFiltration :
    DiscreteToSmoothRoadmapBlocker

  missingTangentCategoryOperations :
    DiscreteToSmoothRoadmapBlocker

  missingTangentCategoryAxioms :
    DiscreteToSmoothRoadmapBlocker

  missingDCHoTTTangentExponential :
    DiscreteToSmoothRoadmapBlocker

canonicalDiscreteToSmoothRoadmapBlockers :
  List DiscreteToSmoothRoadmapBlocker
canonicalDiscreteToSmoothRoadmapBlockers =
  missingFiniteRefinementCategory
  ∷ missingProFinSetCompletionFunctor
  ∷ missingCondensedSetFunctor
  ∷ missingCondensedEmbeddingCompatibility
  ∷ missingDCHoTTFormalSpaceCarrier
  ∷ missingDCHoTTFormalDiskFamily
  ∷ missingFormalDiskEquivalenceWitness
  ∷ missingOperatorNormAdapter
  ∷ missingHolonomyLimitAdapter
  ∷ missingZeroCurvatureToFlatnessAdapter
  ∷ missingFirstGradedFiltration
  ∷ missingTangentCategoryOperations
  ∷ missingTangentCategoryAxioms
  ∷ missingDCHoTTTangentExponential
  ∷ []

-- Professor-facing B0.1/B0.2 roadmap surface.
--
-- This record turns the discrete-to-smooth story into typed target sockets.  It
-- intentionally does not construct condensed mathematics, a DCHoTT formal
-- disk equivalence, an analytic operator norm, holonomy triviality, or an
-- Ambrose-Singer theorem.
record DiscreteToSmoothRoadmapSurface (P : ProObjectCarrier) : Setω where
  field
    status :
      DiscreteToSmoothRoadmapStatus

    roadmapObligations :
      List DiscreteToSmoothRoadmapObligation

    roadmapObligationsAreCanonical :
      roadmapObligations
      ≡
      canonicalDiscreteToSmoothRoadmapObligations

    exactBlockers :
      List DiscreteToSmoothRoadmapBlocker

    exactBlockersAreCanonical :
      exactBlockers
      ≡
      canonicalDiscreteToSmoothRoadmapBlockers

    FiniteRefinementCategory :
      Set

    ProFinSetCategory :
      Set

    CondensedSetCategory :
      Set

    DCHoTTFormalSpaceCategory :
      Set

    finiteToProFinSet :
      FiniteRefinementCategory →
      ProFinSetCategory

    proFinSetToCondensed :
      ProFinSetCategory →
      CondensedSetCategory

    condensedToDCHoTTFormalSpace :
      CondensedSetCategory →
      DCHoTTFormalSpaceCategory

    categoryChainTarget :
      String

    categoryChainTarget-v :
      categoryChainTarget
      ≡
      "target-only-FinRefinement-to-ProFinSet-to-Condensed-to-DCHoTT-formal-space"

    CondensedCarrier :
      Set

    ProfiniteCarrier :
      Set

    condensedEmbedding :
      ProObjectPoint P →
      CondensedCarrier

    profiniteShadow :
      ProObjectPoint P →
      ProfiniteCarrier

    condensedProfiniteCompatibilityTarget :
      String

    condensedProfiniteCompatibilityTarget-v :
      condensedProfiniteCompatibilityTarget
      ≡
      "target-only-compatible-family-embeds-into-condensed-profinite-smoothable-carrier"

    dashiFormalDiskAt :
      ProObjectPoint P →
      Set₁

    dashiFormalDiskAtIsScaffold :
      (x : ProObjectPoint P) →
      dashiFormalDiskAt x
      ≡
      FormalDisk x

    dchottFormalDiskTarget :
      ProObjectPoint P →
      Set₁

    dchottFormalSpaceOfPoint :
      ProObjectPoint P →
      DCHoTTFormalSpaceCategory

    formalDiskEquivalenceTargetName :
      String

    formalDiskEquivalenceTargetName-v :
      formalDiskEquivalenceTargetName
      ≡
      "target-only-DASHI-formal-disk-equivalent-to-DCHoTT-formal-disk"

    formalDiskEquivalenceWitnessTarget :
      ProObjectPoint P →
      Set₁

    formalDiskEquivalenceBlocker :
      DiscreteToSmoothRoadmapBlocker

    formalDiskEquivalenceBlocker-v :
      formalDiskEquivalenceBlocker
      ≡
      missingFormalDiskEquivalenceWitness

    OperatorAtDepth :
      ℕ →
      Set

    operatorNormBound :
      ℕ →
      ℕ

    operatorNormBoundRefinesCarrierBound :
      operatorNormBound
      ≡
      ProObjectCarrier.waveCoherenceBound P

    operatorNormWaveCoherenceTarget :
      String

    operatorNormWaveCoherenceTarget-v :
      operatorNormWaveCoherenceTarget
      ≡
      "target-only-operator-norm-transport-defect-decays-through-refinement"

    PathAtDepth :
      ℕ →
      Set

    HolonomyAtDepth :
      (d : ℕ) →
      PathAtDepth d →
      Set

    holonomyLimitTarget :
      String

    holonomyLimitTarget-v :
      holonomyLimitTarget
      ≡
      "target-only-holonomy-around-refinement-loops-vanishes-in-the-limit"

    pathIndependenceTarget :
      String

    pathIndependenceTarget-v :
      pathIndependenceTarget
      ≡
      "target-only-limit-transport-is-path-independent"

    CurvatureAtDepth :
      ℕ →
      Set

    zeroCurvatureLimitTarget :
      String

    zeroCurvatureLimitTarget-v :
      zeroCurvatureLimitTarget
      ≡
      "target-only-curvature-obstruction-vanishes-in-the-flat-limit"

    ambroseSingerStyleTarget :
      String

    ambroseSingerStyleTarget-v :
      ambroseSingerStyleTarget
      ≡
      "target-only-Ambrose-Singer-style-zero-curvature-from-trivial-limit-holonomy"

    noCondensedProofHere :
      Bool

    noCondensedProofHere-v :
      noCondensedProofHere ≡ true

    noFormalDiskEquivalenceProofHere :
      Bool

    noFormalDiskEquivalenceProofHere-v :
      noFormalDiskEquivalenceProofHere ≡ true

    noAnalyticOperatorNormProofHere :
      Bool

    noAnalyticOperatorNormProofHere-v :
      noAnalyticOperatorNormProofHere ≡ true

    noHolonomyProofHere :
      Bool

    noHolonomyProofHere-v :
      noHolonomyProofHere ≡ true

    noAmbroseSingerProofHere :
      Bool

    noAmbroseSingerProofHere-v :
      noAmbroseSingerProofHere ≡ true

open DiscreteToSmoothRoadmapSurface public

data TangentCategoryAxiomTarget : Set where
  pZeroSectionLawTarget :
    TangentCategoryAxiomTarget

  addFiberwiseCommutativeMonoidTarget :
    TangentCategoryAxiomTarget

  liftNaturalityTarget :
    TangentCategoryAxiomTarget

  canonicalFlipInvolutionTarget :
    TangentCategoryAxiomTarget

  tangentPullbackStabilityTarget :
    TangentCategoryAxiomTarget

canonicalTangentCategoryAxiomTargets :
  List TangentCategoryAxiomTarget
canonicalTangentCategoryAxiomTargets =
  pZeroSectionLawTarget
  ∷ addFiberwiseCommutativeMonoidTarget
  ∷ liftNaturalityTarget
  ∷ canonicalFlipInvolutionTarget
  ∷ tangentPullbackStabilityTarget
  ∷ []

-- B0 tangent-category target surface.  The tangent bundle is indexed by the
-- first graded piece of a filtration on each finite refinement depth, then
-- lifted to pro-object points.  This names the operations expected of a
-- tangent category, but does not prove the tangent-category axioms.
record FirstGradedFiltrationTangentSurface
  (P : ProObjectCarrier) :
  Setω where
  field
    FiltrationAtDepth :
      (d : ℕ) →
      ProObjectCarrier.depthCarrier P d →
      ℕ →
      Set

    firstGradedAtDepth :
      (d : ℕ) →
      ProObjectCarrier.depthCarrier P d →
      Set

    firstGradedRefinement :
      (d : ℕ) →
      (x : ProObjectCarrier.depthCarrier P (suc d)) →
      firstGradedAtDepth (suc d) x →
      firstGradedAtDepth d (ProObjectCarrier.refinementMap P d x)

    TangentAt :
      ProObjectPoint P →
      Set

    tangentAtDepthZeroFirstGradedTarget :
      (x : ProObjectPoint P) →
      TangentAt x →
      firstGradedAtDepth zero (Im x)

    TangentBundle :
      Set₁

    tangentBundleTarget :
      String

    tangentBundleTarget-v :
      tangentBundleTarget
      ≡
      "target-only-tangent-bundle-on-ProObjectCarrier-from-first-graded-filtration"

    p :
      TangentBundle →
      ProObjectPoint P

    zeroT :
      ProObjectPoint P →
      TangentBundle

    SameTangentFiber :
      TangentBundle →
      TangentBundle →
      Set

    addT :
      (u v : TangentBundle) →
      SameTangentFiber u v →
      TangentBundle

    liftT :
      TangentBundle →
      TangentBundle

    canonicalFlipT :
      TangentBundle →
      TangentBundle

    tangentCategoryOperationsTarget :
      String

    tangentCategoryOperationsTarget-v :
      tangentCategoryOperationsTarget
      ≡
      "target-only-p-zero-add-lift-and-canonical-flip-for-DASHI-tangent-category"

    tangentCategoryAxiomTargets :
      List TangentCategoryAxiomTarget

    tangentCategoryAxiomTargetsAreCanonical :
      tangentCategoryAxiomTargets
      ≡
      canonicalTangentCategoryAxiomTargets

    tangentCategoryAxiomsAreTargetsOnly :
      Bool

    tangentCategoryAxiomsAreTargetsOnly-v :
      tangentCategoryAxiomsAreTargetsOnly
      ≡
      true

    DCHoTTFormalSpace :
      Set

    DCHoTTInfinitesimalD1 :
      Set

    DCHoTTExponential :
      DCHoTTFormalSpace →
      DCHoTTInfinitesimalD1 →
      Set

    dchottTangentBundleTarget :
      DCHoTTFormalSpace →
      Set

    dchottTangentEquivalenceTarget :
      String

    dchottTangentEquivalenceTarget-v :
      dchottTangentEquivalenceTarget
      ≡
      "target-only-DCHoTT-tangent-equivalence-TM-is-M-to-the-D1"

    dchottTangentEquivalenceWitnessTarget :
      Set₁

    noTangentCategoryProofHere :
      Bool

    noTangentCategoryProofHere-v :
      noTangentCategoryProofHere
      ≡
      true

open FirstGradedFiltrationTangentSurface public

data GStructureReductionOpenObligation : Set where
  missingDepthIndexedFrameBundle :
    GStructureReductionOpenObligation

  missingFrameRefinementCompatibility :
    GStructureReductionOpenObligation

  missingMetricCompatibilityTower :
    GStructureReductionOpenObligation

  missingMetricTowerRefinementMaps :
    GStructureReductionOpenObligation

  missingLorentzSignatureAdapter :
    GStructureReductionOpenObligation

  missingLorentzSignatureRefinementLock :
    GStructureReductionOpenObligation

  missingProFrameLimitConstruction :
    GStructureReductionOpenObligation

  missingActualDCHoTTGStructureBinding :
    GStructureReductionOpenObligation

  missingDCHoTTGStructureReductionWitness :
    GStructureReductionOpenObligation

  missingTorsionFreeSpecialization :
    GStructureReductionOpenObligation

canonicalGStructureReductionOpenObligations :
  List GStructureReductionOpenObligation
canonicalGStructureReductionOpenObligations =
  missingDepthIndexedFrameBundle
  ∷ missingFrameRefinementCompatibility
  ∷ missingMetricCompatibilityTower
  ∷ missingMetricTowerRefinementMaps
  ∷ missingLorentzSignatureAdapter
  ∷ missingLorentzSignatureRefinementLock
  ∷ missingProFrameLimitConstruction
  ∷ missingActualDCHoTTGStructureBinding
  ∷ missingDCHoTTGStructureReductionWitness
  ∷ missingTorsionFreeSpecialization
  ∷ []

-- B0.3 target: refinement-stable frame and metric data should reduce the
-- pro-object frame bundle to a Lorentz G-structure.  This surface only
-- records the DASHI-side tower and target; it does not construct a DCHoTT
-- G-structure value, torsion-free specialization, or Levi-Civita adapter.
record RefinementStableGStructureSurface (P : ProObjectCarrier) : Setω where
  field
    projectionSurface :
      ProLimitProjectionSurface P

    FrameAtDepth :
      ℕ →
      Set

    frameRefinementMap :
      (d : ℕ) →
      FrameAtDepth (suc d) →
      FrameAtDepth d

    frameOfDepthCarrier :
      (d : ℕ) →
      ProObjectCarrier.depthCarrier P d →
      FrameAtDepth d

    frameOfRefinementCompatible :
      (d : ℕ) →
      (x : ProObjectCarrier.depthCarrier P (suc d)) →
      frameRefinementMap d (frameOfDepthCarrier (suc d) x)
      ≡
      frameOfDepthCarrier d (ProObjectCarrier.refinementMap P d x)

    frameCompatibleWithCarrier :
      String

    frameCompatibleWithCarrier-v :
      frameCompatibleWithCarrier
      ≡
      "target-only-frames-classify-local-bases-for-depth-carrier-sites"

    depthIndexedFrameTowerTarget :
      String

    depthIndexedFrameTowerTarget-v :
      depthIndexedFrameTowerTarget
      ≡
      "target-only-frame-bundles-form-a-depth-indexed-refinement-compatible-tower"

    MetricAtDepth :
      ℕ →
      Set

    metricAtFrame :
      (d : ℕ) →
      FrameAtDepth d →
      MetricAtDepth d

    metricRefinementMap :
      (d : ℕ) →
      MetricAtDepth (suc d) →
      MetricAtDepth d

    metricAtFrameRefinementCompatible :
      (d : ℕ) →
      (f : FrameAtDepth (suc d)) →
      metricRefinementMap d (metricAtFrame (suc d) f)
      ≡
      metricAtFrame d (frameRefinementMap d f)

    MetricRelAtDepth :
      (d : ℕ) →
      FrameAtDepth d →
      FrameAtDepth d →
      Set

    metricRefinementCompatible :
      (d : ℕ) →
      Set

    metricRelRefinementCompatible :
      (d : ℕ) →
      (u v : FrameAtDepth (suc d)) →
      MetricRelAtDepth (suc d) u v →
      MetricRelAtDepth d
        (frameRefinementMap d u)
        (frameRefinementMap d v)

    compatibleMetricTowerTarget :
      String

    compatibleMetricTowerTarget-v :
      compatibleMetricTowerTarget
      ≡
      "target-only-metrics-refine-with-frame-tower-and-preserve-local-inner-product-relations"

    lorentzSignatureAdapter :
      Set

    SignatureClass :
      Set

    lorentz31 :
      SignatureClass

    signatureAtDepth :
      (d : ℕ) →
      FrameAtDepth d →
      SignatureClass

    signatureRefinementLocked :
      (d : ℕ) →
      (f : FrameAtDepth (suc d)) →
      signatureAtDepth d (frameRefinementMap d f)
      ≡
      signatureAtDepth (suc d) f

    lorentzSignatureAdapterTarget :
      String

    lorentzSignatureAdapterTarget-v :
      lorentzSignatureAdapterTarget
      ≡
      "target-only-Lorentz-signature-adapter-locks-compatible-metric-tower-to-3-plus-1-signature"

    ProFrameLimit :
      Set

    proFrameProjection :
      (d : ℕ) →
      ProFrameLimit →
      FrameAtDepth d

    proFrameProjectionCompatible :
      (d : ℕ) →
      (f : ProFrameLimit) →
      frameRefinementMap d (proFrameProjection (suc d) f)
      ≡
      proFrameProjection d f

    DCHoTTGStructureBinding :
      Set

    actualDCHoTTGStructureBindingBlocker :
      String

    actualDCHoTTGStructureBindingBlocker-v :
      actualDCHoTTGStructureBindingBlocker
      ≡
      "blocked-until-local-DCHoTT-G-structure-record-and-reduction-witness-are-bound"

    gStructureReductionTarget :
      String

    gStructureReductionTarget-v :
      gStructureReductionTarget
      ≡
      "target-only-refinement-stable-frame-and-metric-tower-should-define-Lorentz-G-structure-reduction"

    openGStructureObligations :
      List GStructureReductionOpenObligation

    openGStructureObligationsAreCanonical :
      openGStructureObligations
      ≡
      canonicalGStructureReductionOpenObligations

open RefinementStableGStructureSurface public

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
        "bind DASHI wave coherence to operator-norm transport-defect decay, completeness for the transport limit, trivial holonomy limit, and a homogeneous model whose formal disks are identified with the base disk"
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
        "construct a depth-indexed frame bundle, compatible metric refinement tower, Lorentz signature adapter, pro-frame limit, actual DCHoTT G-structure binding, and DCHoTT G-structure reduction witness"
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

    discreteToSmoothRoadmapStatus :
      DiscreteToSmoothRoadmapStatus

    discreteToSmoothRoadmapObligations :
      List DiscreteToSmoothRoadmapObligation

    discreteToSmoothRoadmapObligationsAreCanonical :
      discreteToSmoothRoadmapObligations
      ≡
      canonicalDiscreteToSmoothRoadmapObligations

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

    tierBPaper2CarrierGeometrySprintAccounting :
      TierBPaper2CarrierGeometrySprintAccounting

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
    ; discreteToSmoothRoadmapStatus =
        roadmapIndexedOnlyNoDiscreteSmoothProof
    ; discreteToSmoothRoadmapObligations =
        canonicalDiscreteToSmoothRoadmapObligations
    ; discreteToSmoothRoadmapObligationsAreCanonical =
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
    ; tierBPaper2CarrierGeometrySprintAccounting =
        canonicalTierBPaper2CarrierGeometrySprintAccounting
    ; futurePromotionReceiptBlocked =
        dchottB0PromotionReceiptImpossibleHere
    ; governanceBoundary =
        "B0 remains open: this index names sub-obligations only"
        ∷ "ProObjectCarrier records the inverse-limit target for Paper 2; it is not constructed here"
        ∷ "ProObjectPoint is the compatible-family type (x_d) with refinement coherence"
        ∷ "Im, FormallyClose, and FormalDisk record the depth-zero formal-disk scaffold for B0.1"
        ∷ "B01ImFormalDiskSocket records Im fibres, typed reverse-lift data, FormalDisk/Im-fibre roundtrips, and depth-0/depth-1 agreement to DASHI Im-modal equality; imported DCHoTT modal reflection remains open"
        ∷ "ProCompatibleFamily and ProLimitProjectionSurface record only the DASHI-side compatible-family cone"
        ∷ "limit projection compatibility does not imply a DCHoTT formal D-space, manifold, G-structure, or Levi-Civita adapter"
        ∷ "DiscreteToSmoothRoadmapSurface records B0.1/B0.2 targets for condensed/profinite embedding, formal disk equivalence, operator-norm wave-coherence, path-independence/holonomy limit, and Ambrose-Singer-style zero-curvature"
        ∷ "The roadmap surface is target-only and supplies no condensed proof, no formal disk equivalence proof, no analytic operator norm proof, no holonomy theorem, and no Ambrose-Singer theorem"
        ∷ "FirstGradedFiltrationTangentSurface records the B0 tangent-category target from first graded filtration, p/zero/add/lift/canonical-flip operations, axiom targets, and DCHoTT TM ~= M^D1 equivalence target without proof"
        ∷ "WaveCoherentFlatFormalDiskSurface records operator-norm transport-defect, completeness, and holonomy-limit targets without proving DCHoTT disk-bundle triviality"
        ∷ "RefinementStableGStructureSurface records the B0.3 depth-indexed frame tower, compatible metric tower, Lorentz signature adapter, and pro-frame target without constructing or binding a DCHoTT G-structure reduction"
        ∷ "Tier B / Paper 2 carrier-geometry sprint accounting keeps B0.1-B0.3 as promote-after-sprint targets"
        ∷ "WeakBGCorrespondence needs a precise Wellen DCHoTT thesis theorem/page citation before it can be used as an authority citation"
        ∷ "--cohesion and --cubical are locally incompatible; split carrier/cohesion and cubical code into separately compiled modules connected by erased postulates/types"
        ∷ "carrierToDSpace must bind DASHI carriers to DCHoTT formal D-spaces"
        ∷ "waveCoherentToFlat must connect DASHI wave coherence to homogeneous formal-disk triviality"
        ∷ "refinementToGStr must construct a G-structure lift compatible with refinement-stable frames and metric adapters"
        ∷ "gStrToLeviCivita is blocked on a missing torsion-free/metric-compatible DCHoTT specialization"
        ∷ "no DCHoTTB0PromotionReceipt is constructed or promoted here"
        ∷ []
    }
