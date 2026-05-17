module DASHI.Geometry.GStructureLeviCivitaBindingSurface where

open import Agda.Primitive using (Setω; lzero)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (ℕ; suc)

import DASHI.Geometry.DCHoTTBridgeObligationIndex as B0
import DASHI.Geometry.ConeTimeIsotropy as CTI
import DASHI.Geometry.SO31FirstProlongationZero as SO31P
import DASHI.Geometry.Signature.Signature31Instance as Sig31
import DASHI.Lorentz.ConeSignature as Cone

------------------------------------------------------------------------
-- B0.3 G-structure / Levi-Civita binding surface.
--
-- This module records the proof target that should eventually bind a
-- depth-indexed DASHI frame/metric tower to a Lorentzian SO(3,1)
-- G-structure socket and then to the Wellen torsion-free/Levi-Civita
-- theorem shape.  It deliberately does not import a fictional DCHoTT
-- torsion-free module and does not promote Levi-Civita.

data GStructureLeviCivitaBindingStatus : Set where
  gStructureLeviCivitaBindingTargetsOnlyNoPromotion :
    GStructureLeviCivitaBindingStatus

data GStructureLeviCivitaBindingBlocker : Set where
  missingDepthIndexedFrameBundle :
    GStructureLeviCivitaBindingBlocker

  missingFrameTowerMaps :
    GStructureLeviCivitaBindingBlocker

  missingCompatibleMetricTower :
    GStructureLeviCivitaBindingBlocker

  missingAdapter1SignatureGate :
    GStructureLeviCivitaBindingBlocker

  missingSO31ReductionWitness :
    GStructureLeviCivitaBindingBlocker

  missingActualDCHoTTGStructureBinding :
    GStructureLeviCivitaBindingBlocker

  missingPrincipalBundleSocket :
    GStructureLeviCivitaBindingBlocker

  missingWeakBGCorrespondenceAuthority :
    GStructureLeviCivitaBindingBlocker

  missingCubicalHITBGConstruction :
    GStructureLeviCivitaBindingBlocker

  missingLocalTrivialitySocket :
    GStructureLeviCivitaBindingBlocker

  missingWellenTheoremAuthority :
    GStructureLeviCivitaBindingBlocker

  missingWellenSocketDischarge :
    GStructureLeviCivitaBindingBlocker

  missingTorsionFreeMetricCompatibleAdapter :
    GStructureLeviCivitaBindingBlocker

  missingLeviCivitaUniquenessImport :
    GStructureLeviCivitaBindingBlocker

canonicalGStructureLeviCivitaBindingBlockers :
  List GStructureLeviCivitaBindingBlocker
canonicalGStructureLeviCivitaBindingBlockers =
  missingActualDCHoTTGStructureBinding
  ∷ missingPrincipalBundleSocket
  ∷ missingWeakBGCorrespondenceAuthority
  ∷ missingCubicalHITBGConstruction
  ∷ missingLocalTrivialitySocket
  ∷ missingWellenTheoremAuthority
  ∷ missingWellenSocketDischarge
  ∷ missingTorsionFreeMetricCompatibleAdapter
  ∷ missingLeviCivitaUniquenessImport
  ∷ []

-- Constructorless: no promotion authority is manufactured here.
data GStructureLeviCivitaPromotionAuthorityToken : Set where

transportAlong :
  {A : Set} →
  (P : A → Set) →
  {x y : A} →
  x ≡ y →
  P x →
  P y
transportAlong _ refl px =
  px

record IsContractible (A : Set) : Set where
  field
    center :
      A

    contraction :
      (x : A) →
      center ≡ x

open IsContractible public

unitContractible :
  IsContractible ⊤
unitContractible =
  record
    { center =
        tt
    ; contraction =
        λ { tt →
          refl }
    }

record CarrierContractibilitySurface
    (P : B0.ProObjectCarrier)
    (projection : B0.ProLimitProjectionSurface P)
    : Setω where
  field
    depthCarrierContractible :
      (d : ℕ) →
      IsContractible
        (B0.ProObjectCarrier.depthCarrier P d)

    proObjectLimitContractible :
      IsContractible
        (B0.ProObjectCarrier.proObjectLimit P)

    limitProjectionPreservesContractibleCenter :
      (d : ℕ) →
      B0.ProLimitProjectionSurface.limitProjection projection d
        (IsContractible.center proObjectLimitContractible)
      ≡
      IsContractible.center (depthCarrierContractible d)

    canonicalLimitBasepoint :
      B0.ProObjectCarrier.proObjectLimit P

    canonicalLimitBasepoint-v :
      canonicalLimitBasepoint
      ≡
      IsContractible.center proObjectLimitContractible

    canonicalProObjectBasepoint :
      B0.ProObjectPoint P

    canonicalProObjectBasepoint-v :
      canonicalProObjectBasepoint
      ≡
      B0.limitAsProObjectPoint projection canonicalLimitBasepoint

    carrierContractibilityShape :
      String

    carrierContractibilityShape-v :
      carrierContractibilityShape
      ≡
      "explicit-DASHI-side-contractible-depth-carriers-and-contractible-pro-object-limit"

    carrierContractibilityWitnessed :
      Bool

    carrierContractibilityWitnessed-v :
      carrierContractibilityWitnessed ≡ true

open CarrierContractibilitySurface public

carrierContractibilitySurface :
  (P : B0.ProObjectCarrier) →
  (projection : B0.ProLimitProjectionSurface P) →
  (depthContr :
    (d : ℕ) →
    IsContractible (B0.ProObjectCarrier.depthCarrier P d)) →
  (limitContr :
    IsContractible (B0.ProObjectCarrier.proObjectLimit P)) →
  ((d : ℕ) →
    B0.ProLimitProjectionSurface.limitProjection projection d
      (IsContractible.center limitContr)
      ≡
      IsContractible.center (depthContr d)) →
  CarrierContractibilitySurface P projection
carrierContractibilitySurface P projection depthContr limitContr preserves =
  record
    { depthCarrierContractible =
        depthContr
    ; proObjectLimitContractible =
        limitContr
    ; limitProjectionPreservesContractibleCenter =
        preserves
    ; canonicalLimitBasepoint =
        IsContractible.center limitContr
    ; canonicalLimitBasepoint-v =
        refl
    ; canonicalProObjectBasepoint =
        B0.limitAsProObjectPoint projection (IsContractible.center limitContr)
    ; canonicalProObjectBasepoint-v =
        refl
    ; carrierContractibilityShape =
        "explicit-DASHI-side-contractible-depth-carriers-and-contractible-pro-object-limit"
    ; carrierContractibilityShape-v =
        refl
    ; carrierContractibilityWitnessed =
        true
    ; carrierContractibilityWitnessed-v =
        refl
    }

record DepthIndexedFrameTowerSurface
    (P : B0.ProObjectCarrier)
    : Setω where
  field
    projectionSurface :
      B0.ProLimitProjectionSurface P

    FrameAtDepth :
      ℕ →
      Set

    frameProjectionMap :
      (d : ℕ) →
      FrameAtDepth (suc d) →
      FrameAtDepth d

    frameOfCarrier :
      (d : ℕ) →
      B0.ProObjectCarrier.depthCarrier P d →
      FrameAtDepth d

    frameTowerMapCompatible :
      (d : ℕ) →
      (x : B0.ProObjectCarrier.depthCarrier P (suc d)) →
      frameProjectionMap d (frameOfCarrier (suc d) x)
      ≡
      frameOfCarrier d (B0.ProObjectCarrier.refinementMap P d x)

    ProFrameLimit :
      Set

    proFrameProjection :
      (d : ℕ) →
      ProFrameLimit →
      FrameAtDepth d

    proFrameProjectionCompatible :
      (d : ℕ) →
      (f : ProFrameLimit) →
      frameProjectionMap d (proFrameProjection (suc d) f)
      ≡
      proFrameProjection d f

    frameTowerShape :
      String

    frameTowerShape-v :
      frameTowerShape
      ≡
      "depth-indexed-frame-bundles-with-compatible-refinement-projection-maps"

open DepthIndexedFrameTowerSurface public

record CompatibleMetricTowerSurface
    {P : B0.ProObjectCarrier}
    (frames : DepthIndexedFrameTowerSurface P)
    : Setω where
  field
    MetricAtDepth :
      ℕ →
      Set

    metricAtFrame :
      (d : ℕ) →
      DepthIndexedFrameTowerSurface.FrameAtDepth frames d →
      MetricAtDepth d

    metricProjectionMap :
      (d : ℕ) →
      MetricAtDepth (suc d) →
      MetricAtDepth d

    metricTowerCompatible :
      (d : ℕ) →
      (f : DepthIndexedFrameTowerSurface.FrameAtDepth frames (suc d)) →
      metricProjectionMap d (metricAtFrame (suc d) f)
      ≡
      metricAtFrame d
        (DepthIndexedFrameTowerSurface.frameProjectionMap frames d f)

    MetricRelationAtDepth :
      (d : ℕ) →
      DepthIndexedFrameTowerSurface.FrameAtDepth frames d →
      DepthIndexedFrameTowerSurface.FrameAtDepth frames d →
      Set

    metricRelationRefines :
      (d : ℕ) →
      (u v : DepthIndexedFrameTowerSurface.FrameAtDepth frames (suc d)) →
      MetricRelationAtDepth (suc d) u v →
      MetricRelationAtDepth d
        (DepthIndexedFrameTowerSurface.frameProjectionMap frames d u)
        (DepthIndexedFrameTowerSurface.frameProjectionMap frames d v)

    metricTowerShape :
      String

    metricTowerShape-v :
      metricTowerShape
      ≡
      "compatible-metric-tower-refines-with-frame-tower-and-preserves-metric-relations"

open CompatibleMetricTowerSurface public

canonicalDepthIndexedFrameTowerSurface :
  (P : B0.ProObjectCarrier) →
  B0.ProLimitProjectionSurface P →
  DepthIndexedFrameTowerSurface P
canonicalDepthIndexedFrameTowerSurface P projection =
  record
    { projectionSurface =
        projection
    ; FrameAtDepth =
        λ d →
          B0.ProObjectCarrier.depthCarrier P d
    ; frameProjectionMap =
        λ d →
          B0.ProObjectCarrier.refinementMap P d
    ; frameOfCarrier =
        λ _ x →
          x
    ; frameTowerMapCompatible =
        λ _ _ →
          refl
    ; ProFrameLimit =
        B0.ProObjectCarrier.proObjectLimit P
    ; proFrameProjection =
        λ d x →
          B0.ProLimitProjectionSurface.limitProjection projection d x
    ; proFrameProjectionCompatible =
        λ d x →
          B0.ProLimitProjectionSurface.limitProjectionCompatible projection d x
    ; frameTowerShape =
        "depth-indexed-frame-bundles-with-compatible-refinement-projection-maps"
    ; frameTowerShape-v =
        refl
    }

unitCompatibleMetricTowerSurface :
  {P : B0.ProObjectCarrier} →
  (frames : DepthIndexedFrameTowerSurface P) →
  CompatibleMetricTowerSurface frames
unitCompatibleMetricTowerSurface frames =
  record
    { MetricAtDepth =
        λ _ →
          ⊤
    ; metricAtFrame =
        λ _ _ →
          tt
    ; metricProjectionMap =
        λ _ _ →
          tt
    ; metricTowerCompatible =
        λ _ _ →
          refl
    ; MetricRelationAtDepth =
        λ _ _ _ →
          ⊤
    ; metricRelationRefines =
        λ _ _ _ _ →
          tt
    ; metricTowerShape =
        "compatible-metric-tower-refines-with-frame-tower-and-preserves-metric-relations"
    ; metricTowerShape-v =
        refl
    }

record SO31ReductionSocket
    {P : B0.ProObjectCarrier}
    (frames : DepthIndexedFrameTowerSurface P)
    (metrics : CompatibleMetricTowerSurface frames)
    : Setω where
  field
    SignatureClass :
      Set

    lorentz31 :
      SignatureClass

    signatureAtDepth :
      (d : ℕ) →
      DepthIndexedFrameTowerSurface.FrameAtDepth frames d →
      SignatureClass

    signatureTowerLocked :
      (d : ℕ) →
      (f : DepthIndexedFrameTowerSurface.FrameAtDepth frames (suc d)) →
      signatureAtDepth d
        (DepthIndexedFrameTowerSurface.frameProjectionMap frames d f)
      ≡
      signatureAtDepth (suc d) f

    adapter1SignatureGate :
      String

    adapter1SignatureGate-v :
      adapter1SignatureGate
      ≡
      "Adapter1-signature-gate-locks-compatible-metric-tower-to-Lorentz-3-plus-1"

    so31ReductionShape :
      String

    so31ReductionShape-v :
      so31ReductionShape
      ≡
      "target-only-SO31-reduction-of-frame-tower-after-Lorentz-signature-gate"

    so31ReductionPromoted :
      Bool

    so31ReductionPromoted-v :
      so31ReductionPromoted ≡ false

open SO31ReductionSocket public

record PrincipalBundleLocalTrivialitySocket : Setω where
  field
    BaseSpace :
      Set

    PrincipalBundle :
      Set

    StructureGroup :
      Set

    bundleProjection :
      PrincipalBundle →
      BaseSpace

    LocalPatch :
      BaseSpace →
      Set

    localTrivialization :
      (b : BaseSpace) →
      LocalPatch b →
      PrincipalBundle →
      Set

    transitionFunction :
      (b : BaseSpace) →
      LocalPatch b →
      LocalPatch b →
      StructureGroup

    principalBundleSocketShape :
      String

    principalBundleSocketShape-v :
      principalBundleSocketShape
      ≡
      "remaining-principal-SO31-bundle-socket-over-the-depth-indexed-frame-base"

    localTrivialitySocketShape :
      String

    localTrivialitySocketShape-v :
      localTrivialitySocketShape
      ≡
      "remaining-local-triviality-atlas-and-transition-function-socket"

    principalBundleConstructed :
      Bool

    principalBundleConstructed-v :
      principalBundleConstructed ≡ false

    localTrivialityConstructed :
      Bool

    localTrivialityConstructed-v :
      localTrivialityConstructed ≡ false

open PrincipalBundleLocalTrivialitySocket public

canonicalPrincipalBundleLocalTrivialitySocket :
  PrincipalBundleLocalTrivialitySocket
canonicalPrincipalBundleLocalTrivialitySocket =
  record
    { BaseSpace =
        ⊤
    ; PrincipalBundle =
        ⊤
    ; StructureGroup =
        ⊤
    ; bundleProjection =
        λ _ →
          tt
    ; LocalPatch =
        λ _ →
          ⊤
    ; localTrivialization =
        λ _ _ _ →
          ⊤
    ; transitionFunction =
        λ _ _ _ →
          tt
    ; principalBundleSocketShape =
        "remaining-principal-SO31-bundle-socket-over-the-depth-indexed-frame-base"
    ; principalBundleSocketShape-v =
        refl
    ; localTrivialitySocketShape =
        "remaining-local-triviality-atlas-and-transition-function-socket"
    ; localTrivialitySocketShape-v =
        refl
    ; principalBundleConstructed =
        false
    ; principalBundleConstructed-v =
        refl
    ; localTrivialityConstructed =
        false
    ; localTrivialityConstructed-v =
        refl
    }

record SO31TorsorFibreSurface : Setω where
  field
    BaseSpace :
      Set

    SO31Group :
      Set

    TorsorTotal :
      Set

    torsorProjection :
      TorsorTotal →
      BaseSpace

    SO31TorsorFibre :
      BaseSpace →
      Set

    SO31TorsorFibre-v :
      (b : BaseSpace) →
      SO31TorsorFibre b
      ≡
      Σ TorsorTotal
        (λ p →
          torsorProjection p
          ≡
          b)

    so31Action :
      (b : BaseSpace) →
      SO31Group →
      SO31TorsorFibre b →
      SO31TorsorFibre b

    actionFreeTarget :
      (b : BaseSpace) →
      SO31Group →
      SO31Group →
      SO31TorsorFibre b →
      Set

    actionTransitiveTarget :
      (b : BaseSpace) →
      SO31TorsorFibre b →
      SO31TorsorFibre b →
      Set

    torsorFibreShape :
      String

    torsorFibreShape-v :
      torsorFibreShape
      ≡
      "SO31-torsor-fibres-over-base-with-action-free-and-transitive-targets"

    freeActionProved :
      Bool

    freeActionProved-v :
      freeActionProved ≡ false

    transitiveActionProved :
      Bool

    transitiveActionProved-v :
      transitiveActionProved ≡ false

open SO31TorsorFibreSurface public

canonicalSO31TorsorFibreSurface :
  SO31TorsorFibreSurface
canonicalSO31TorsorFibreSurface =
  record
    { BaseSpace =
        ⊤
    ; SO31Group =
        ⊤
    ; TorsorTotal =
        ⊤
    ; torsorProjection =
        λ _ →
          tt
    ; SO31TorsorFibre =
        λ b →
          Σ ⊤
            (λ p →
              tt
              ≡
              b)
    ; SO31TorsorFibre-v =
        λ _ →
          refl
    ; so31Action =
        λ _ _ fibre →
          fibre
    ; actionFreeTarget =
        λ _ _ _ _ →
          ⊤
    ; actionTransitiveTarget =
        λ _ _ _ →
          ⊤
    ; torsorFibreShape =
        "SO31-torsor-fibres-over-base-with-action-free-and-transitive-targets"
    ; torsorFibreShape-v =
        refl
    ; freeActionProved =
        false
    ; freeActionProved-v =
        refl
    ; transitiveActionProved =
        false
    ; transitiveActionProved-v =
        refl
    }

record WeakBGCorrespondenceAuthoritySurface : Setω where
  field
    so31TorsorFibreSurface :
      SO31TorsorFibreSurface

    PrincipalBundleSurface :
      Set

    principalBundleSocket :
      PrincipalBundleLocalTrivialitySocket

    principalBundleSurfaceShape :
      String

    principalBundleSurfaceShape-v :
      principalBundleSurfaceShape
      ≡
      "local-principal-bundle-placeholder-bound-to-existing-principal-bundle-socket"

    torsorToPrincipalBundleTarget :
      SO31TorsorFibreSurface.TorsorTotal so31TorsorFibreSurface →
      PrincipalBundleSurface →
      Set

    principalBundleToTorsorTarget :
      PrincipalBundleSurface →
      SO31TorsorFibreSurface.TorsorTotal so31TorsorFibreSurface →
      Set

    WeakBGCorrespondence :
      Set₁

    WeakBGCorrespondence-v :
      WeakBGCorrespondence
      ≡
      Σ Set
        (λ TorsorCarrier →
          TorsorCarrier →
          PrincipalBundleSurface →
          Set)

    authorityShape :
      String

    authorityShape-v :
      authorityShape
      ≡
      "WeakBGCorrespondence-authority-shape-for-SO31-torsors-to-principal-bundles"

    cubicalHITBlocker :
      String

    cubicalHITBlocker-v :
      cubicalHITBlocker
      ≡
      "blocked-until-cubical-HIT-BG-classifying-stack-and-torsor-principal-bundle-equivalence-are-imported"

    cubicalHITBlockerPresent :
      Bool

    cubicalHITBlockerPresent-v :
      cubicalHITBlockerPresent ≡ true

    weakBGAuthorityImported :
      Bool

    weakBGAuthorityImported-v :
      weakBGAuthorityImported ≡ false

    torsorToPrincipalBundlePromoted :
      Bool

    torsorToPrincipalBundlePromoted-v :
      torsorToPrincipalBundlePromoted ≡ false

    b03ClosureModuloWeakBGOnly :
      Bool

    b03ClosureModuloWeakBGOnly-v :
      b03ClosureModuloWeakBGOnly ≡ true

    canonicalReceipt :
      String

    canonicalReceipt-v :
      canonicalReceipt
      ≡
      "weak-BG-correspondence-surface-records-SO31-torsor-fibres-and-torsor-to-principal-bundle-targets-with-cubical-HIT-blocker"

open WeakBGCorrespondenceAuthoritySurface public

canonicalWeakBGCorrespondenceAuthoritySurface :
  WeakBGCorrespondenceAuthoritySurface
canonicalWeakBGCorrespondenceAuthoritySurface =
  record
    { so31TorsorFibreSurface =
        canonicalSO31TorsorFibreSurface
    ; PrincipalBundleSurface =
        ⊤
    ; principalBundleSocket =
        canonicalPrincipalBundleLocalTrivialitySocket
    ; principalBundleSurfaceShape =
        "local-principal-bundle-placeholder-bound-to-existing-principal-bundle-socket"
    ; principalBundleSurfaceShape-v =
        refl
    ; torsorToPrincipalBundleTarget =
        λ _ _ →
          ⊤
    ; principalBundleToTorsorTarget =
        λ _ _ →
          ⊤
    ; WeakBGCorrespondence =
        Σ Set
          (λ TorsorCarrier →
            TorsorCarrier →
            ⊤ →
            Set)
    ; WeakBGCorrespondence-v =
        refl
    ; authorityShape =
        "WeakBGCorrespondence-authority-shape-for-SO31-torsors-to-principal-bundles"
    ; authorityShape-v =
        refl
    ; cubicalHITBlocker =
        "blocked-until-cubical-HIT-BG-classifying-stack-and-torsor-principal-bundle-equivalence-are-imported"
    ; cubicalHITBlocker-v =
        refl
    ; cubicalHITBlockerPresent =
        true
    ; cubicalHITBlockerPresent-v =
        refl
    ; weakBGAuthorityImported =
        false
    ; weakBGAuthorityImported-v =
        refl
    ; torsorToPrincipalBundlePromoted =
        false
    ; torsorToPrincipalBundlePromoted-v =
        refl
    ; b03ClosureModuloWeakBGOnly =
        true
    ; b03ClosureModuloWeakBGOnly-v =
        refl
    ; canonicalReceipt =
        "weak-BG-correspondence-surface-records-SO31-torsor-fibres-and-torsor-to-principal-bundle-targets-with-cubical-HIT-blocker"
    ; canonicalReceipt-v =
        refl
    }

PrincipalFiber :
  (socket : PrincipalBundleLocalTrivialitySocket) →
  PrincipalBundleLocalTrivialitySocket.BaseSpace socket →
  Set
PrincipalFiber socket b =
  Σ (PrincipalBundleLocalTrivialitySocket.PrincipalBundle socket)
    (λ p →
      PrincipalBundleLocalTrivialitySocket.bundleProjection socket p
      ≡
      b)

principalFiberTransport :
  (socket : PrincipalBundleLocalTrivialitySocket) →
  (baseContractible :
    IsContractible
      (PrincipalBundleLocalTrivialitySocket.BaseSpace socket)) →
  PrincipalFiber socket (IsContractible.center baseContractible) →
  (b : PrincipalBundleLocalTrivialitySocket.BaseSpace socket) →
  PrincipalFiber socket b
principalFiberTransport socket baseContractible liftAtCenter b =
  transportAlong
    (PrincipalFiber socket)
    (IsContractible.contraction baseContractible b)
    liftAtCenter

record CanonicalSectionBasepointLift
    (socket : PrincipalBundleLocalTrivialitySocket)
    : Set where
  field
    baseContractible :
      IsContractible
        (PrincipalBundleLocalTrivialitySocket.BaseSpace socket)

    liftAtContractibleCenter :
      PrincipalFiber socket (IsContractible.center baseContractible)

    sectionFiber :
      (b : PrincipalBundleLocalTrivialitySocket.BaseSpace socket) →
      PrincipalFiber socket b

    sectionFiber-v :
      sectionFiber
      ≡
      principalFiberTransport socket baseContractible liftAtContractibleCenter

    canonicalSection :
      PrincipalBundleLocalTrivialitySocket.BaseSpace socket →
      PrincipalBundleLocalTrivialitySocket.PrincipalBundle socket

    canonicalSection-v :
      canonicalSection
      ≡
      (λ b →
        fst (sectionFiber b))

    canonicalSectionProjectsToBase :
      (b : PrincipalBundleLocalTrivialitySocket.BaseSpace socket) →
      PrincipalBundleLocalTrivialitySocket.bundleProjection socket
        (fst (sectionFiber b))
      ≡
      b

    canonicalSectionProjectsToBase-v :
      canonicalSectionProjectsToBase
      ≡
      (λ b →
        snd (sectionFiber b))

    canonicalSectionBasepointLiftShape :
      String

    canonicalSectionBasepointLiftShape-v :
      canonicalSectionBasepointLiftShape
      ≡
      "contractible-base-center-lift-transported-to-a-global-principal-bundle-section"

    canonicalSectionBasepointLiftWitnessed :
      Bool

    canonicalSectionBasepointLiftWitnessed-v :
      canonicalSectionBasepointLiftWitnessed ≡ true

open CanonicalSectionBasepointLift public

canonicalSectionBasepointLift :
  (socket : PrincipalBundleLocalTrivialitySocket) →
  (baseContractible :
    IsContractible
      (PrincipalBundleLocalTrivialitySocket.BaseSpace socket)) →
  PrincipalFiber socket (IsContractible.center baseContractible) →
  CanonicalSectionBasepointLift socket
canonicalSectionBasepointLift socket baseContractible liftAtCenter =
  record
    { baseContractible =
        baseContractible
    ; liftAtContractibleCenter =
        liftAtCenter
    ; sectionFiber =
        principalFiberTransport socket baseContractible liftAtCenter
    ; sectionFiber-v =
        refl
    ; canonicalSection =
        λ b →
          fst (principalFiberTransport socket baseContractible liftAtCenter b)
    ; canonicalSection-v =
        refl
    ; canonicalSectionProjectsToBase =
        λ b →
          snd (principalFiberTransport socket baseContractible liftAtCenter b)
    ; canonicalSectionProjectsToBase-v =
        refl
    ; canonicalSectionBasepointLiftShape =
        "contractible-base-center-lift-transported-to-a-global-principal-bundle-section"
    ; canonicalSectionBasepointLiftShape-v =
        refl
    ; canonicalSectionBasepointLiftWitnessed =
        true
    ; canonicalSectionBasepointLiftWitnessed-v =
        refl
    }

record ContractibleBasePrincipalBundleTrivialitySurface
    (socket : PrincipalBundleLocalTrivialitySocket)
    : Set where
  field
    sectionBasepointLift :
      CanonicalSectionBasepointLift socket

    globalSectionConstructed :
      Bool

    globalSectionConstructed-v :
      globalSectionConstructed ≡ true

    contractibleBaseTrivialityShape :
      String

    contractibleBaseTrivialityShape-v :
      contractibleBaseTrivialityShape
      ≡
      "DASHI-side-contractible-base-gives-a-global-section-witness-for-the-principal-bundle-socket"

    dchottPrincipalBundleTrivialityImported :
      Bool

    dchottPrincipalBundleTrivialityImported-v :
      dchottPrincipalBundleTrivialityImported ≡ false

    principalBundleTrivialityPromoted :
      Bool

    principalBundleTrivialityPromoted-v :
      principalBundleTrivialityPromoted ≡ false

open ContractibleBasePrincipalBundleTrivialitySurface public

contractibleBaseImpliesPrincipalBundleTrivialitySurface :
  (socket : PrincipalBundleLocalTrivialitySocket) →
  (baseContractible :
    IsContractible
      (PrincipalBundleLocalTrivialitySocket.BaseSpace socket)) →
  PrincipalFiber socket (IsContractible.center baseContractible) →
  ContractibleBasePrincipalBundleTrivialitySurface socket
contractibleBaseImpliesPrincipalBundleTrivialitySurface
    socket baseContractible liftAtCenter =
  record
    { sectionBasepointLift =
        canonicalSectionBasepointLift socket baseContractible liftAtCenter
    ; globalSectionConstructed =
        true
    ; globalSectionConstructed-v =
        refl
    ; contractibleBaseTrivialityShape =
        "DASHI-side-contractible-base-gives-a-global-section-witness-for-the-principal-bundle-socket"
    ; contractibleBaseTrivialityShape-v =
        refl
    ; dchottPrincipalBundleTrivialityImported =
        false
    ; dchottPrincipalBundleTrivialityImported-v =
        refl
    ; principalBundleTrivialityPromoted =
        false
    ; principalBundleTrivialityPromoted-v =
        refl
    }

unitPrincipalCenterLift :
  PrincipalFiber
    canonicalPrincipalBundleLocalTrivialitySocket
    (IsContractible.center unitContractible)
unitPrincipalCenterLift =
  tt , refl

unitCanonicalSectionBasepointLift :
  CanonicalSectionBasepointLift canonicalPrincipalBundleLocalTrivialitySocket
unitCanonicalSectionBasepointLift =
  canonicalSectionBasepointLift
    canonicalPrincipalBundleLocalTrivialitySocket
    unitContractible
    unitPrincipalCenterLift

unitContractibleBasePrincipalBundleTrivialitySurface :
  ContractibleBasePrincipalBundleTrivialitySurface
    canonicalPrincipalBundleLocalTrivialitySocket
unitContractibleBasePrincipalBundleTrivialitySurface =
  contractibleBaseImpliesPrincipalBundleTrivialitySurface
    canonicalPrincipalBundleLocalTrivialitySocket
    unitContractible
    unitPrincipalCenterLift

canonicalSO31ReductionSocket :
  {P : B0.ProObjectCarrier} →
  (frames : DepthIndexedFrameTowerSurface P) →
  (metrics : CompatibleMetricTowerSurface frames) →
  SO31ReductionSocket frames metrics
canonicalSO31ReductionSocket frames metrics =
  record
    { SignatureClass =
        CTI.Signature
    ; lorentz31 =
        Sig31.signature31
    ; signatureAtDepth =
        λ _ _ →
          Sig31.signature31
    ; signatureTowerLocked =
        λ _ _ →
          refl
    ; adapter1SignatureGate =
        "Adapter1-signature-gate-locks-compatible-metric-tower-to-Lorentz-3-plus-1"
    ; adapter1SignatureGate-v =
        refl
    ; so31ReductionShape =
        "target-only-SO31-reduction-of-frame-tower-after-Lorentz-signature-gate"
    ; so31ReductionShape-v =
        refl
    ; so31ReductionPromoted =
        false
    ; so31ReductionPromoted-v =
        refl
    }

record FrameTowerLocalTrivialitySurface
    {P : B0.ProObjectCarrier}
    (frames : DepthIndexedFrameTowerSurface P)
    : Setω where
  field
    frameAtDepthContractible :
      (d : ℕ) →
      IsContractible
        (DepthIndexedFrameTowerSurface.FrameAtDepth frames d)

    canonicalFrameAtDepth :
      (d : ℕ) →
      DepthIndexedFrameTowerSurface.FrameAtDepth frames d

    canonicalFrameAtDepth-v :
      (d : ℕ) →
      canonicalFrameAtDepth d
      ≡
      IsContractible.center (frameAtDepthContractible d)

    FramePatchAtDepth :
      (d : ℕ) →
      DepthIndexedFrameTowerSurface.FrameAtDepth frames d →
      Set

    framePatchContractible :
      (d : ℕ) →
      (f : DepthIndexedFrameTowerSurface.FrameAtDepth frames d) →
      IsContractible (FramePatchAtDepth d f)

    localFrameTrivialization :
      (d : ℕ) →
      (f : DepthIndexedFrameTowerSurface.FrameAtDepth frames d) →
      FramePatchAtDepth d f →
      DepthIndexedFrameTowerSurface.FrameAtDepth frames d →
      Set

    localFrameTrivializationAtCenter :
      (d : ℕ) →
      (f : DepthIndexedFrameTowerSurface.FrameAtDepth frames d) →
      (patch : FramePatchAtDepth d f) →
      localFrameTrivialization d f patch (canonicalFrameAtDepth d)

    frameTowerLocalTrivialityShape :
      String

    frameTowerLocalTrivialityShape-v :
      frameTowerLocalTrivialityShape
      ≡
      "contractible-frame-carriers-give-unit-local-patches-and-center-local-trivializations-at-each-depth"

    frameTowerLocalTrivialityWitnessed :
      Bool

    frameTowerLocalTrivialityWitnessed-v :
      frameTowerLocalTrivialityWitnessed ≡ true

    dchottFrameTowerLocalTrivialityImported :
      Bool

    dchottFrameTowerLocalTrivialityImported-v :
      dchottFrameTowerLocalTrivialityImported ≡ false

open FrameTowerLocalTrivialitySurface public

frameTowerLocalTrivialitySurface :
  {P : B0.ProObjectCarrier} →
  (frames : DepthIndexedFrameTowerSurface P) →
  ((d : ℕ) →
    IsContractible
      (DepthIndexedFrameTowerSurface.FrameAtDepth frames d)) →
  FrameTowerLocalTrivialitySurface frames
frameTowerLocalTrivialitySurface frames frameContr =
  record
    { frameAtDepthContractible =
        frameContr
    ; canonicalFrameAtDepth =
        λ d →
          IsContractible.center (frameContr d)
    ; canonicalFrameAtDepth-v =
        λ _ →
          refl
    ; FramePatchAtDepth =
        λ _ _ →
          ⊤
    ; framePatchContractible =
        λ _ _ →
          unitContractible
    ; localFrameTrivialization =
        λ _ _ _ _ →
          ⊤
    ; localFrameTrivializationAtCenter =
        λ _ _ _ →
          tt
    ; frameTowerLocalTrivialityShape =
        "contractible-frame-carriers-give-unit-local-patches-and-center-local-trivializations-at-each-depth"
    ; frameTowerLocalTrivialityShape-v =
        refl
    ; frameTowerLocalTrivialityWitnessed =
        true
    ; frameTowerLocalTrivialityWitnessed-v =
        refl
    ; dchottFrameTowerLocalTrivialityImported =
        false
    ; dchottFrameTowerLocalTrivialityImported-v =
        refl
    }

canonicalFrameTowerContractibilityFromCarrier :
  (P : B0.ProObjectCarrier) →
  (projection : B0.ProLimitProjectionSurface P) →
  CarrierContractibilitySurface P projection →
  (d : ℕ) →
  IsContractible
    (DepthIndexedFrameTowerSurface.FrameAtDepth
      (canonicalDepthIndexedFrameTowerSurface P projection)
      d)
canonicalFrameTowerContractibilityFromCarrier _ _ carrierContractibility d =
  CarrierContractibilitySurface.depthCarrierContractible
    carrierContractibility
    d

canonicalFrameTowerLocalTrivialityFromCarrier :
  (P : B0.ProObjectCarrier) →
  (projection : B0.ProLimitProjectionSurface P) →
  CarrierContractibilitySurface P projection →
  FrameTowerLocalTrivialitySurface
    (canonicalDepthIndexedFrameTowerSurface P projection)
canonicalFrameTowerLocalTrivialityFromCarrier P projection carrierContractibility =
  frameTowerLocalTrivialitySurface
    (canonicalDepthIndexedFrameTowerSurface P projection)
    (canonicalFrameTowerContractibilityFromCarrier
      P
      projection
      carrierContractibility)

localSignature31IsSig31 :
  Sig31.signature31
  ≡
  CTI.sig31
localSignature31IsSig31 =
  refl

data SO31FirstProlongationZeroLocalStatus : Set where
  localAbstractIndexFirstProlongationZeroProof :
    SO31FirstProlongationZeroLocalStatus

canonicalSO31FirstProlongationZeroLocalStatus :
  SO31FirstProlongationZeroLocalStatus
canonicalSO31FirstProlongationZeroLocalStatus =
  localAbstractIndexFirstProlongationZeroProof

unitPrincipalSymbol :
  Cone.PrincipalSymbol lzero
unitPrincipalSymbol =
  record
    { Covector =
        ⊤
    ; characteristic =
        λ _ →
          ⊤
    ; negativeRegion =
        λ _ →
          ⊤
    ; nullRegion =
        λ _ →
          ⊤
    ; positiveRegion =
        λ _ →
          ⊤
    }

unitConeHypotheses :
  Cone.ConeHypotheses unitPrincipalSymbol
unitConeHypotheses =
  record
    { closedCone =
        ⊤
    ; convexCone =
        ⊤
    ; symmetricCone =
        ⊤
    ; nonemptyCone =
        ⊤
    ; properCone =
        ⊤
    ; nondegenerateSymbol =
        ⊤
    ; twoNegativeComponents =
        ⊤
    }

unitLorentzianSignatureSocket :
  Cone.LorentzianSignature unitPrincipalSymbol
unitLorentzianSignatureSocket =
  record
    { oneTimelikeDirection =
        ⊤
    ; spatialHyperplane =
        ⊤
    ; coneWitness =
        ⊤
    }

constructibleTowerResidualBlockers :
  List GStructureLeviCivitaBindingBlocker
constructibleTowerResidualBlockers =
  canonicalGStructureLeviCivitaBindingBlockers

record ConstructibleFrameMetricSignatureTowerSurface
    (P : B0.ProObjectCarrier)
    (projection : B0.ProLimitProjectionSurface P)
    : Setω where
  field
    frameTower :
      DepthIndexedFrameTowerSurface P

    metricTower :
      CompatibleMetricTowerSurface frameTower

    so31Reduction :
      SO31ReductionSocket frameTower metricTower

    importedSignature31 :
      CTI.Signature

    importedSignature31-v :
      importedSignature31
      ≡
      Sig31.signature31

    importedSignature31IsSig31 :
      importedSignature31
      ≡
      CTI.sig31

    firstProlongationZeroLocalStatus :
      SO31FirstProlongationZeroLocalStatus

    firstProlongationZeroLocalStatus-v :
      firstProlongationZeroLocalStatus
      ≡
      localAbstractIndexFirstProlongationZeroProof

    firstProlongationZeroEvidence :
      SO31P.SO31FirstProlongationZeroEvidence

    principalBundleLocalTrivialitySocket :
      PrincipalBundleLocalTrivialitySocket

    weakBGCorrespondenceAuthority :
      WeakBGCorrespondenceAuthoritySurface

    principalBundleSocketRemaining :
      Bool

    principalBundleSocketRemaining-v :
      principalBundleSocketRemaining ≡ true

    localTrivialitySocketRemaining :
      Bool

    localTrivialitySocketRemaining-v :
      localTrivialitySocketRemaining ≡ true

    firstProlongationZeroTheoremName :
      String

    firstProlongationZeroTheoremName-v :
      firstProlongationZeroTheoremName
      ≡
      "so31FirstProlongationZero"

    lorentzPrincipalSymbol :
      Cone.PrincipalSymbol lzero

    lorentzPrincipalSymbol-v :
      lorentzPrincipalSymbol
      ≡
      unitPrincipalSymbol

    lorentzSignatureSocket :
      Cone.LorentzianSignature lorentzPrincipalSymbol

    residualBlockers :
      List GStructureLeviCivitaBindingBlocker

    residualBlockers-v :
      residualBlockers
      ≡
      constructibleTowerResidualBlockers

    noPromotionWithoutAuthority :
      GStructureLeviCivitaPromotionAuthorityToken →
      ⊥

open ConstructibleFrameMetricSignatureTowerSurface public

canonicalConstructibleFrameMetricSignatureTowerSurface :
  (P : B0.ProObjectCarrier) →
  (projection : B0.ProLimitProjectionSurface P) →
  ConstructibleFrameMetricSignatureTowerSurface P projection
canonicalConstructibleFrameMetricSignatureTowerSurface P projection =
  record
    { frameTower =
        canonicalDepthIndexedFrameTowerSurface P projection
    ; metricTower =
        unitCompatibleMetricTowerSurface
          (canonicalDepthIndexedFrameTowerSurface P projection)
    ; so31Reduction =
        canonicalSO31ReductionSocket
          (canonicalDepthIndexedFrameTowerSurface P projection)
          (unitCompatibleMetricTowerSurface
            (canonicalDepthIndexedFrameTowerSurface P projection))
    ; importedSignature31 =
        Sig31.signature31
    ; importedSignature31-v =
        refl
    ; importedSignature31IsSig31 =
        localSignature31IsSig31
    ; firstProlongationZeroLocalStatus =
        localAbstractIndexFirstProlongationZeroProof
    ; firstProlongationZeroLocalStatus-v =
        refl
    ; firstProlongationZeroEvidence =
        SO31P.canonicalSO31FirstProlongationZeroEvidence
    ; principalBundleLocalTrivialitySocket =
        canonicalPrincipalBundleLocalTrivialitySocket
    ; weakBGCorrespondenceAuthority =
        canonicalWeakBGCorrespondenceAuthoritySurface
    ; principalBundleSocketRemaining =
        true
    ; principalBundleSocketRemaining-v =
        refl
    ; localTrivialitySocketRemaining =
        true
    ; localTrivialitySocketRemaining-v =
        refl
    ; firstProlongationZeroTheoremName =
        "so31FirstProlongationZero"
    ; firstProlongationZeroTheoremName-v =
        refl
    ; lorentzPrincipalSymbol =
        unitPrincipalSymbol
    ; lorentzPrincipalSymbol-v =
        refl
    ; lorentzSignatureSocket =
        unitLorentzianSignatureSocket
    ; residualBlockers =
        constructibleTowerResidualBlockers
    ; residualBlockers-v =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    }

record WellenLeviCivitaTheoremSocket : Setω where
  field
    so31FirstProlongationZeroShape :
      String

    so31FirstProlongationZeroShape-v :
      so31FirstProlongationZeroShape
      ≡
      "local-abstract-index-so31-first-prolongation-zero-proof-feeds-Wellen-LeviCivita-socket"

    so31FirstProlongationZeroEvidence :
      SO31P.SO31FirstProlongationZeroEvidence

    principalBundleLocalTrivialitySocket :
      PrincipalBundleLocalTrivialitySocket

    weakBGCorrespondenceAuthority :
      WeakBGCorrespondenceAuthoritySurface

    principalBundleSocketRemaining :
      Bool

    principalBundleSocketRemaining-v :
      principalBundleSocketRemaining ≡ true

    localTrivialitySocketRemaining :
      Bool

    localTrivialitySocketRemaining-v :
      localTrivialitySocketRemaining ≡ true

    wellenTheoremAuthority :
      String

    wellenTheoremAuthority-v :
      wellenTheoremAuthority
      ≡
      "Wellen-thesis-DCHoTT-G-structure-torsion-free-Levi-Civita-theorem-authority-target"

    actualLocalImportStatus :
      String

    actualLocalImportStatus-v :
      actualLocalImportStatus
      ≡
      "local-DCHoTT-Agda-clone-exposes-G-structures-but-not-an-importable-torsion-free-Levi-Civita-theorem"

    wellenSocketDischarged :
      Bool

    wellenSocketDischarged-v :
      wellenSocketDischarged ≡ false

    leviCivitaPromoted :
      Bool

    leviCivitaPromoted-v :
      leviCivitaPromoted ≡ false

    residualBlockers :
      List GStructureLeviCivitaBindingBlocker

    residualBlockers-v :
      residualBlockers
      ≡
      canonicalGStructureLeviCivitaBindingBlockers

    firstResidualBlocker :
      GStructureLeviCivitaBindingBlocker

    firstResidualBlocker-v :
      firstResidualBlocker
      ≡
      missingActualDCHoTTGStructureBinding

open WellenLeviCivitaTheoremSocket public

canonicalWellenLeviCivitaTheoremSocket :
  WellenLeviCivitaTheoremSocket
canonicalWellenLeviCivitaTheoremSocket =
  record
    { so31FirstProlongationZeroShape =
        "local-abstract-index-so31-first-prolongation-zero-proof-feeds-Wellen-LeviCivita-socket"
    ; so31FirstProlongationZeroShape-v =
        refl
    ; so31FirstProlongationZeroEvidence =
        SO31P.canonicalSO31FirstProlongationZeroEvidence
    ; principalBundleLocalTrivialitySocket =
        canonicalPrincipalBundleLocalTrivialitySocket
    ; weakBGCorrespondenceAuthority =
        canonicalWeakBGCorrespondenceAuthoritySurface
    ; principalBundleSocketRemaining =
        true
    ; principalBundleSocketRemaining-v =
        refl
    ; localTrivialitySocketRemaining =
        true
    ; localTrivialitySocketRemaining-v =
        refl
    ; wellenTheoremAuthority =
        "Wellen-thesis-DCHoTT-G-structure-torsion-free-Levi-Civita-theorem-authority-target"
    ; wellenTheoremAuthority-v =
        refl
    ; actualLocalImportStatus =
        "local-DCHoTT-Agda-clone-exposes-G-structures-but-not-an-importable-torsion-free-Levi-Civita-theorem"
    ; actualLocalImportStatus-v =
        refl
    ; wellenSocketDischarged =
        false
    ; wellenSocketDischarged-v =
        refl
    ; leviCivitaPromoted =
        false
    ; leviCivitaPromoted-v =
        refl
    ; residualBlockers =
        canonicalGStructureLeviCivitaBindingBlockers
    ; residualBlockers-v =
        refl
    ; firstResidualBlocker =
        missingActualDCHoTTGStructureBinding
    ; firstResidualBlocker-v =
        refl
    }

record Gate3WellenBindingReadinessSurface
    {P : B0.ProObjectCarrier}
    (projection : B0.ProLimitProjectionSurface P)
    (frames : DepthIndexedFrameTowerSurface P)
    (socket : PrincipalBundleLocalTrivialitySocket)
    : Setω where
  field
    carrierContractibility :
      CarrierContractibilitySurface P projection

    sectionBasepointLiftWitness :
      CanonicalSectionBasepointLift socket

    contractibleBasePrincipalBundleTriviality :
      ContractibleBasePrincipalBundleTrivialitySurface socket

    frameTowerLocalTriviality :
      FrameTowerLocalTrivialitySurface frames

    so31FirstProlongationZeroEvidence :
      SO31P.SO31FirstProlongationZeroEvidence

    wellenSocket :
      WellenLeviCivitaTheoremSocket

    carrierContractibilityReady :
      Bool

    carrierContractibilityReady-v :
      carrierContractibilityReady ≡ true

    canonicalSectionBasepointLiftReady :
      Bool

    canonicalSectionBasepointLiftReady-v :
      canonicalSectionBasepointLiftReady ≡ true

    contractibleBasePrincipalBundleTrivialityReady :
      Bool

    contractibleBasePrincipalBundleTrivialityReady-v :
      contractibleBasePrincipalBundleTrivialityReady ≡ true

    frameTowerLocalTrivialityReady :
      Bool

    frameTowerLocalTrivialityReady-v :
      frameTowerLocalTrivialityReady ≡ true

    so31AlgebraReady :
      Bool

    so31AlgebraReady-v :
      so31AlgebraReady ≡ true

    dashiInternalGate3Readiness :
      Bool

    dashiInternalGate3Readiness-v :
      dashiInternalGate3Readiness ≡ true

    externalWellenDCHoTTAuthorityImported :
      Bool

    externalWellenDCHoTTAuthorityImported-v :
      externalWellenDCHoTTAuthorityImported ≡ false

    dchottTorsionFreeLeviCivitaTheoremImported :
      Bool

    dchottTorsionFreeLeviCivitaTheoremImported-v :
      dchottTorsionFreeLeviCivitaTheoremImported ≡ false

    wellenSocketDischarged :
      Bool

    wellenSocketDischarged-v :
      wellenSocketDischarged ≡ false

    leviCivitaPromoted :
      Bool

    leviCivitaPromoted-v :
      leviCivitaPromoted ≡ false

    readinessShape :
      String

    readinessShape-v :
      readinessShape
      ≡
      "Gate-3-DASHI-internal-witnesses-ready-while-Wellen-DCHoTT-authority-and-LeviCivita-promotion-remain-external"

open Gate3WellenBindingReadinessSurface public

gate3WellenBindingReadinessSurface :
  {P : B0.ProObjectCarrier} →
  (projection : B0.ProLimitProjectionSurface P) →
  (frames : DepthIndexedFrameTowerSurface P) →
  (socket : PrincipalBundleLocalTrivialitySocket) →
  CarrierContractibilitySurface P projection →
  CanonicalSectionBasepointLift socket →
  ContractibleBasePrincipalBundleTrivialitySurface socket →
  FrameTowerLocalTrivialitySurface frames →
  Gate3WellenBindingReadinessSurface projection frames socket
gate3WellenBindingReadinessSurface
    projection frames socket carrier sectionLift principalTriviality frameLocal =
  record
    { carrierContractibility =
        carrier
    ; sectionBasepointLiftWitness =
        sectionLift
    ; contractibleBasePrincipalBundleTriviality =
        principalTriviality
    ; frameTowerLocalTriviality =
        frameLocal
    ; so31FirstProlongationZeroEvidence =
        SO31P.canonicalSO31FirstProlongationZeroEvidence
    ; wellenSocket =
        canonicalWellenLeviCivitaTheoremSocket
    ; carrierContractibilityReady =
        true
    ; carrierContractibilityReady-v =
        refl
    ; canonicalSectionBasepointLiftReady =
        true
    ; canonicalSectionBasepointLiftReady-v =
        refl
    ; contractibleBasePrincipalBundleTrivialityReady =
        true
    ; contractibleBasePrincipalBundleTrivialityReady-v =
        refl
    ; frameTowerLocalTrivialityReady =
        true
    ; frameTowerLocalTrivialityReady-v =
        refl
    ; so31AlgebraReady =
        true
    ; so31AlgebraReady-v =
        refl
    ; dashiInternalGate3Readiness =
        true
    ; dashiInternalGate3Readiness-v =
        refl
    ; externalWellenDCHoTTAuthorityImported =
        false
    ; externalWellenDCHoTTAuthorityImported-v =
        refl
    ; dchottTorsionFreeLeviCivitaTheoremImported =
        false
    ; dchottTorsionFreeLeviCivitaTheoremImported-v =
        refl
    ; wellenSocketDischarged =
        false
    ; wellenSocketDischarged-v =
        refl
    ; leviCivitaPromoted =
        false
    ; leviCivitaPromoted-v =
        refl
    ; readinessShape =
        "Gate-3-DASHI-internal-witnesses-ready-while-Wellen-DCHoTT-authority-and-LeviCivita-promotion-remain-external"
    ; readinessShape-v =
        refl
    }

gate3ReadinessFromCanonicalFrameCarrierContractibility :
  (P : B0.ProObjectCarrier) →
  (projection : B0.ProLimitProjectionSurface P) →
  CarrierContractibilitySurface P projection →
  Gate3WellenBindingReadinessSurface
    projection
    (canonicalDepthIndexedFrameTowerSurface P projection)
    canonicalPrincipalBundleLocalTrivialitySocket
gate3ReadinessFromCanonicalFrameCarrierContractibility
    P projection carrierContractibility =
  gate3WellenBindingReadinessSurface
    projection
    (canonicalDepthIndexedFrameTowerSurface P projection)
    canonicalPrincipalBundleLocalTrivialitySocket
    carrierContractibility
    unitCanonicalSectionBasepointLift
    unitContractibleBasePrincipalBundleTrivialitySurface
    (canonicalFrameTowerLocalTrivialityFromCarrier
      P
      projection
      carrierContractibility)

record GStructureLeviCivitaBindingSurface
    (P : B0.ProObjectCarrier)
    : Setω where
  field
    frameTower :
      DepthIndexedFrameTowerSurface P

    metricTower :
      CompatibleMetricTowerSurface frameTower

    so31Reduction :
      SO31ReductionSocket frameTower metricTower

    wellenSocket :
      WellenLeviCivitaTheoremSocket

    principalBundleLocalTrivialitySocket :
      PrincipalBundleLocalTrivialitySocket

    weakBGCorrespondenceAuthority :
      WeakBGCorrespondenceAuthoritySurface

    bindingTargetShape :
      String

    bindingTargetShape-v :
      bindingTargetShape
      ≡
      "B0-3-bind-depth-indexed-frame-and-metric-tower-to-SO31-G-structure-then-Wellen-LeviCivita-socket"

    blockers :
      List GStructureLeviCivitaBindingBlocker

    blockersAreCanonical :
      blockers
      ≡
      canonicalGStructureLeviCivitaBindingBlockers

    firstResidualBlocker :
      GStructureLeviCivitaBindingBlocker

    firstResidualBlocker-v :
      firstResidualBlocker
      ≡
      missingActualDCHoTTGStructureBinding

    b03ClosedModuloWeakBGAuthority :
      Bool

    b03ClosedModuloWeakBGAuthority-v :
      b03ClosedModuloWeakBGAuthority ≡ true

    weakBGCubicalHITBlocked :
      Bool

    weakBGCubicalHITBlocked-v :
      weakBGCubicalHITBlocked ≡ true

    leviCivitaPromoted :
      Bool

    leviCivitaPromoted-v :
      leviCivitaPromoted ≡ false

open GStructureLeviCivitaBindingSurface public

record CanonicalGStructureLeviCivitaBindingReceipt : Setω where
  field
    status :
      GStructureLeviCivitaBindingStatus

    frameTowerMaps :
      String

    frameTowerMaps-v :
      frameTowerMaps
      ≡
      "FrameAtDepth-d-frameProjectionMap-d-frameOfCarrier-d-proFrameProjection-d"

    metricTowerCompatibility :
      String

    metricTowerCompatibility-v :
      metricTowerCompatibility
      ≡
      "metricProjectionMap-d-metricAtFrame-suc-d-f-equals-metricAtFrame-d-frameProjectionMap-d-f"

    adapter1SignatureGate :
      String

    adapter1SignatureGate-v :
      adapter1SignatureGate
      ≡
      "Adapter1-signature-gate-locks-compatible-metric-tower-to-Lorentz-3-plus-1"

    so31ReductionShape :
      String

    so31ReductionShape-v :
      so31ReductionShape
      ≡
      "target-only-SO31-reduction-of-frame-tower-after-Lorentz-signature-gate"

    so31FirstProlongationZeroShape :
      String

    so31FirstProlongationZeroShape-v :
      so31FirstProlongationZeroShape
      ≡
      "local-abstract-index-so31-first-prolongation-zero-proof-feeds-Wellen-LeviCivita-socket"

    so31FirstProlongationZeroEvidence :
      SO31P.SO31FirstProlongationZeroEvidence

    principalBundleLocalTrivialitySocket :
      PrincipalBundleLocalTrivialitySocket

    weakBGCorrespondenceAuthority :
      WeakBGCorrespondenceAuthoritySurface

    weakBGCorrespondenceAuthorityShape :
      String

    weakBGCorrespondenceAuthorityShape-v :
      weakBGCorrespondenceAuthorityShape
      ≡
      "WeakBGCorrespondence-authority-shape-for-SO31-torsors-to-principal-bundles"

    cubicalHITBlocker :
      String

    cubicalHITBlocker-v :
      cubicalHITBlocker
      ≡
      "blocked-until-cubical-HIT-BG-classifying-stack-and-torsor-principal-bundle-equivalence-are-imported"

    principalBundleSocketRemaining :
      Bool

    principalBundleSocketRemaining-v :
      principalBundleSocketRemaining ≡ true

    localTrivialitySocketRemaining :
      Bool

    localTrivialitySocketRemaining-v :
      localTrivialitySocketRemaining ≡ true

    wellenTheoremAuthority :
      String

    wellenTheoremAuthority-v :
      wellenTheoremAuthority
      ≡
      "Wellen-thesis-DCHoTT-G-structure-torsion-free-Levi-Civita-theorem-authority-target"

    wellenSocket :
      WellenLeviCivitaTheoremSocket

    blockers :
      List GStructureLeviCivitaBindingBlocker

    blockersAreCanonical :
      blockers
      ≡
      canonicalGStructureLeviCivitaBindingBlockers

    firstResidualBlocker :
      GStructureLeviCivitaBindingBlocker

    firstResidualBlocker-v :
      firstResidualBlocker
      ≡
      missingActualDCHoTTGStructureBinding

    so31ReductionPromoted :
      Bool

    so31ReductionPromoted-v :
      so31ReductionPromoted ≡ false

    b03ClosedModuloWeakBGAuthority :
      Bool

    b03ClosedModuloWeakBGAuthority-v :
      b03ClosedModuloWeakBGAuthority ≡ true

    weakBGCubicalHITBlocked :
      Bool

    weakBGCubicalHITBlocked-v :
      weakBGCubicalHITBlocked ≡ true

    wellenSocketDischarged :
      Bool

    wellenSocketDischarged-v :
      wellenSocketDischarged ≡ false

    leviCivitaPromoted :
      Bool

    leviCivitaPromoted-v :
      leviCivitaPromoted ≡ false

    noPromotionWithoutAuthority :
      GStructureLeviCivitaPromotionAuthorityToken →
      ⊥

    bindingBoundary :
      List String

open CanonicalGStructureLeviCivitaBindingReceipt public

canonicalGStructureLeviCivitaBindingReceipt :
  CanonicalGStructureLeviCivitaBindingReceipt
canonicalGStructureLeviCivitaBindingReceipt =
  record
    { status =
        gStructureLeviCivitaBindingTargetsOnlyNoPromotion
    ; frameTowerMaps =
        "FrameAtDepth-d-frameProjectionMap-d-frameOfCarrier-d-proFrameProjection-d"
    ; frameTowerMaps-v =
        refl
    ; metricTowerCompatibility =
        "metricProjectionMap-d-metricAtFrame-suc-d-f-equals-metricAtFrame-d-frameProjectionMap-d-f"
    ; metricTowerCompatibility-v =
        refl
    ; adapter1SignatureGate =
        "Adapter1-signature-gate-locks-compatible-metric-tower-to-Lorentz-3-plus-1"
    ; adapter1SignatureGate-v =
        refl
    ; so31ReductionShape =
        "target-only-SO31-reduction-of-frame-tower-after-Lorentz-signature-gate"
    ; so31ReductionShape-v =
        refl
    ; so31FirstProlongationZeroShape =
        "local-abstract-index-so31-first-prolongation-zero-proof-feeds-Wellen-LeviCivita-socket"
    ; so31FirstProlongationZeroShape-v =
        refl
    ; so31FirstProlongationZeroEvidence =
        SO31P.canonicalSO31FirstProlongationZeroEvidence
    ; principalBundleLocalTrivialitySocket =
        canonicalPrincipalBundleLocalTrivialitySocket
    ; weakBGCorrespondenceAuthority =
        canonicalWeakBGCorrespondenceAuthoritySurface
    ; weakBGCorrespondenceAuthorityShape =
        "WeakBGCorrespondence-authority-shape-for-SO31-torsors-to-principal-bundles"
    ; weakBGCorrespondenceAuthorityShape-v =
        refl
    ; cubicalHITBlocker =
        "blocked-until-cubical-HIT-BG-classifying-stack-and-torsor-principal-bundle-equivalence-are-imported"
    ; cubicalHITBlocker-v =
        refl
    ; principalBundleSocketRemaining =
        true
    ; principalBundleSocketRemaining-v =
        refl
    ; localTrivialitySocketRemaining =
        true
    ; localTrivialitySocketRemaining-v =
        refl
    ; wellenTheoremAuthority =
        "Wellen-thesis-DCHoTT-G-structure-torsion-free-Levi-Civita-theorem-authority-target"
    ; wellenTheoremAuthority-v =
        refl
    ; wellenSocket =
        canonicalWellenLeviCivitaTheoremSocket
    ; blockers =
        canonicalGStructureLeviCivitaBindingBlockers
    ; blockersAreCanonical =
        refl
    ; firstResidualBlocker =
        missingActualDCHoTTGStructureBinding
    ; firstResidualBlocker-v =
        refl
    ; so31ReductionPromoted =
        false
    ; so31ReductionPromoted-v =
        refl
    ; b03ClosedModuloWeakBGAuthority =
        true
    ; b03ClosedModuloWeakBGAuthority-v =
        refl
    ; weakBGCubicalHITBlocked =
        true
    ; weakBGCubicalHITBlocked-v =
        refl
    ; wellenSocketDischarged =
        false
    ; wellenSocketDischarged-v =
        refl
    ; leviCivitaPromoted =
        false
    ; leviCivitaPromoted-v =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; bindingBoundary =
        "B0.3 records a target-only depth-indexed frame bundle and compatible metric tower"
        ∷ "Adapter 1 signature gate must lock the tower to Lorentz 3-plus-1 before SO(3,1) reduction can be used"
        ∷ "SO(3,1) reduction is a socket and so31ReductionPromoted remains false"
        ∷ "first-prolongation-zero is discharged locally by DASHI.Geometry.SO31FirstProlongationZero.so31FirstProlongationZero over abstract lowered coefficients"
        ∷ "PrincipalBundle and local-triviality atlas inputs are explicit remaining sockets and are not constructed here"
        ∷ "WeakBGCorrespondence records SO31 torsor fibres, free/transitive action targets, and torsor-to-principal-bundle binding targets"
        ∷ "B0.3 can be considered closed only modulo the weak BG authority surface; cubical/HIT BG construction remains an explicit blocker"
        ∷ "the residual blocker list now starts at missingActualDCHoTTGStructureBinding"
        ∷ "Wellen theorem authority is recorded as an external/socket target because the local DCHoTT clone does not expose an importable torsion-free Levi-Civita theorem"
        ∷ "wellenSocketDischarged and leviCivitaPromoted remain false"
        ∷ []
    }

canonicalLeviCivitaNotPromoted :
  CanonicalGStructureLeviCivitaBindingReceipt.leviCivitaPromoted
    canonicalGStructureLeviCivitaBindingReceipt
  ≡
  false
canonicalLeviCivitaNotPromoted =
  refl
