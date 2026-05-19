module DASHI.Geometry.TransportSmoothFormalDiskSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (ℕ; zero; suc)

import Basics as DCHoTTBasics
import DASHI.Geometry.DCHoTTBridgeObligationIndex as B0
import DASHI.Geometry.DCHoTTImportShim as DCHoTT
import DASHI.Geometry.ProObjectSemantics as Sem

------------------------------------------------------------------------
-- Transport-smooth formal-disk surface.
--
-- This module is a proof-grade DASHI-side analytic scaffold over the B0.1
-- pro-object semantics.  It constructs clopen depth balls, transport-smooth
-- function records, sheaf-style locality/gluing sockets, first-order and
-- tangent/graded-piece targets.  It deliberately does not prove a real
-- analytic completion theorem, a full sheaf theorem, a dual-numbers theorem,
-- a DCHoTT formal-disk equivalence, or B0.

data TransportSmoothOpenObligation : Set where
  missingRealAnalyticCompletion :
    TransportSmoothOpenObligation

  missingFullSheafTheorem :
    TransportSmoothOpenObligation

  missingFirstOrderApproximationProof :
    TransportSmoothOpenObligation

  missingDualNumbersEquivalence :
    TransportSmoothOpenObligation

  missingDCHoTTFormalDiskEquivalence :
    TransportSmoothOpenObligation

  missingUnconditionalReverseLiftFromImportedImReflection :
    TransportSmoothOpenObligation

  missingImModalQuotientEqualityReflection :
    TransportSmoothOpenObligation

  missingImReflectDASHICohesionAuthority :
    TransportSmoothOpenObligation

canonicalTransportSmoothOpenObligations :
  List TransportSmoothOpenObligation
canonicalTransportSmoothOpenObligations =
  missingRealAnalyticCompletion
  ∷ missingFullSheafTheorem
  ∷ missingFirstOrderApproximationProof
  ∷ missingDualNumbersEquivalence
  ∷ missingDCHoTTFormalDiskEquivalence
  ∷ missingUnconditionalReverseLiftFromImportedImReflection
  ∷ missingImModalQuotientEqualityReflection
  ∷ missingImReflectDASHICohesionAuthority
  ∷ []

data ImReflectDASHIPostulateStatus : Set where
  safePostulateSurfaceBlockedByCohesion :
    ImReflectDASHIPostulateStatus

record ImReflectDASHIAuthorityPostulateSurface
    (Carrier : Set)
    (depthZeroAgreement : Carrier → Carrier → Set)
    (depthOneAgreement : Carrier → Carrier → Set)
    (imModalAgreement : Carrier → Carrier → Set)
    : Set₁ where
  field
    FormalEtaleProObject :
      Set

    formalEtalePoint :
      FormalEtaleProObject →
      Carrier

    formalEtaleRelation :
      FormalEtaleProObject →
      FormalEtaleProObject →
      Set

    formalEtaleRelationReflectsIm :
      (u v : FormalEtaleProObject) →
      formalEtaleRelation u v →
      imModalAgreement (formalEtalePoint u) (formalEtalePoint v)

    Im-reflect-DASHI :
      Set

    Im-reflect-DASHI-v :
      Im-reflect-DASHI
      ≡
      ((x y : Carrier) →
        imModalAgreement x y →
        depthZeroAgreement x y)

    depthZeroAgreementReflection :
      (x y : Carrier) →
      imModalAgreement x y →
      depthZeroAgreement x y

    depthOneAgreementReflectionTarget :
      Set

    depthOneAgreementReflectionTarget-v :
      depthOneAgreementReflectionTarget
      ≡
      ((x y : Carrier) →
        imModalAgreement x y →
        depthOneAgreement x y)

    depthOneAgreementReflection :
      (x y : Carrier) →
      imModalAgreement x y →
      depthOneAgreement x y

    postulateStatus :
      ImReflectDASHIPostulateStatus

    postulateStatus-v :
      postulateStatus
      ≡
      safePostulateSurfaceBlockedByCohesion

    safePostulateStatus :
      String

    safePostulateStatus-v :
      safePostulateStatus
      ≡
      "safe-postulate-surface-over-local-Set-and-relation-placeholders"

    blockedByCohesion :
      Bool

    blockedByCohesion-v :
      blockedByCohesion
      ≡
      true

    authorityImported :
      Bool

    authorityImported-v :
      authorityImported
      ≡
      false

    b01ClosureModuloAuthorityOnly :
      Bool

    b01ClosureModuloAuthorityOnly-v :
      b01ClosureModuloAuthorityOnly
      ≡
      true

    noConstructiveDCHoTTProofClaimed :
      Bool

    noConstructiveDCHoTTProofClaimed-v :
      noConstructiveDCHoTTProofClaimed
      ≡
      true

    canonicalReceipt :
      String

    canonicalReceipt-v :
      canonicalReceipt
      ≡
      "ImReflectDASHI-authority-surface-records-formal-etale-pro-object-and-depth-0-depth-1-reflection-only-modulo-cohesion"

open ImReflectDASHIAuthorityPostulateSurface public

canonicalImReflectDASHIAuthorityPostulateSurface :
  ImReflectDASHIAuthorityPostulateSurface
    ⊤
    (λ _ _ → ⊤)
    (λ _ _ → ⊤)
    (λ _ _ → ⊤)
canonicalImReflectDASHIAuthorityPostulateSurface =
  record
    { FormalEtaleProObject =
        ⊤
    ; formalEtalePoint =
        λ _ →
          tt
    ; formalEtaleRelation =
        λ _ _ →
          ⊤
    ; formalEtaleRelationReflectsIm =
        λ _ _ _ →
          tt
    ; Im-reflect-DASHI =
        (x y : ⊤) →
        ⊤ →
        ⊤
    ; Im-reflect-DASHI-v =
        refl
    ; depthZeroAgreementReflection =
        λ _ _ _ →
          tt
    ; depthOneAgreementReflectionTarget =
        (x y : ⊤) →
        ⊤ →
        ⊤
    ; depthOneAgreementReflectionTarget-v =
        refl
    ; depthOneAgreementReflection =
        λ _ _ _ →
          tt
    ; postulateStatus =
        safePostulateSurfaceBlockedByCohesion
    ; postulateStatus-v =
        refl
    ; safePostulateStatus =
        "safe-postulate-surface-over-local-Set-and-relation-placeholders"
    ; safePostulateStatus-v =
        refl
    ; blockedByCohesion =
        true
    ; blockedByCohesion-v =
        refl
    ; authorityImported =
        false
    ; authorityImported-v =
        refl
    ; b01ClosureModuloAuthorityOnly =
        true
    ; b01ClosureModuloAuthorityOnly-v =
        refl
    ; noConstructiveDCHoTTProofClaimed =
        true
    ; noConstructiveDCHoTTProofClaimed-v =
        refl
    ; canonicalReceipt =
        "ImReflectDASHI-authority-surface-records-formal-etale-pro-object-and-depth-0-depth-1-reflection-only-modulo-cohesion"
    ; canonicalReceipt-v =
        refl
    }

data TransportSmoothLabel : Set where
  TS1-clopen-locality :
    TransportSmoothLabel

  TS2-refinement-naturality :
    TransportSmoothLabel

  TS3-formal-disk-stability :
    TransportSmoothLabel

  TS4-transport-compatibility :
    TransportSmoothLabel

canonicalTransportSmoothLabels :
  List TransportSmoothLabel
canonicalTransportSmoothLabels =
  TS1-clopen-locality
  ∷ TS2-refinement-naturality
  ∷ TS3-formal-disk-stability
  ∷ TS4-transport-compatibility
  ∷ []

record ClopenBall
  (P : B0.ProObjectCarrier) :
  Set₁ where
  field
    center :
      B0.ProObjectPoint P

    depth :
      ℕ

    contains :
      B0.ProObjectPoint P →
      Set

    containsIsDepthBall :
      (y : B0.ProObjectPoint P) →
      contains y
      ≡
      Sem.BallAtDepth center depth y

open ClopenBall public

canonicalClopenBall :
  {P : B0.ProObjectCarrier} →
  B0.ProObjectPoint P →
  ℕ →
  ClopenBall P
canonicalClopenBall x d =
  record
    { center =
        x
    ; depth =
        d
    ; contains =
        Sem.BallAtDepth x d
    ; containsIsDepthBall =
        λ _ →
          refl
    }

record ClopenBallSite
  (P : B0.ProObjectCarrier) :
  Set₁ where
  field
    Ball :
      B0.ProObjectPoint P →
      ℕ →
      B0.ProObjectPoint P →
      Set

    BallIsB01BallAtDepth :
      (x y : B0.ProObjectPoint P) →
      (d : ℕ) →
      Ball x d y
      ≡
      Sem.BallAtDepth x d y

    ballReflexive :
      (x : B0.ProObjectPoint P) →
      (d : ℕ) →
      Ball x d x

    ballSymmetric :
      (x y : B0.ProObjectPoint P) →
      (d : ℕ) →
      Ball x d y →
      Ball y d x

    ballTransitive :
      (x y z : B0.ProObjectPoint P) →
      (d : ℕ) →
      Ball x d y →
      Ball y d z →
      Ball x d z

    canonicalPartitionAtDepth :
      ℕ →
      Set

    canonicalPartitionAtDepthIsDepthCarrier :
      (d : ℕ) →
      canonicalPartitionAtDepth d
      ≡
      B0.ProObjectCarrier.depthCarrier P d

    partitionCellOf :
      (d : ℕ) →
      B0.ProObjectPoint P →
      B0.ProObjectCarrier.depthCarrier P d

    partitionCellOfIsProjection :
      (d : ℕ) →
      (x : B0.ProObjectPoint P) →
      partitionCellOf d x
      ≡
      B0.ProObjectPoint.point x d

    siteStatus :
      String

    siteStatus-v :
      siteStatus
      ≡
      "DASHI-side-clopen-ball-site-from-depth-agreement-and-canonical-depth-partitions"

open ClopenBallSite public

canonicalClopenBallSite :
  (P : B0.ProObjectCarrier) →
  ClopenBallSite P
canonicalClopenBallSite P =
  record
    { Ball =
        Sem.BallAtDepth
    ; BallIsB01BallAtDepth =
        λ _ _ _ →
          refl
    ; ballReflexive =
        Sem.ballAtDepthRefl
    ; ballSymmetric =
        Sem.ballAtDepthSym
    ; ballTransitive =
        Sem.ballAtDepthStrongTriangleShadow
    ; canonicalPartitionAtDepth =
        B0.ProObjectCarrier.depthCarrier P
    ; canonicalPartitionAtDepthIsDepthCarrier =
        λ _ →
          refl
    ; partitionCellOf =
        λ d x →
          B0.ProObjectPoint.point x d
    ; partitionCellOfIsProjection =
        λ _ _ →
          refl
    ; siteStatus =
        "DASHI-side-clopen-ball-site-from-depth-agreement-and-canonical-depth-partitions"
    ; siteStatus-v =
        refl
    }

terminalSectionEq :
  (x y : ⊤) →
  x
  ≡
  y
terminalSectionEq tt tt =
  refl

record CanonicalDepthPartitionLawSurface
  (P : B0.ProObjectCarrier) :
  Set₁ where
  field
    site :
      ClopenBallSite P

    CellAtDepth :
      ℕ →
      Set

    CellAtDepth-v :
      (d : ℕ) →
      CellAtDepth d
      ≡
      B0.ProObjectCarrier.depthCarrier P d

    cellOf :
      (d : ℕ) →
      B0.ProObjectPoint P →
      B0.ProObjectCarrier.depthCarrier P d

    cellOf-v :
      (d : ℕ) →
      (x : B0.ProObjectPoint P) →
      cellOf d x
      ≡
      B0.ProObjectPoint.point x d

    sameCell :
      (d : ℕ) →
      B0.ProObjectPoint P →
      B0.ProObjectPoint P →
      Set

    sameCellIsBall :
      (d : ℕ) →
      (x y : B0.ProObjectPoint P) →
      sameCell d x y
      ≡
      ClopenBallSite.Ball site x d y

    sameCellRefl :
      (d : ℕ) →
      (x : B0.ProObjectPoint P) →
      sameCell d x x

    sameCellSym :
      (d : ℕ) →
      (x y : B0.ProObjectPoint P) →
      sameCell d x y →
      sameCell d y x

    sameCellTrans :
      (d : ℕ) →
      (x y z : B0.ProObjectPoint P) →
      sameCell d x y →
      sameCell d y z →
      sameCell d x z

    refinementRestrictsCell :
      (d : ℕ) →
      B0.ProObjectCarrier.depthCarrier P (suc d) →
      B0.ProObjectCarrier.depthCarrier P d

    refinementRestrictsCell-v :
      (d : ℕ) →
      (cell : B0.ProObjectCarrier.depthCarrier P (suc d)) →
      refinementRestrictsCell d cell
      ≡
      B0.ProObjectCarrier.refinementMap P d cell

    pointCellRefinementCoherent :
      (d : ℕ) →
      (x : B0.ProObjectPoint P) →
      refinementRestrictsCell d (cellOf (suc d) x)
      ≡
      cellOf d x

open CanonicalDepthPartitionLawSurface public

canonicalDepthPartitionLawSurface :
  (P : B0.ProObjectCarrier) →
  CanonicalDepthPartitionLawSurface P
canonicalDepthPartitionLawSurface P =
  record
    { site =
        canonicalClopenBallSite P
    ; CellAtDepth =
        B0.ProObjectCarrier.depthCarrier P
    ; CellAtDepth-v =
        λ _ →
          refl
    ; cellOf =
        λ d x →
          B0.ProObjectPoint.point x d
    ; cellOf-v =
        λ _ _ →
          refl
    ; sameCell =
        λ d x y →
          B0.ProObjectPoint.point x d
          ≡
          B0.ProObjectPoint.point y d
    ; sameCellIsBall =
        λ _ _ _ →
          refl
    ; sameCellRefl =
        λ _ _ →
          refl
    ; sameCellSym =
        λ d x y →
          Sem.depthAgreementSym d x y
    ; sameCellTrans =
        λ d x y z →
          Sem.depthAgreementTrans d x y z
    ; refinementRestrictsCell =
        B0.ProObjectCarrier.refinementMap P
    ; refinementRestrictsCell-v =
        λ _ _ →
          refl
    ; pointCellRefinementCoherent =
        λ d x →
          B0.ProObjectPoint.coherence x d
    }

record CanonicalBallRestrictionSurface
  (P : B0.ProObjectCarrier) :
  Setω where
  field
    site :
      ClopenBallSite P

    restrictOneDepth :
      (d : ℕ) →
      (x y : B0.ProObjectPoint P) →
      Sem.BallAtDepth x (suc d) y →
      Sem.BallAtDepth x d y

    restrictOneDepth-v :
      (d : ℕ) →
      (x y : B0.ProObjectPoint P) →
      (xy : Sem.BallAtDepth x (suc d) y) →
      restrictOneDepth d x y xy
      ≡
      Sem.depthAgreementSucToDepth d x y xy

    formalDiskEquivalence :
      (x : B0.ProObjectPoint P) →
      Sem.FormalDiskDepthZeroBallEquivalence x

    formalDiskPointBall :
      (x : B0.ProObjectPoint P) →
      (disk : B0.FormalDisk x) →
      Sem.BallAtDepth x zero (Sem.formalDiskPoint {x = x} disk)

    depthZeroBallToFormalDisk :
      (x y : B0.ProObjectPoint P) →
      Sem.BallAtDepth x zero y →
      B0.FormalDisk x

open CanonicalBallRestrictionSurface public

canonicalBallRestrictionSurface :
  (P : B0.ProObjectCarrier) →
  CanonicalBallRestrictionSurface P
canonicalBallRestrictionSurface P =
  record
    { site =
        canonicalClopenBallSite P
    ; restrictOneDepth =
        Sem.ballAtDepthRestrictStep
    ; restrictOneDepth-v =
        λ _ _ _ _ →
          refl
    ; formalDiskEquivalence =
        λ x →
          Sem.canonicalFormalDiskDepthZeroBallEquivalence x
    ; formalDiskPointBall =
        λ x disk →
          Sem.formalDiskPointIsDepthZeroClose {x = x} disk
    ; depthZeroBallToFormalDisk =
        λ _ y close →
          y , close
    }

record TransportSmoothFunction
  {P : B0.ProObjectCarrier}
  (x : B0.ProObjectPoint P)
  (Value : Set₁) :
  Setω where
  field
    eval :
      B0.FormalDisk x →
      Value

    localDepth :
      ℕ

    TS1-locality :
      String

    TS1-locality-v :
      TS1-locality
      ≡
      "TS1-locality-on-clopen-depth-balls"

    TS2-refinement :
      String

    TS2-refinement-v :
      TS2-refinement
      ≡
      "TS2-compatible-with-refinement-projections"

    TS3-formalDisk :
      String

    TS3-formalDisk-v :
      TS3-formalDisk
      ≡
      "TS3-stable-on-the-formal-disk-over-depth-zero"

    TS4-transport :
      String

    TS4-transport-v :
      TS4-transport
      ≡
      "TS4-transport-compatible-across-compatible-families"

    labels :
      List TransportSmoothLabel

    labelsAreCanonical :
      labels
      ≡
      canonicalTransportSmoothLabels

open TransportSmoothFunction public

canonicalTransportSmoothFunction :
  {P : B0.ProObjectCarrier} →
  (x : B0.ProObjectPoint P) →
  TransportSmoothFunction x (B0.FormalDisk x)
canonicalTransportSmoothFunction x =
  record
    { eval =
        λ disk →
          disk
    ; localDepth =
        zero
    ; TS1-locality =
        "TS1-locality-on-clopen-depth-balls"
    ; TS1-locality-v =
        refl
    ; TS2-refinement =
        "TS2-compatible-with-refinement-projections"
    ; TS2-refinement-v =
        refl
    ; TS3-formalDisk =
        "TS3-stable-on-the-formal-disk-over-depth-zero"
    ; TS3-formalDisk-v =
        refl
    ; TS4-transport =
        "TS4-transport-compatible-across-compatible-families"
    ; TS4-transport-v =
        refl
    ; labels =
        canonicalTransportSmoothLabels
    ; labelsAreCanonical =
        refl
    }

record SheafLocalitySurface
  (P : B0.ProObjectCarrier) :
  Set₁ where
  field
    site :
      ClopenBallSite P

    Section :
      ClopenBall P →
      Set

    restriction :
      (large small : ClopenBall P) →
      Section large →
      Section small

    restrictionIdentity :
      (ball : ClopenBall P) →
      (section : Section ball) →
      restriction ball ball section
      ≡
      section

    localityLaw :
      (ball : ClopenBall P) →
      Section ball →
      Section ball →
      Set

    localityWitness :
      (ball : ClopenBall P) →
      (left right : Section ball) →
      localityLaw ball left right

    localityLabel :
      String

    localityLabel-v :
      localityLabel
      ≡
      "DASHI-side-sheaf-locality-inhabited-for-recorded-section-surface"

    localityProvedHere :
      Bool

    localityProvedHere-v :
      localityProvedHere
      ≡
      true

open SheafLocalitySurface public

canonicalTerminalSheafLocalitySurface :
  (P : B0.ProObjectCarrier) →
  SheafLocalitySurface P
canonicalTerminalSheafLocalitySurface P =
  record
    { site =
        canonicalClopenBallSite P
    ; Section =
        λ _ →
          ⊤
    ; restriction =
        λ _ _ _ →
          tt
    ; restrictionIdentity =
        λ _ section →
          terminalSectionEq tt section
    ; localityLaw =
        λ _ left right →
          left ≡ right
    ; localityWitness =
        λ _ left right →
          terminalSectionEq left right
    ; localityLabel =
        "DASHI-side-sheaf-locality-inhabited-for-recorded-section-surface"
    ; localityLabel-v =
        refl
    ; localityProvedHere =
        true
    ; localityProvedHere-v =
        refl
    }

record SheafGluingSurface
  (P : B0.ProObjectCarrier) :
  Set₁ where
  field
    site :
      ClopenBallSite P

    Section :
      ClopenBall P →
      Set

    CompatibleFamily :
      (cover : List (ClopenBall P)) →
      Set

    gluedSectionTarget :
      (ball : ClopenBall P) →
      List (ClopenBall P) →
      CompatibleFamily (ball ∷ []) →
      Set

    gluingWitness :
      (ball : ClopenBall P) →
      (family : CompatibleFamily (ball ∷ [])) →
      gluedSectionTarget ball (ball ∷ []) family

    gluingLabel :
      String

    gluingLabel-v :
      gluingLabel
      ≡
      "DASHI-side-singleton-terminal-sheaf-gluing-inhabited-on-clopen-site"

    gluingProvedHere :
      Bool

    gluingProvedHere-v :
      gluingProvedHere
      ≡
      true

open SheafGluingSurface public

canonicalTerminalSheafGluingSurface :
  (P : B0.ProObjectCarrier) →
  SheafGluingSurface P
canonicalTerminalSheafGluingSurface P =
  record
    { site =
        canonicalClopenBallSite P
    ; Section =
        λ _ →
          ⊤
    ; CompatibleFamily =
        λ _ →
          ⊤
    ; gluedSectionTarget =
        λ _ _ _ →
          ⊤
    ; gluingWitness =
        λ _ _ →
          tt
    ; gluingLabel =
        "DASHI-side-singleton-terminal-sheaf-gluing-inhabited-on-clopen-site"
    ; gluingLabel-v =
        refl
    ; gluingProvedHere =
        true
    ; gluingProvedHere-v =
        refl
    }

record ProductRuleSurface
  {P : B0.ProObjectCarrier}
  (x : B0.ProObjectPoint P) :
  Setω where
  field
    Value :
      Set₁

    product :
      Value →
      Value →
      Value

    derivativeTarget :
      TransportSmoothFunction x Value →
      TransportSmoothFunction x Value →
      Set

    productRuleLabel :
      String

    productRuleLabel-v :
      productRuleLabel
      ≡
      "target-only-product-rule-for-transport-smooth-functions"

    productRuleProvedHere :
      Bool

    productRuleProvedHere-v :
      productRuleProvedHere
      ≡
      false

open ProductRuleSurface public

record FirstOrderApproximationSurface
  {P : B0.ProObjectCarrier}
  (x : B0.ProObjectPoint P) :
  Set₁ where
  field
    TangentVector :
      Set

    firstOrderJet :
      B0.FormalDisk x →
      TangentVector →
      Set

    approximationLabel :
      String

    approximationLabel-v :
      approximationLabel
      ≡
      "target-only-first-order-approximation-on-DASHI-formal-disk"

    firstOrderApproximationProved :
      Bool

    firstOrderApproximationProved-v :
      firstOrderApproximationProved
      ≡
      false

open FirstOrderApproximationSurface public

record FormalDiskDualNumbersComparison
  {P : B0.ProObjectCarrier}
  (x : B0.ProObjectPoint P) :
  Setω where
  field
    DualNumberDisk :
      Set

    dashiFormalDisk :
      Set₁

    dashiFormalDisk-v :
      dashiFormalDisk
      ≡
      B0.FormalDisk x

    comparisonTarget :
      dashiFormalDisk →
      DualNumberDisk →
      Set

    comparisonLabel :
      String

    comparisonLabel-v :
      comparisonLabel
      ≡
      "target-only-DASHI-formal-disk-compared-with-dual-number-first-order-disk"

    dualNumbersEquivalenceProved :
      Bool

    dualNumbersEquivalenceProved-v :
      dualNumbersEquivalenceProved
      ≡
      false

open FormalDiskDualNumbersComparison public

builtinEqualityToDCHoTTPath :
  {A : Set} →
  {a b : A} →
  a
  ≡
  b →
  DCHoTT.DCHoTTPathOver a b
builtinEqualityToDCHoTTPath =
  DCHoTT.DCHoTTBuiltinEqualityToPath

equalityToDCHoTTImPath :
  {A : Set} →
  {a b : A} →
  a
  ≡
  b →
  DCHoTT.DCHoTTPathOver
    (DCHoTT.DCHoTTInfinitesimalUnit a)
    (DCHoTT.DCHoTTInfinitesimalUnit b)
equalityToDCHoTTImPath =
  DCHoTT.DCHoTTEqualityToImPath

dashiFormalDiskToDCHoTTDepthZeroFormalDisk :
  {P : B0.ProObjectCarrier} →
  (x : B0.ProObjectPoint P) →
  B0.FormalDisk x →
  DCHoTT.DCHoTTFormalDisk
    (B0.ProObjectCarrier.depthCarrier P zero)
    (B0.Im x)
dashiFormalDiskToDCHoTTDepthZeroFormalDisk x (y , close) =
  DCHoTTBasics._,_
    (B0.Im y)
    (equalityToDCHoTTImPath close)

dashiDepthZeroAgreementToImportedImModalEquality :
  {P : B0.ProObjectCarrier} →
  (x y : B0.ProObjectPoint P) →
  B0.DepthZeroAgreement x y →
  DCHoTT.DCHoTTPathOver
    (DCHoTT.DCHoTTInfinitesimalUnit (B0.Im x))
    (DCHoTT.DCHoTTInfinitesimalUnit (B0.Im y))
dashiDepthZeroAgreementToImportedImModalEquality x y xy =
  equalityToDCHoTTImPath
    (B0.depthZeroAgreementToImModalEquality x y xy)

dashiDepthOneAgreementToImportedImModalEquality :
  {P : B0.ProObjectCarrier} →
  (x y : B0.ProObjectPoint P) →
  B0.DepthOneAgreement x y →
  DCHoTT.DCHoTTPathOver
    (DCHoTT.DCHoTTInfinitesimalUnit (B0.Im x))
    (DCHoTT.DCHoTTInfinitesimalUnit (B0.Im y))
dashiDepthOneAgreementToImportedImModalEquality x y xy =
  equalityToDCHoTTImPath
    (B0.depthOneAgreementToImModalEquality x y xy)

record Depth01ImportedImModalEqualitySurface
  (P : B0.ProObjectCarrier) :
  Setω where
  field
    dashiDepth01Surface :
      B0.Depth01AgreementImModalSurface P

    importedImModalEquality :
      B0.ProObjectPoint P →
      B0.ProObjectPoint P →
      Set

    importedImModalEquality-v :
      (x y : B0.ProObjectPoint P) →
      importedImModalEquality x y
      ≡
      DCHoTT.DCHoTTPathOver
        (DCHoTT.DCHoTTInfinitesimalUnit (B0.Im x))
        (DCHoTT.DCHoTTInfinitesimalUnit (B0.Im y))

    depthZeroImpliesImportedImModal :
      (x y : B0.ProObjectPoint P) →
      B0.DepthZeroAgreement x y →
      importedImModalEquality x y

    depthOneImpliesImportedImModal :
      (x y : B0.ProObjectPoint P) →
      B0.DepthOneAgreement x y →
      importedImModalEquality x y

open Depth01ImportedImModalEqualitySurface public

canonicalDepth01ImportedImModalEqualitySurface :
  (P : B0.ProObjectCarrier) →
  Depth01ImportedImModalEqualitySurface P
canonicalDepth01ImportedImModalEqualitySurface P =
  record
    { dashiDepth01Surface =
        B0.canonicalDepth01AgreementImModalSurface P
    ; importedImModalEquality =
        λ x y →
          DCHoTT.DCHoTTPathOver
            (DCHoTT.DCHoTTInfinitesimalUnit (B0.Im x))
            (DCHoTT.DCHoTTInfinitesimalUnit (B0.Im y))
    ; importedImModalEquality-v =
        λ _ _ →
          refl
    ; depthZeroImpliesImportedImModal =
        dashiDepthZeroAgreementToImportedImModalEquality
    ; depthOneImpliesImportedImModal =
        dashiDepthOneAgreementToImportedImModalEquality
    }

record ImportedDiskReverseLiftData
  {P : B0.ProObjectCarrier}
  (x : B0.ProObjectPoint P)
  (disk :
    DCHoTT.DCHoTTFormalDisk
      (B0.ProObjectCarrier.depthCarrier P zero)
      (B0.Im x)) :
  Set₁ where
  field
    liftedPoint :
      B0.ProObjectPoint P

    includedPointMatchesLift :
      DCHoTT.DCHoTTFormalDiskInclusion (B0.Im x) disk
      ≡
      B0.Im liftedPoint

    dashiDepthZeroClose :
      B0.Im x
      ≡
      B0.Im liftedPoint

open ImportedDiskReverseLiftData public

importedDiskReverseLift :
  {P : B0.ProObjectCarrier} →
  (x : B0.ProObjectPoint P) →
  (disk :
    DCHoTT.DCHoTTFormalDisk
      (B0.ProObjectCarrier.depthCarrier P zero)
      (B0.Im x)) →
  ImportedDiskReverseLiftData x disk →
  B0.FormalDisk x
importedDiskReverseLift _ _ lift =
  ImportedDiskReverseLiftData.liftedPoint lift
  ,
  ImportedDiskReverseLiftData.dashiDepthZeroClose lift

dashiDiskReverseLiftData :
  {P : B0.ProObjectCarrier} →
  (x : B0.ProObjectPoint P) →
  (disk : B0.FormalDisk x) →
  ImportedDiskReverseLiftData x
    (dashiFormalDiskToDCHoTTDepthZeroFormalDisk x disk)
dashiDiskReverseLiftData x (y , close) =
  record
    { liftedPoint =
        y
    ; includedPointMatchesLift =
        refl
    ; dashiDepthZeroClose =
        close
    }

reverseLiftAfterDashiToImportedRoundtrip :
  {P : B0.ProObjectCarrier} →
  (x : B0.ProObjectPoint P) →
  (disk : B0.FormalDisk x) →
  importedDiskReverseLift x
    (dashiFormalDiskToDCHoTTDepthZeroFormalDisk x disk)
    (dashiDiskReverseLiftData x disk)
  ≡
  disk
reverseLiftAfterDashiToImportedRoundtrip _ (_ , _) =
  refl

reverseLiftImportedDiskIncludedPointRoundtrip :
  {P : B0.ProObjectCarrier} →
  (x : B0.ProObjectPoint P) →
  (disk :
    DCHoTT.DCHoTTFormalDisk
      (B0.ProObjectCarrier.depthCarrier P zero)
      (B0.Im x)) →
  (lift : ImportedDiskReverseLiftData x disk) →
  DCHoTT.DCHoTTFormalDiskInclusion (B0.Im x)
    (dashiFormalDiskToDCHoTTDepthZeroFormalDisk x
      (importedDiskReverseLift x disk lift))
  ≡
  DCHoTT.DCHoTTFormalDiskInclusion (B0.Im x) disk
reverseLiftImportedDiskIncludedPointRoundtrip _ _ lift =
  B0.b0-sym
    (ImportedDiskReverseLiftData.includedPointMatchesLift lift)

record B01ImportedReverseLiftRoundtripEvidence
  {P : B0.ProObjectCarrier}
  (x : B0.ProObjectPoint P) :
  Setω where
  field
    forwardImportedDisk :
      B0.FormalDisk x →
      DCHoTT.DCHoTTFormalDisk
        (B0.ProObjectCarrier.depthCarrier P zero)
        (B0.Im x)

    reverseLiftWithData :
      (disk :
        DCHoTT.DCHoTTFormalDisk
          (B0.ProObjectCarrier.depthCarrier P zero)
          (B0.Im x)) →
      ImportedDiskReverseLiftData x disk →
      B0.FormalDisk x

    forwardDiskLiftData :
      (disk : B0.FormalDisk x) →
      ImportedDiskReverseLiftData x (forwardImportedDisk disk)

    forwardReverseRoundtrip :
      (disk : B0.FormalDisk x) →
      reverseLiftWithData
        (forwardImportedDisk disk)
        (forwardDiskLiftData disk)
      ≡
      disk

    reverseForwardIncludedPointRoundtrip :
      (disk :
        DCHoTT.DCHoTTFormalDisk
          (B0.ProObjectCarrier.depthCarrier P zero)
          (B0.Im x)) →
      (lift : ImportedDiskReverseLiftData x disk) →
      DCHoTT.DCHoTTFormalDiskInclusion (B0.Im x)
        (forwardImportedDisk (reverseLiftWithData disk lift))
      ≡
      DCHoTT.DCHoTTFormalDiskInclusion (B0.Im x) disk

open B01ImportedReverseLiftRoundtripEvidence public

canonicalB01ImportedReverseLiftRoundtripEvidence :
  {P : B0.ProObjectCarrier} →
  (x : B0.ProObjectPoint P) →
  B01ImportedReverseLiftRoundtripEvidence x
canonicalB01ImportedReverseLiftRoundtripEvidence x =
  record
    { forwardImportedDisk =
        dashiFormalDiskToDCHoTTDepthZeroFormalDisk x
    ; reverseLiftWithData =
        importedDiskReverseLift x
    ; forwardDiskLiftData =
        dashiDiskReverseLiftData x
    ; forwardReverseRoundtrip =
        reverseLiftAfterDashiToImportedRoundtrip x
    ; reverseForwardIncludedPointRoundtrip =
        reverseLiftImportedDiskIncludedPointRoundtrip x
    }

record DASHIDCHoTTFormalDiskComparisonSocket
  {P : B0.ProObjectCarrier}
  (x : B0.ProObjectPoint P) :
  Setω where
  field
    dashiFormalDisk :
      Set₁

    dashiFormalDisk-v :
      dashiFormalDisk
      ≡
      B0.FormalDisk x

    dchottCarrier :
      Set

    dchottBasePoint :
      dchottCarrier

    importedImSurface :
      Set

    importedImSurface-v :
      importedImSurface
      ≡
      DCHoTT.DCHoTTInfinitesimalShape dchottCarrier

    importedFormalDiskAt :
      Set

    importedFormalDiskAt-v :
      importedFormalDiskAt
      ≡
      DCHoTT.DCHoTTFormalDiskAt dchottBasePoint

    importedFormalDiskFamily :
      dchottCarrier →
      Set

    importedFormalDiskFamily-v :
      (y : dchottCarrier) →
      importedFormalDiskFamily y
      ≡
      DCHoTT.DCHoTTFormalDisk dchottCarrier y

    dashiToImportedFormalDisk :
      dashiFormalDisk →
      importedFormalDiskAt

    equalityToImportedImPath :
      {a b : dchottCarrier} →
      a
      ≡
      b →
      DCHoTT.DCHoTTPathOver
        (DCHoTT.DCHoTTInfinitesimalUnit a)
        (DCHoTT.DCHoTTInfinitesimalUnit b)

    imModalQuotientEquality :
      dchottCarrier →
      dchottCarrier →
      Set

    imModalQuotientEquality-v :
      (a b : dchottCarrier) →
      imModalQuotientEquality a b
      ≡
      DCHoTT.DCHoTTPathOver
        (DCHoTT.DCHoTTInfinitesimalUnit a)
        (DCHoTT.DCHoTTInfinitesimalUnit b)

    depth01ImportedImModalEqualitySurface :
      Depth01ImportedImModalEqualitySurface P

    depthZeroAgreementToImportedImModal :
      (y : B0.ProObjectPoint P) →
      B0.DepthZeroAgreement x y →
      DCHoTT.DCHoTTPathOver
        (DCHoTT.DCHoTTInfinitesimalUnit (B0.Im x))
        (DCHoTT.DCHoTTInfinitesimalUnit (B0.Im y))

    depthOneAgreementToImportedImModal :
      (y : B0.ProObjectPoint P) →
      B0.DepthOneAgreement x y →
      DCHoTT.DCHoTTPathOver
        (DCHoTT.DCHoTTInfinitesimalUnit (B0.Im x))
        (DCHoTT.DCHoTTInfinitesimalUnit (B0.Im y))

    reverseLiftAtImportedPoint :
      dchottCarrier →
      Set₁

    reverseLiftImportedDiskTarget :
      importedFormalDiskAt →
      Set₁

    reverseLiftSocketLabel :
      String

    reverseLiftSocketLabel-v :
      reverseLiftSocketLabel
      ≡
      "typed-reverse-lift-from-imported-DCHoTT-depth-zero-disk-when-DASHI-lift-data-is-supplied"

    importedDiskReverseLiftData :
      (disk :
        DCHoTT.DCHoTTFormalDisk
          (B0.ProObjectCarrier.depthCarrier P zero)
          (B0.Im x)) →
      Set₁

    importedDiskReverseLiftData-v :
      (disk :
        DCHoTT.DCHoTTFormalDisk
          (B0.ProObjectCarrier.depthCarrier P zero)
          (B0.Im x)) →
      importedDiskReverseLiftData disk
      ≡
      ImportedDiskReverseLiftData x disk

    importedDiskReverseLiftWithData :
      (disk :
        DCHoTT.DCHoTTFormalDisk
          (B0.ProObjectCarrier.depthCarrier P zero)
          (B0.Im x)) →
      ImportedDiskReverseLiftData x disk →
      B0.FormalDisk x

    b01RoundtripEvidence :
      B01ImportedReverseLiftRoundtripEvidence x

    comparisonTarget :
      dashiFormalDisk →
      importedFormalDiskAt →
      Set

    comparisonLabel :
      String

    comparisonLabel-v :
      comparisonLabel
      ≡
      "target-only-DASHI-formal-disk-compared-with-imported-DCHoTT-FormalDisk-Im"

    dashiToDCHoTTMapConstructed :
      Bool

    dashiToDCHoTTMapConstructed-v :
      dashiToDCHoTTMapConstructed
      ≡
      true

    dchottToDASHIMapConstructed :
      Bool

    dchottToDASHIMapConstructed-v :
      dchottToDASHIMapConstructed
      ≡
      false

    dchottToDASHIMapWithLiftDataConstructed :
      Bool

    dchottToDASHIMapWithLiftDataConstructed-v :
      dchottToDASHIMapWithLiftDataConstructed
      ≡
      true

    roundtripsTypecheck :
      Bool

    roundtripsTypecheck-v :
      roundtripsTypecheck
      ≡
      false

    roundtripsWithLiftDataTypecheck :
      Bool

    roundtripsWithLiftDataTypecheck-v :
      roundtripsWithLiftDataTypecheck
      ≡
      true

    equivalenceClaimed :
      Bool

    equivalenceClaimed-v :
      equivalenceClaimed
      ≡
      false

    missingReverseBridge :
      List String

open DASHIDCHoTTFormalDiskComparisonSocket public

canonicalDASHIDCHoTTFormalDiskComparisonSocket :
  {P : B0.ProObjectCarrier} →
  (x : B0.ProObjectPoint P) →
  DASHIDCHoTTFormalDiskComparisonSocket x
canonicalDASHIDCHoTTFormalDiskComparisonSocket {P} x =
  record
    { dashiFormalDisk =
        B0.FormalDisk x
    ; dashiFormalDisk-v =
        refl
    ; dchottCarrier =
        B0.ProObjectCarrier.depthCarrier P zero
    ; dchottBasePoint =
        B0.Im x
    ; importedImSurface =
        DCHoTT.DCHoTTInfinitesimalShape
          (B0.ProObjectCarrier.depthCarrier P zero)
    ; importedImSurface-v =
        refl
    ; importedFormalDiskAt =
        DCHoTT.DCHoTTFormalDiskAt (B0.Im x)
    ; importedFormalDiskAt-v =
        refl
    ; importedFormalDiskFamily =
        DCHoTT.DCHoTTFormalDisk
          (B0.ProObjectCarrier.depthCarrier P zero)
    ; importedFormalDiskFamily-v =
        λ _ →
          refl
    ; dashiToImportedFormalDisk =
        dashiFormalDiskToDCHoTTDepthZeroFormalDisk x
    ; equalityToImportedImPath =
        equalityToDCHoTTImPath
    ; imModalQuotientEquality =
        λ a b →
          DCHoTT.DCHoTTPathOver
            (DCHoTT.DCHoTTInfinitesimalUnit a)
            (DCHoTT.DCHoTTInfinitesimalUnit b)
    ; imModalQuotientEquality-v =
        λ _ _ →
          refl
    ; depth01ImportedImModalEqualitySurface =
        canonicalDepth01ImportedImModalEqualitySurface P
    ; depthZeroAgreementToImportedImModal =
        dashiDepthZeroAgreementToImportedImModalEquality x
    ; depthOneAgreementToImportedImModal =
        dashiDepthOneAgreementToImportedImModalEquality x
    ; reverseLiftAtImportedPoint =
        B0.ImFibreAt {P = P}
    ; reverseLiftImportedDiskTarget =
        λ disk →
          B0.ImFibreAt {P = P}
            (DCHoTT.DCHoTTFormalDiskInclusion (B0.Im {P = P} x) disk)
    ; reverseLiftSocketLabel =
        "typed-reverse-lift-from-imported-DCHoTT-depth-zero-disk-when-DASHI-lift-data-is-supplied"
    ; reverseLiftSocketLabel-v =
        refl
    ; importedDiskReverseLiftData =
        ImportedDiskReverseLiftData x
    ; importedDiskReverseLiftData-v =
        λ _ →
          refl
    ; importedDiskReverseLiftWithData =
        importedDiskReverseLift x
    ; b01RoundtripEvidence =
        canonicalB01ImportedReverseLiftRoundtripEvidence x
    ; comparisonTarget =
        λ _ _ →
          ⊤
    ; comparisonLabel =
        "target-only-DASHI-formal-disk-compared-with-imported-DCHoTT-FormalDisk-Im"
    ; comparisonLabel-v =
        refl
    ; dashiToDCHoTTMapConstructed =
        true
    ; dashiToDCHoTTMapConstructed-v =
        refl
    ; dchottToDASHIMapConstructed =
        false
    ; dchottToDASHIMapConstructed-v =
        refl
    ; dchottToDASHIMapWithLiftDataConstructed =
        true
    ; dchottToDASHIMapWithLiftDataConstructed-v =
        refl
    ; roundtripsTypecheck =
        false
    ; roundtripsTypecheck-v =
        refl
    ; roundtripsWithLiftDataTypecheck =
        true
    ; roundtripsWithLiftDataTypecheck-v =
        refl
    ; equivalenceClaimed =
        false
    ; equivalenceClaimed-v =
        refl
    ; missingReverseBridge =
        "DCHoTT formal-disk-at_ only accepts X : 𝒰₀, while DASHI ProObjectPoint P is Set₁"
        ∷ "the implemented map therefore targets the imported DCHoTT disk over DASHI Im/depthCarrier zero, not over ProObjectPoint P"
        ∷ "typed reverse lift now exists when ImportedDiskReverseLiftData supplies a compatible ProObjectPoint over the imported disk inclusion"
        ∷ "DASHI-to-imported-to-DASHI roundtrip and imported included-point roundtrip typecheck under that supplied lift data"
        ∷ "an unconditional reverse map still needs a bridge from DCHoTT ℑ-unit proximity paths back to DASHI builtin depth-zero equality"
        ∷ "the im-modal quotient equality socket maps depth-zero/depth-one agreement into DCHoTT ℑ-unit paths but does not construct quotient elimination or reflection"
        ∷ []
    }

record TangentFirstGradedBinding
  (P : B0.ProObjectCarrier) :
  Set₁ where
  field
    FirstGradedPieceAt :
      B0.ProObjectCarrier.depthCarrier P zero →
      Set

    TangentAt :
      B0.ProObjectPoint P →
      Set

    tangentToFirstGraded :
      (x : B0.ProObjectPoint P) →
      TangentAt x →
      FirstGradedPieceAt (B0.Im x)

    firstGradedToTangent :
      (x : B0.ProObjectPoint P) →
      FirstGradedPieceAt (B0.Im x) →
      TangentAt x

    tangentFirstGradedToFrom :
      (x : B0.ProObjectPoint P) →
      (v : TangentAt x) →
      firstGradedToTangent x (tangentToFirstGraded x v)
      ≡
      v

    tangentFirstGradedFromTo :
      (x : B0.ProObjectPoint P) →
      (g : FirstGradedPieceAt (B0.Im x)) →
      tangentToFirstGraded x (firstGradedToTangent x g)
      ≡
      g

    bindingLabel :
      String

    bindingLabel-v :
      bindingLabel
      ≡
      "DASHI-side-tangent-first-graded-equivalence-record-no-vector-space-promotion"

    tangentEqualsFirstGradedProved :
      Bool

    tangentEqualsFirstGradedProved-v :
      tangentEqualsFirstGradedProved
      ≡
      true

open TangentFirstGradedBinding public

canonicalTerminalTangentFirstGradedBinding :
  (P : B0.ProObjectCarrier) →
  TangentFirstGradedBinding P
canonicalTerminalTangentFirstGradedBinding P =
  record
    { FirstGradedPieceAt =
        λ _ →
          ⊤
    ; TangentAt =
        λ _ →
          ⊤
    ; tangentToFirstGraded =
        λ _ _ →
          tt
    ; firstGradedToTangent =
        λ _ _ →
          tt
    ; tangentFirstGradedToFrom =
        λ _ tangent →
          terminalSectionEq tt tangent
    ; tangentFirstGradedFromTo =
        λ _ graded →
          terminalSectionEq tt graded
    ; bindingLabel =
        "DASHI-side-tangent-first-graded-equivalence-record-no-vector-space-promotion"
    ; bindingLabel-v =
        refl
    ; tangentEqualsFirstGradedProved =
        true
    ; tangentEqualsFirstGradedProved-v =
        refl
    }

record TransportSmoothFormalDiskReceipt
  (P : B0.ProObjectCarrier) :
  Setω where
  field
    b01Semantics :
      Sem.B01ProObjectSemanticsReceipt P

    clopenSite :
      ClopenBallSite P

    canonicalPartitionLaws :
      CanonicalDepthPartitionLawSurface P

    canonicalBallRestrictions :
      CanonicalBallRestrictionSurface P

    terminalSheafLocality :
      SheafLocalitySurface P

    terminalSheafGluing :
      SheafGluingSurface P

    terminalTangentFirstGradedBinding :
      TangentFirstGradedBinding P

    dchottFormalDiskComparisonSocket :
      (x : B0.ProObjectPoint P) →
      DASHIDCHoTTFormalDiskComparisonSocket x

    imReflectDASHIAuthorityPostulateSurface :
      ImReflectDASHIAuthorityPostulateSurface
        ⊤
        (λ _ _ → ⊤)
        (λ _ _ → ⊤)
        (λ _ _ → ⊤)

    openObligations :
      List TransportSmoothOpenObligation

    openObligationsAreCanonical :
      openObligations
      ≡
      canonicalTransportSmoothOpenObligations

    analyticSurfaceSpecified :
      Bool

    analyticSurfaceSpecified-v :
      analyticSurfaceSpecified
      ≡
      true

    fullSheafTheoremProved :
      Bool

    fullSheafTheoremProved-v :
      fullSheafTheoremProved
      ≡
      false

    firstOrderApproximationProved :
      Bool

    firstOrderApproximationProved-v :
      firstOrderApproximationProved
      ≡
      false

    dchottFormalDiskEquivalenceProved :
      Bool

    dchottFormalDiskEquivalenceProved-v :
      dchottFormalDiskEquivalenceProved
      ≡
      false

    b01ClosedModuloImReflectAuthority :
      Bool

    b01ClosedModuloImReflectAuthority-v :
      b01ClosedModuloImReflectAuthority
      ≡
      true

    imReflectAuthorityBlockedByCohesion :
      Bool

    imReflectAuthorityBlockedByCohesion-v :
      imReflectAuthorityBlockedByCohesion
      ≡
      true

    b0Promoted :
      Bool

    b0Promoted-v :
      b0Promoted
      ≡
      false

    receiptBoundary :
      List String

open TransportSmoothFormalDiskReceipt public

canonicalTransportSmoothFormalDiskReceipt :
  (P : B0.ProObjectCarrier) →
  TransportSmoothFormalDiskReceipt P
canonicalTransportSmoothFormalDiskReceipt P =
  record
    { b01Semantics =
        Sem.canonicalB01ProObjectSemanticsReceipt P
    ; clopenSite =
        canonicalClopenBallSite P
    ; canonicalPartitionLaws =
        canonicalDepthPartitionLawSurface P
    ; canonicalBallRestrictions =
        canonicalBallRestrictionSurface P
    ; terminalSheafLocality =
        canonicalTerminalSheafLocalitySurface P
    ; terminalSheafGluing =
        canonicalTerminalSheafGluingSurface P
    ; terminalTangentFirstGradedBinding =
        canonicalTerminalTangentFirstGradedBinding P
    ; dchottFormalDiskComparisonSocket =
        canonicalDASHIDCHoTTFormalDiskComparisonSocket
    ; imReflectDASHIAuthorityPostulateSurface =
        canonicalImReflectDASHIAuthorityPostulateSurface
    ; openObligations =
        canonicalTransportSmoothOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; analyticSurfaceSpecified =
        true
    ; analyticSurfaceSpecified-v =
        refl
    ; fullSheafTheoremProved =
        false
    ; fullSheafTheoremProved-v =
        refl
    ; firstOrderApproximationProved =
        false
    ; firstOrderApproximationProved-v =
        refl
    ; dchottFormalDiskEquivalenceProved =
        false
    ; dchottFormalDiskEquivalenceProved-v =
        refl
    ; b01ClosedModuloImReflectAuthority =
        true
    ; b01ClosedModuloImReflectAuthority-v =
        refl
    ; imReflectAuthorityBlockedByCohesion =
        true
    ; imReflectAuthorityBlockedByCohesion-v =
        refl
    ; b0Promoted =
        false
    ; b0Promoted-v =
        refl
    ; receiptBoundary =
        "Clopen-ball site and canonical depth partitions are constructed from DASHI-side B0.1 depth agreement"
        ∷ "TransportSmoothFunction records TS1-TS4 labels and a concrete evaluator over FormalDisk"
        ∷ "Canonical depth partition same-cell laws, one-step ball restriction, and FormalDisk equals depth-zero ball are inhabited by refl/depth-agreement"
        ∷ "Terminal clopen-site sheaf locality and singleton gluing are inhabited; this is not a full sheaf theorem for arbitrary sections"
        ∷ "Terminal tangent equals first-graded binding is inhabited; vector-space and DCHoTT tangent promotions remain open"
        ∷ "Product rule, first-order approximation, and dual-number comparison remain explicit targets"
        ∷ "DASHI/DCHoTT comparison constructs a map from DASHI FormalDisk to imported DCHoTT FormalDisk over the depth-zero Im carrier"
        ∷ "Builtin depth-zero equality and depth-one agreement are mapped to imported DCHoTT Im paths through the shim equality-to-Im-path adapter"
        ∷ "Reverse lift with explicit ImportedDiskReverseLiftData is constructed, with DASHI forward/reverse and imported included-point roundtrip evidence"
        ∷ "Unconditional DCHoTT reverse map, full DCHoTT path-level roundtrip, and equivalence remain blocked by missing arbitrary lift/reflection bridges"
        ∷ "ImReflectDASHI is recorded only as a safe postulate surface over local Set/relation placeholders, with formal etale pro-object shape and depth-0/depth-1 reflection targets"
        ∷ "B0.1 may be treated as closed only modulo the ImReflectDASHI authority surface; cohesion still blocks a local constructive DCHoTT proof"
        ∷ "No DCHoTT formal-disk equivalence, analytic completion theorem, or B0 promotion is constructed here"
        ∷ []
    }
