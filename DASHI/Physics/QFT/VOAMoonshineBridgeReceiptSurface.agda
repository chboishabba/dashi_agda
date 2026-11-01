module DASHI.Physics.QFT.VOAMoonshineBridgeReceiptSurface where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- VOA / Moonshine / K3 bridge target surface.
--
-- This module records typed sockets for a possible route through vertex
-- operator algebras, Moonshine VOA data, chiral CFT nets, holomorphic
-- factorisation, K3 compactification, and a 4D effective-theory target.
--
-- It is deliberately non-promoting.  It does not construct a VOA, prove
-- Moonshine, construct a conformal net, derive K3 compactification data, or
-- derive four-dimensional physics.

data VOAMoonshineBridgeStatus : Set where
  voaMoonshineBridgeTargetsOnlyNoPromotion :
    VOAMoonshineBridgeStatus

data VOAMoonshineBridgeOpenObligation : Set where
  missingVertexOperatorAlgebraConstruction :
    VOAMoonshineBridgeOpenObligation

  missingVOALocalityJacobiIdentity :
    VOAMoonshineBridgeOpenObligation

  missingMoonshineVOAConstruction :
    VOAMoonshineBridgeOpenObligation

  missingMonsterSymmetryAction :
    VOAMoonshineBridgeOpenObligation

  missingChiralCFTNetConstruction :
    VOAMoonshineBridgeOpenObligation

  missingChiralNetLocalityAndCovariance :
    VOAMoonshineBridgeOpenObligation

  missingHolomorphicFactorisationLaw :
    VOAMoonshineBridgeOpenObligation

  missingK3CompactificationGeometry :
    VOAMoonshineBridgeOpenObligation

  missingK3SCFTOrSigmaModelBridge :
    VOAMoonshineBridgeOpenObligation

  missingFourDimensionalEffectiveTheoryExtraction :
    VOAMoonshineBridgeOpenObligation

  missingPhenomenologyAndAnomalyChecks :
    VOAMoonshineBridgeOpenObligation

canonicalVOAMoonshineBridgeOpenObligations :
  List VOAMoonshineBridgeOpenObligation
canonicalVOAMoonshineBridgeOpenObligations =
  missingVertexOperatorAlgebraConstruction
  ∷ missingVOALocalityJacobiIdentity
  ∷ missingMoonshineVOAConstruction
  ∷ missingMonsterSymmetryAction
  ∷ missingChiralCFTNetConstruction
  ∷ missingChiralNetLocalityAndCovariance
  ∷ missingHolomorphicFactorisationLaw
  ∷ missingK3CompactificationGeometry
  ∷ missingK3SCFTOrSigmaModelBridge
  ∷ missingFourDimensionalEffectiveTheoryExtraction
  ∷ missingPhenomenologyAndAnomalyChecks
  ∷ []

data VOAMoonshineBridgePromotionAuthorityToken : Set where

postulate
  AbstractStateSpace :
    Set

  AbstractVacuumVector :
    Set

  AbstractVirasoroElement :
    Set

  AbstractVertexOperator :
    Set

  abstractVertexOperatorMap :
    AbstractStateSpace →
    AbstractVertexOperator

  abstractVOAJacobiIdentityTarget :
    Set

  AbstractMonsterGroup :
    Set

  AbstractMoonshineVOA :
    Set

  AbstractGradedDimension :
    Set

  AbstractJInvariantTarget :
    Set

  abstractMonsterActionTarget :
    AbstractMonsterGroup →
    AbstractMoonshineVOA →
    Set

  AbstractChiralInterval :
    Set

  AbstractChiralLocalAlgebra :
    AbstractChiralInterval →
    Set

  abstractChiralIsotonyTarget :
    AbstractChiralInterval →
    AbstractChiralInterval →
    Set

  abstractChiralLocalityTarget :
    AbstractChiralInterval →
    AbstractChiralInterval →
    Set

  AbstractChiralCovarianceTarget :
    Set

  AbstractFullCFT :
    Set

  AbstractLeftChiralSector :
    Set

  AbstractRightChiralSector :
    Set

  AbstractHolomorphicFactorisationMap :
    Set

  AbstractK3Surface :
    Set

  AbstractK3CompactificationData :
    Set

  AbstractK3SigmaModelTarget :
    Set

  AbstractEffective4DFieldContent :
    Set

  AbstractEffective4DGaugeTarget :
    Set

  AbstractEffective4DCouplingTarget :
    Set

  AbstractEffective4DSpectrumTarget :
    Set

  AbstractEffective4DAnomalyCheckTarget :
    Set

record VertexOperatorAlgebraTargetSurface : Setω where
  field
    StateSpace :
      Set

    VacuumVector :
      Set

    VirasoroElement :
      Set

    VertexOperator :
      Set

    vertexOperatorMap :
      StateSpace →
      VertexOperator

    localityJacobiIdentityTarget :
      Set

    voaTargetName :
      String

    voaTargetName-v :
      voaTargetName
      ≡
      "target-only-vertex-operator-algebra-with-vacuum-virasoro-and-Jacobi-locality"

open VertexOperatorAlgebraTargetSurface public

record MoonshineVOATargetSurface : Setω where
  field
    MonsterGroup :
      Set

    MoonshineVOA :
      Set

    gradedDimension :
      Set

    jInvariantTarget :
      Set

    monsterActionTarget :
      MonsterGroup →
      MoonshineVOA →
      Set

    moonshineTargetName :
      String

    moonshineTargetName-v :
      moonshineTargetName
      ≡
      "target-only-Moonshine-VOA-with-Monster-action-and-graded-dimension"

    moonshinePromoted :
      Bool

    moonshinePromotedIsFalse :
      moonshinePromoted ≡ false

open MoonshineVOATargetSurface public

record ChiralCFTNetTargetSurface : Setω where
  field
    ChiralInterval :
      Set

    LocalAlgebra :
      ChiralInterval →
      Set

    isotonyTarget :
      ChiralInterval →
      ChiralInterval →
      Set

    localityTarget :
      ChiralInterval →
      ChiralInterval →
      Set

    covarianceTarget :
      Set

    chiralNetTargetName :
      String

    chiralNetTargetName-v :
      chiralNetTargetName
      ≡
      "target-only-chiral-CFT-net-with-isotony-locality-and-covariance"

open ChiralCFTNetTargetSurface public

record HolomorphicFactorisationTargetSurface : Setω where
  field
    FullCFT :
      Set

    LeftChiralSector :
      Set

    RightChiralSector :
      Set

    factorisationMapTarget :
      Set

    holomorphicFactorisationTargetName :
      String

    holomorphicFactorisationTargetName-v :
      holomorphicFactorisationTargetName
      ≡
      "target-only-holomorphic-factorisation-full-CFT-to-left-right-chiral-sectors"

    factorisationPromoted :
      Bool

    factorisationPromotedIsFalse :
      factorisationPromoted ≡ false

open HolomorphicFactorisationTargetSurface public

record K3CompactificationTargetSurface : Setω where
  field
    K3Surface :
      Set

    CompactificationData :
      Set

    K3SigmaModelTarget :
      Set

    k3BridgeTargetName :
      String

    k3BridgeTargetName-v :
      k3BridgeTargetName
      ≡
      "target-only-K3-compactification-and-K3-SCFT-sigma-model-bridge"

    k3CompactificationPromoted :
      Bool

    k3CompactificationPromotedIsFalse :
      k3CompactificationPromoted ≡ false

open K3CompactificationTargetSurface public

record Effective4DTheoryTargetSurface : Setω where
  field
    FieldContentTarget :
      Set

    GaugeTarget :
      Set

    CouplingTarget :
      Set

    SpectrumTarget :
      Set

    anomalyCheckTarget :
      Set

    effectiveTheoryTargetName :
      String

    effectiveTheoryTargetName-v :
      effectiveTheoryTargetName
      ≡
      "target-only-four-dimensional-effective-theory-data-not-derived-physics"

    fourDimensionalPhysicsDerived :
      Bool

    fourDimensionalPhysicsDerivedIsFalse :
      fourDimensionalPhysicsDerived ≡ false

open Effective4DTheoryTargetSurface public

record VOAMoonshineBridgeReceiptSurface : Setω where
  field
    status :
      VOAMoonshineBridgeStatus

    voaSurface :
      VertexOperatorAlgebraTargetSurface

    moonshineSurface :
      MoonshineVOATargetSurface

    chiralCFTNetSurface :
      ChiralCFTNetTargetSurface

    holomorphicFactorisationSurface :
      HolomorphicFactorisationTargetSurface

    k3CompactificationSurface :
      K3CompactificationTargetSurface

    effective4DTheorySurface :
      Effective4DTheoryTargetSurface

    openObligations :
      List VOAMoonshineBridgeOpenObligation

    openObligationsAreCanonical :
      openObligations
      ≡
      canonicalVOAMoonshineBridgeOpenObligations

    bridgePromoted :
      Bool

    bridgePromotedIsFalse :
      bridgePromoted ≡ false

    fourDimensionalPhysicsDerived :
      Bool

    fourDimensionalPhysicsDerivedIsFalse :
      fourDimensionalPhysicsDerived ≡ false

    noPromotionWithoutAuthority :
      VOAMoonshineBridgePromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open VOAMoonshineBridgeReceiptSurface public

canonicalVertexOperatorAlgebraTargetSurface :
  VertexOperatorAlgebraTargetSurface
canonicalVertexOperatorAlgebraTargetSurface =
  record
    { StateSpace =
        AbstractStateSpace
    ; VacuumVector =
        AbstractVacuumVector
    ; VirasoroElement =
        AbstractVirasoroElement
    ; VertexOperator =
        AbstractVertexOperator
    ; vertexOperatorMap =
        abstractVertexOperatorMap
    ; localityJacobiIdentityTarget =
        abstractVOAJacobiIdentityTarget
    ; voaTargetName =
        "target-only-vertex-operator-algebra-with-vacuum-virasoro-and-Jacobi-locality"
    ; voaTargetName-v =
        refl
    }

canonicalMoonshineVOATargetSurface :
  MoonshineVOATargetSurface
canonicalMoonshineVOATargetSurface =
  record
    { MonsterGroup =
        AbstractMonsterGroup
    ; MoonshineVOA =
        AbstractMoonshineVOA
    ; gradedDimension =
        AbstractGradedDimension
    ; jInvariantTarget =
        AbstractJInvariantTarget
    ; monsterActionTarget =
        abstractMonsterActionTarget
    ; moonshineTargetName =
        "target-only-Moonshine-VOA-with-Monster-action-and-graded-dimension"
    ; moonshineTargetName-v =
        refl
    ; moonshinePromoted =
        false
    ; moonshinePromotedIsFalse =
        refl
    }

canonicalChiralCFTNetTargetSurface :
  ChiralCFTNetTargetSurface
canonicalChiralCFTNetTargetSurface =
  record
    { ChiralInterval =
        AbstractChiralInterval
    ; LocalAlgebra =
        AbstractChiralLocalAlgebra
    ; isotonyTarget =
        abstractChiralIsotonyTarget
    ; localityTarget =
        abstractChiralLocalityTarget
    ; covarianceTarget =
        AbstractChiralCovarianceTarget
    ; chiralNetTargetName =
        "target-only-chiral-CFT-net-with-isotony-locality-and-covariance"
    ; chiralNetTargetName-v =
        refl
    }

canonicalHolomorphicFactorisationTargetSurface :
  HolomorphicFactorisationTargetSurface
canonicalHolomorphicFactorisationTargetSurface =
  record
    { FullCFT =
        AbstractFullCFT
    ; LeftChiralSector =
        AbstractLeftChiralSector
    ; RightChiralSector =
        AbstractRightChiralSector
    ; factorisationMapTarget =
        AbstractHolomorphicFactorisationMap
    ; holomorphicFactorisationTargetName =
        "target-only-holomorphic-factorisation-full-CFT-to-left-right-chiral-sectors"
    ; holomorphicFactorisationTargetName-v =
        refl
    ; factorisationPromoted =
        false
    ; factorisationPromotedIsFalse =
        refl
    }

canonicalK3CompactificationTargetSurface :
  K3CompactificationTargetSurface
canonicalK3CompactificationTargetSurface =
  record
    { K3Surface =
        AbstractK3Surface
    ; CompactificationData =
        AbstractK3CompactificationData
    ; K3SigmaModelTarget =
        AbstractK3SigmaModelTarget
    ; k3BridgeTargetName =
        "target-only-K3-compactification-and-K3-SCFT-sigma-model-bridge"
    ; k3BridgeTargetName-v =
        refl
    ; k3CompactificationPromoted =
        false
    ; k3CompactificationPromotedIsFalse =
        refl
    }

canonicalEffective4DTheoryTargetSurface :
  Effective4DTheoryTargetSurface
canonicalEffective4DTheoryTargetSurface =
  record
    { FieldContentTarget =
        AbstractEffective4DFieldContent
    ; GaugeTarget =
        AbstractEffective4DGaugeTarget
    ; CouplingTarget =
        AbstractEffective4DCouplingTarget
    ; SpectrumTarget =
        AbstractEffective4DSpectrumTarget
    ; anomalyCheckTarget =
        AbstractEffective4DAnomalyCheckTarget
    ; effectiveTheoryTargetName =
        "target-only-four-dimensional-effective-theory-data-not-derived-physics"
    ; effectiveTheoryTargetName-v =
        refl
    ; fourDimensionalPhysicsDerived =
        false
    ; fourDimensionalPhysicsDerivedIsFalse =
        refl
    }

canonicalVOAMoonshineBridgeReceiptSurface :
  VOAMoonshineBridgeReceiptSurface
canonicalVOAMoonshineBridgeReceiptSurface =
  record
    { status =
        voaMoonshineBridgeTargetsOnlyNoPromotion
    ; voaSurface =
        canonicalVertexOperatorAlgebraTargetSurface
    ; moonshineSurface =
        canonicalMoonshineVOATargetSurface
    ; chiralCFTNetSurface =
        canonicalChiralCFTNetTargetSurface
    ; holomorphicFactorisationSurface =
        canonicalHolomorphicFactorisationTargetSurface
    ; k3CompactificationSurface =
        canonicalK3CompactificationTargetSurface
    ; effective4DTheorySurface =
        canonicalEffective4DTheoryTargetSurface
    ; openObligations =
        canonicalVOAMoonshineBridgeOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; bridgePromoted =
        false
    ; bridgePromotedIsFalse =
        refl
    ; fourDimensionalPhysicsDerived =
        false
    ; fourDimensionalPhysicsDerivedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "VOA layer is target-only: no vertex-operator algebra, locality/Jacobi identity, or representation category is constructed here"
        ∷ "Moonshine VOA layer is target-only: no Monster action, graded-dimension theorem, or j-invariant theorem is proved here"
        ∷ "Chiral CFT net layer is target-only: isotony, locality, covariance, and conformal-net construction remain open"
        ∷ "Holomorphic factorisation is a target socket, not a factorisation theorem"
        ∷ "K3 compactification and K3 SCFT/sigma-model bridge are target sockets only"
        ∷ "The 4D effective-theory surface records field-content, gauge, coupling, spectrum, and anomaly-check targets but derives no four-dimensional physics"
        ∷ "This receipt is non-promoting and supplies no Standard Model, GRQFT, TOE, or physical derivation claim"
        ∷ []
    }
