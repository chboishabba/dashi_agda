module DASHI.Physics.Closure.G6PrerequisiteIndex where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- G6 prerequisite index.
--
-- This file is deliberately non-promoting.  It records the exact upstream
-- gates that a future G6 commutativity receipt must consume, without importing
-- or manufacturing any of those inhabitants from current obligation surfaces.

data G6PrerequisiteIndexStatus : Set where
  indexedPrerequisitesOnlyNoG6Commutativity :
    G6PrerequisiteIndexStatus

data G6PrerequisiteLane : Set where
  g2DiscreteCurvatureCarrierLane :
    G6PrerequisiteLane
  g3PoincareToGalileiContractionCarrierLane :
    G6PrerequisiteLane
  grNonFlatLeviCivitaEinsteinLane :
    G6PrerequisiteLane
  w3FullEmpiricalAdequacyLane :
    G6PrerequisiteLane
  g6OrthogonalityLawLane :
    G6PrerequisiteLane

data G6PrerequisiteBlocker : Set where
  missingG2DiscreteCurvatureCarrier :
    G6PrerequisiteBlocker
  missingG3PoincareToGalileiContractionCarrier :
    G6PrerequisiteBlocker
  missingGRNonFlatLeviCivitaEinsteinSurface :
    G6PrerequisiteBlocker
  missingW3FullEmpiricalAdequacy :
    G6PrerequisiteBlocker
  missingP2ReImOrthogonalityLaw :
    G6PrerequisiteBlocker
  missingPrimeSectorOrthogonalityLaw :
    G6PrerequisiteBlocker

canonicalG6PrerequisiteBlockers :
  List G6PrerequisiteBlocker
canonicalG6PrerequisiteBlockers =
  missingG2DiscreteCurvatureCarrier
  ∷ missingG3PoincareToGalileiContractionCarrier
  ∷ missingGRNonFlatLeviCivitaEinsteinSurface
  ∷ missingW3FullEmpiricalAdequacy
  ∷ missingP2ReImOrthogonalityLaw
  ∷ missingPrimeSectorOrthogonalityLaw
  ∷ []

record G6OrthogonalityLawRequest : Set where
  field
    p2ReProjectionName :
      String

    p2ImProjectionName :
      String

    p2ReImOrthogonalityLawName :
      String

    primeSectorCarrierName :
      String

    primeSectorOrthogonalityLawName :
      String

    requestBoundary :
      List String

canonicalG6OrthogonalityLawRequest :
  G6OrthogonalityLawRequest
canonicalG6OrthogonalityLawRequest =
  record
    { p2ReProjectionName =
        "p2 Re projection"
    ; p2ImProjectionName =
        "p2 Im projection"
    ; p2ReImOrthogonalityLawName =
        "p2 Re/Im orthogonality law"
    ; primeSectorCarrierName =
        "prime-sector carrier embedding for G6 lanes"
    ; primeSectorOrthogonalityLawName =
        "prime-sector orthogonality law"
    ; requestBoundary =
        "These fields request law names only; they do not inhabit an orthogonality theorem"
        ∷ "The p2 Re/Im law must be tied to the same p2 carrier used by the G3 contraction route"
        ∷ "The prime-sector law must be tied to the same embeddings used by Maxwell, Schrodinger, GR, and empirical lanes"
        ∷ []
    }

record G6AllPrerequisiteInhabitants : Setω where
  field
    g2DiscreteCurvatureCarrier :
      Set

    g3PoincareToGalileiContractionCarrier :
      Set

    grNonFlatFiniteRLeviCivitaEinsteinSurface :
      Set

    w3FullEmpiricalAdequacy :
      Set

    p2ReImOrthogonalityLaw :
      Set

    primeSectorOrthogonalityLaw :
      Set

    inhabitantBoundary :
      List String

record G6CommutativityClaimGate
  (prerequisites : G6AllPrerequisiteInhabitants) : Setω where
  field
    consumedPrerequisites :
      G6AllPrerequisiteInhabitants

    commutativityBoundary :
      List String

record G6PrerequisiteIndex : Setω where
  field
    status :
      G6PrerequisiteIndexStatus

    prerequisiteLanes :
      List G6PrerequisiteLane

    g2DiscreteCurvatureCarrierModule :
      String

    g2DiscreteCurvatureCarrierType :
      String

    g2RequiredCarrierName :
      String

    g3PoincareGalileiCarrierChainModule :
      String

    g3PoincareToGalileiContractionCarrierType :
      String

    grNonFlatLeviCivitaEinsteinModule :
      String

    grNonFlatLeviCivitaEinsteinSurfaceType :
      String

    w3EmpiricalAuthorityModule :
      String

    w3FullEmpiricalAdequacyType :
      String

    orthogonalityLawRequest :
      G6OrthogonalityLawRequest

    firstBlocker :
      G6PrerequisiteBlocker

    firstBlockerIsG2DiscreteCurvatureCarrier :
      firstBlocker
      ≡
      missingG2DiscreteCurvatureCarrier

    blockers :
      List G6PrerequisiteBlocker

    blockersAreCanonical :
      blockers
      ≡
      canonicalG6PrerequisiteBlockers

    commutativityRequires :
      String

    noPromotionBoundary :
      List String

canonicalG6PrerequisiteIndex :
  G6PrerequisiteIndex
canonicalG6PrerequisiteIndex =
  record
    { status =
        indexedPrerequisitesOnlyNoG6Commutativity
    ; prerequisiteLanes =
        g2DiscreteCurvatureCarrierLane
        ∷ g3PoincareToGalileiContractionCarrierLane
        ∷ grNonFlatLeviCivitaEinsteinLane
        ∷ w3FullEmpiricalAdequacyLane
        ∷ g6OrthogonalityLawLane
        ∷ []
    ; g2DiscreteCurvatureCarrierModule =
        "DASHI.Physics.Closure.G2DiscreteCurvatureCarrier"
    ; g2DiscreteCurvatureCarrierType =
        "DiscreteCurvatureCarrier"
    ; g2RequiredCarrierName =
        "DiscreteCurvatureCarrier for SFGC.GaugeField"
    ; g3PoincareGalileiCarrierChainModule =
        "DASHI.Physics.Closure.G3PoincareGalileiCarrierChain"
    ; g3PoincareToGalileiContractionCarrierType =
        "G3PoincareGalileiCarrierChain.poincareToGalileiContractionCarrier canonicalG3PoincareGalileiCarrierChain"
    ; grNonFlatLeviCivitaEinsteinModule =
        "DASHI.Physics.Closure.GRDiscreteBianchiFiniteR"
    ; grNonFlatLeviCivitaEinsteinSurfaceType =
        "GRDiscreteBianchiFiniteRObligationSurface with selected non-flat finite-r Levi-Civita/Bianchi/Ricci/Einstein obligations"
    ; w3EmpiricalAuthorityModule =
        "DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate"
    ; w3FullEmpiricalAdequacyType =
        "W3AcceptedEmpiricalAuthorityGate"
    ; orthogonalityLawRequest =
        canonicalG6OrthogonalityLawRequest
    ; firstBlocker =
        missingG2DiscreteCurvatureCarrier
    ; firstBlockerIsG2DiscreteCurvatureCarrier =
        refl
    ; blockers =
        canonicalG6PrerequisiteBlockers
    ; blockersAreCanonical =
        refl
    ; commutativityRequires =
        "G6CommutativityClaimGate may only be formed after G6AllPrerequisiteInhabitants is supplied"
    ; noPromotionBoundary =
        "This index records G2, G3, GR, W3, and orthogonality prerequisites only"
        ∷ "It does not construct DiscreteCurvatureCarrier for the shift gauge field"
        ∷ "It does not construct PoincareToGalileiContractionCarrier for the Schrodinger lane"
        ∷ "It does not upgrade the GR obligation surface to a non-flat Levi-Civita/Einstein closure"
        ∷ "It does not construct W3AcceptedEmpiricalAuthorityGate or full empirical adequacy"
        ∷ "It does not claim G6 commutativity"
        ∷ []
    }

canonicalG6PrerequisiteIndexStatus :
  G6PrerequisiteIndexStatus
canonicalG6PrerequisiteIndexStatus =
  G6PrerequisiteIndex.status canonicalG6PrerequisiteIndex

canonicalG6PrerequisiteIndexNoCommutativity :
  canonicalG6PrerequisiteIndexStatus
  ≡
  indexedPrerequisitesOnlyNoG6Commutativity
canonicalG6PrerequisiteIndexNoCommutativity = refl
