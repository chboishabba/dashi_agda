module DASHI.Physics.Closure.GRFirstOrderGravityScope where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Closure.EinsteinEquationCandidate as EEC
import DASHI.Physics.Closure.GRQFTConsumerNextObligationV2 as GRQFT
import DASHI.Physics.Closure.KnownLimitsGRBridgeTheorem as GR
import DASHI.Physics.Closure.W4MatterStressEnergyMDLInternalBridge as W4SE

------------------------------------------------------------------------
-- G4 first-order gravity scope.
--
-- This module deliberately does not claim GR closure.  It records the
-- first-order/BF/MacDowell-Mansouri route as a typed obligation surface after
-- the current F^2 versus R mismatch diagnostic: a curvature-norm/Yang-Mills
-- route is not by itself an Einstein-Hilbert action.  A future G4 theorem must
-- supply a first-order structure group, vierbein, spin connection, action
-- restriction, sourced stress-energy interface, Einstein-equation consumer,
-- and G6 section.

data G4FirstOrderGravityScopeStatus : Set where
  obligationSurfaceOnlyNoPromotion :
    G4FirstOrderGravityScopeStatus

data G4FirstOrderStructureGroupCandidate : Set where
  exceptionalE8 :
    G4FirstOrderStructureGroupCandidate
  deSitterSO23 :
    G4FirstOrderStructureGroupCandidate
  antiDeSitterSO32 :
    G4FirstOrderStructureGroupCandidate
  poincareISO13 :
    G4FirstOrderStructureGroupCandidate
  scopedFirstOrderSubstitute :
    G4FirstOrderStructureGroupCandidate

data G4FirstOrderMissingField : Set where
  missingStructureGroupTheorem :
    G4FirstOrderMissingField

  missingVierbeinCarrier :
    G4FirstOrderMissingField

  missingSpinConnectionCarrier :
    G4FirstOrderMissingField

  missingCurvatureTwoForm :
    G4FirstOrderMissingField

  missingPalatiniBFActionRestriction :
    G4FirstOrderMissingField

  missingMacDowellMansouriBreakingOrScopedSubstitute :
    G4FirstOrderMissingField

  missingBFMacDowellMansouriActionEquivalence :
    G4FirstOrderMissingField

  missingCouplingEmbeddingIndexCaveat :
    G4FirstOrderMissingField

  missingW4StressEnergySource :
    G4FirstOrderMissingField

  missingEinsteinEquationConsumer :
    G4FirstOrderMissingField

  missingFirstOrderSpinePreservationSection :
    G4FirstOrderMissingField

data G4FirstOrderObstructionStatus : Set where
  firstMissingObligationOnlyNoNegation :
    G4FirstOrderObstructionStatus

data GRFiniteRClosureTheoremTargetStatus : Set where
  closureTheoremTargetObligationOnlyNoPromotion :
    GRFiniteRClosureTheoremTargetStatus

record GRFiniteRKernelNamedObligations : Set where
  field
    finiteRGeometryObligation :
      String

    finiteRBianchiObligation :
      String

    finiteRMatterCouplingObligation :
      String

    stressEnergyConservationObligation :
      String

    firstOrderEinsteinTargetObligation :
      String

    namedObligationBoundary :
      List String

record G4CurrentGRInputs : Setω where
  field
    knownLimitsGRBridge :
      GR.KnownLimitsGRBridgeTheorem

    partialGRQFTConsumer :
      GRQFT.GRQFTPartialConsumerReceipt

    einsteinEquationCandidate :
      EEC.EinsteinEquationCandidateObligationSurface

    w4StressEnergyInternalBridge :
      W4SE.W4MatterStressEnergyAdapterObstruction

    inhabitedGRFacingFields :
      List String

    firstOrderBoundaries :
      List String

canonicalG4CurrentGRInputs :
  G4CurrentGRInputs
canonicalG4CurrentGRInputs =
  record
    { knownLimitsGRBridge =
        GR.canonicalKnownLimitsGRBridgeTheorem
    ; partialGRQFTConsumer =
        GRQFT.canonicalGRQFTPartialConsumerReceipt
    ; einsteinEquationCandidate =
        EEC.canonicalEinsteinEquationCandidateObligationSurface
    ; w4StressEnergyInternalBridge =
        W4SE.canonicalW4MatterStressEnergyAdapterObstruction
    ; inhabitedGRFacingFields =
        "KnownLimitsGRBridgeTheorem provides the current GR-like known-limits adapter surface"
        ∷ "GRQFTPartialConsumerReceipt inhabits only internally adaptable carrier fields and explicitly leaves stress-energy, curvature law, Einstein equation law, and interaction closure gated"
        ∷ "EinsteinEquationCandidate records the sourced discrete Einstein-equation obligation shape"
        ∷ "W4MatterStressEnergyMDLInternalBridge records an internal MDL stress-energy-shaped bridge but blocks physical-unit promotion"
        ∷ []
    ; firstOrderBoundaries =
        "The current known-limits GR route does not select E8, SO(2,3), SO(3,2), ISO(1,3), or an equivalent first-order structure group"
        ∷ "The current route does not construct a vierbein/spin-connection first-order pair"
        ∷ "The current route does not restrict a spine action to Palatini, BF, or MacDowell-Mansouri gravity"
        ∷ "The current route does not prove BF/MacDowell-Mansouri action equivalence or discharge coupling and embedding-index caveats"
        ∷ "The current route does not turn W4 stress-energy into a sourced Einstein-equation consumer"
        ∷ []
    }

record G4FirstOrderGeometryObligations
  (inputs : G4CurrentGRInputs) : Setω where
  field
    StructureGroupCarrier :
      Set

    VierbeinCarrier :
      Set

    SpinConnectionCarrier :
      Set

    CurvatureTwoFormCarrier :
      Set

    FirstOrderActionCarrier :
      Set

    BFActionCarrier :
      Set

    MacDowellMansouriActionCarrier :
      Set

    CouplingCarrier :
      Set

    EmbeddingIndexCarrier :
      Set

    FirstOrderEquationCarrier :
      Set

    selectedStructureGroup :
      StructureGroupCarrier

    selectedStructureGroupCandidate :
      G4FirstOrderStructureGroupCandidate

    structureGroupAdmissibleForFirstOrderGravity :
      StructureGroupCarrier →
      Set

    selectedStructureGroupAdmissible :
      structureGroupAdmissibleForFirstOrderGravity
        selectedStructureGroup

    vierbeinFromSpine :
      StructureGroupCarrier →
      VierbeinCarrier

    spinConnectionFromSpine :
      StructureGroupCarrier →
      SpinConnectionCarrier

    curvatureFromSpinConnection :
      SpinConnectionCarrier →
      CurvatureTwoFormCarrier

    palatiniBFActionRestriction :
      VierbeinCarrier →
      CurvatureTwoFormCarrier →
      FirstOrderActionCarrier

    palatiniBFActionLaw :
      FirstOrderActionCarrier →
      Set

    palatiniBFActionRestrictedFromSpine :
      palatiniBFActionLaw
        (palatiniBFActionRestriction
          (vierbeinFromSpine selectedStructureGroup)
          (curvatureFromSpinConnection
            (spinConnectionFromSpine selectedStructureGroup)))

    macDowellMansouriBreakingOrScopedSubstitute :
      StructureGroupCarrier →
      FirstOrderActionCarrier →
      Set

    macDowellMansouriRouteAdmissible :
      macDowellMansouriBreakingOrScopedSubstitute
        selectedStructureGroup
        (palatiniBFActionRestriction
          (vierbeinFromSpine selectedStructureGroup)
          (curvatureFromSpinConnection
            (spinConnectionFromSpine selectedStructureGroup)))

    bfActionFromFirstOrderRestriction :
      FirstOrderActionCarrier →
      BFActionCarrier

    macDowellMansouriActionFromBreaking :
      StructureGroupCarrier →
      FirstOrderActionCarrier →
      MacDowellMansouriActionCarrier

    bfMacDowellMansouriActionEquivalenceLaw :
      BFActionCarrier →
      MacDowellMansouriActionCarrier →
      Set

    bfMacDowellMansouriActionEquivalent :
      bfMacDowellMansouriActionEquivalenceLaw
        (bfActionFromFirstOrderRestriction
          (palatiniBFActionRestriction
            (vierbeinFromSpine selectedStructureGroup)
            (curvatureFromSpinConnection
              (spinConnectionFromSpine selectedStructureGroup))))
        (macDowellMansouriActionFromBreaking
          selectedStructureGroup
          (palatiniBFActionRestriction
            (vierbeinFromSpine selectedStructureGroup)
            (curvatureFromSpinConnection
              (spinConnectionFromSpine selectedStructureGroup))))

    couplingForEmbeddingIndex :
      StructureGroupCarrier →
      EmbeddingIndexCarrier →
      CouplingCarrier

    couplingEmbeddingIndexCaveatLaw :
      StructureGroupCarrier →
      EmbeddingIndexCarrier →
      CouplingCarrier →
      Set

    couplingEmbeddingIndexCaveatDischarged :
      (embeddingIndex : EmbeddingIndexCarrier) →
      couplingEmbeddingIndexCaveatLaw
        selectedStructureGroup
        embeddingIndex
        (couplingForEmbeddingIndex selectedStructureGroup embeddingIndex)

record G4FirstOrderSourcedEinsteinObligations
  (inputs : G4CurrentGRInputs) : Setω where
  field
    MatterStressEnergyCarrier :
      Set

    CurvatureCarrier :
      Set

    EinsteinEquationCarrier :
      Set

    stressEnergyFromW4 :
      W4SE.InternalStressEnergyDiagonal →
      MatterStressEnergyCarrier

    curvatureFromFirstOrderGeometry :
      Set →
      CurvatureCarrier

    einsteinEquationConsumer :
      MatterStressEnergyCarrier →
      CurvatureCarrier →
      EinsteinEquationCarrier

    sourcedEinsteinEquationLaw :
      EinsteinEquationCarrier →
      Set

    sourcedEinsteinEquationAtConsumer :
      (internalStressEnergy : W4SE.InternalStressEnergyDiagonal) →
      (firstOrderGeometry : Set) →
      sourcedEinsteinEquationLaw
        (einsteinEquationConsumer
          (stressEnergyFromW4 internalStressEnergy)
          (curvatureFromFirstOrderGeometry firstOrderGeometry))

    stressEnergyBoundary :
      List String

record G4FirstOrderSpinePreservationObligations : Setω where
  field
    SpineCarrier :
      Set

    GRFirstOrderLaneCarrier :
      Set

    embedFirstOrderGRInSpine :
      GRFirstOrderLaneCarrier →
      SpineCarrier

    recoverFirstOrderGRFromSpine :
      SpineCarrier →
      GRFirstOrderLaneCarrier

    firstOrderGRSpineSection :
      (spine : SpineCarrier) →
      embedFirstOrderGRInSpine (recoverFirstOrderGRFromSpine spine) ≡ spine

    g6SectionDependency :
      String

    spinePreservationBoundary :
      List String

record G4FirstOrderGravityObstructionCertificate : Set where
  field
    missingField :
      G4FirstOrderMissingField

    obstructionStatus :
      G4FirstOrderObstructionStatus

    requiredTheoremOrReceipt :
      String

    whyNoNegationProof :
      String

    nextEvidence :
      String

    boundary :
      String

structureGroupCertificate :
  G4FirstOrderGravityObstructionCertificate
structureGroupCertificate =
  record
    { missingField =
        missingStructureGroupTheorem
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "structure group theorem selecting E8, SO(2,3), SO(3,2), ISO(1,3), or a scoped first-order substitute"
    ; whyNoNegationProof =
        "The current scope has not fixed a failed first-order structure group; it only records that no admissible selection theorem is present"
    ; nextEvidence =
        "Provide a structure-group admissibility theorem for the first-order gravity route"
    ; boundary =
        "Obligation certificate only; no G4 theorem promotion"
    }

firstOrderActionRestrictionCertificate :
  G4FirstOrderGravityObstructionCertificate
firstOrderActionRestrictionCertificate =
  record
    { missingField =
        missingPalatiniBFActionRestriction
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "Palatini/BF/MacDowell-Mansouri action restriction from the spine action"
    ; whyNoNegationProof =
        "The current F^2 curvature-norm route is known to be insufficient for an Einstein-Hilbert R action, but no concrete first-order restriction candidate has been rejected"
    ; nextEvidence =
        "Supply the first-order action carrier and prove that the spine action restricts to the Palatini/BF/MacDowell-Mansouri form"
    ; boundary =
        "Obligation certificate only; no Einstein equation theorem"
    }

bfMacDowellMansouriEquivalenceCertificate :
  G4FirstOrderGravityObstructionCertificate
bfMacDowellMansouriEquivalenceCertificate =
  record
    { missingField =
        missingBFMacDowellMansouriActionEquivalence
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "equivalence law between the BF first-order action presentation and the MacDowell-Mansouri broken-symmetry action presentation"
    ; whyNoNegationProof =
        "The current route has not supplied either accepted first-order action presentation, so no failed equivalence proof can be exhibited"
    ; nextEvidence =
        "Supply BF and MacDowell-Mansouri action carriers and prove their equivalence for the selected structure group"
    ; boundary =
        "Obligation certificate only; no G4 theorem promotion"
    }

couplingEmbeddingIndexCaveatCertificate :
  G4FirstOrderGravityObstructionCertificate
couplingEmbeddingIndexCaveatCertificate =
  record
    { missingField =
        missingCouplingEmbeddingIndexCaveat
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "coupling normalization and embedding-index caveat for the chosen structure-group embedding"
    ; whyNoNegationProof =
        "No accepted structure-group embedding, embedding index, or coupling normalization has been supplied"
    ; nextEvidence =
        "Provide the embedding-index carrier and coupling law before claiming physical normalization of the first-order action"
    ; boundary =
        "Obligation certificate only; no coupling normalization or G4 theorem promotion"
    }

stressEnergySourceCertificate :
  G4FirstOrderGravityObstructionCertificate
stressEnergySourceCertificate =
  record
    { missingField =
        missingW4StressEnergySource
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "authority-backed W4 stress-energy source, not only the internal MDL stress-energy-shaped bridge"
    ; whyNoNegationProof =
        "W4MatterStressEnergyMDLInternalBridge deliberately blocks physical-unit and covariant-conservation promotion"
    ; nextEvidence =
        "Provide W4 physical-unit authority and stress-energy source binding before sourcing the Einstein-equation consumer"
    ; boundary =
        "Obligation certificate only; no W4 or G4 promotion"
    }

einsteinEquationConsumerCertificate :
  G4FirstOrderGravityObstructionCertificate
einsteinEquationConsumerCertificate =
  record
    { missingField =
        missingEinsteinEquationConsumer
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "sourced Einstein-equation consumer over first-order curvature and W4 stress-energy"
    ; whyNoNegationProof =
        "EinsteinEquationCandidate records the consumer shape and W4 dependency queue but does not supply the sourced law"
    ; nextEvidence =
        "Supply the sourced Einstein-equation law after structure group, first-order action, and stress-energy obligations are discharged"
    ; boundary =
        "Obligation certificate only; no GRQFT closure receipt"
    }

firstOrderSpineSectionCertificate :
  G4FirstOrderGravityObstructionCertificate
firstOrderSpineSectionCertificate =
  record
    { missingField =
        missingFirstOrderSpinePreservationSection
    ; obstructionStatus =
        firstMissingObligationOnlyNoNegation
    ; requiredTheoremOrReceipt =
        "first-order GR lane carrier, embedding/recovery maps, and G6 section-GR proof"
    ; whyNoNegationProof =
        "A real obstruction would require a concrete failed first-order GR lane candidate; this scope only records the missing section field"
    ; nextEvidence =
        "Provide the G6 section-GR compatible first-order GR spine preservation proof"
    ; boundary =
        "Obligation certificate only; no G4 or G6 promotion"
    }

canonicalG4FirstOrderGravityObstructionCertificates :
  List G4FirstOrderGravityObstructionCertificate
canonicalG4FirstOrderGravityObstructionCertificates =
  structureGroupCertificate
  ∷ firstOrderActionRestrictionCertificate
  ∷ bfMacDowellMansouriEquivalenceCertificate
  ∷ couplingEmbeddingIndexCaveatCertificate
  ∷ stressEnergySourceCertificate
  ∷ einsteinEquationConsumerCertificate
  ∷ firstOrderSpineSectionCertificate
  ∷ []

-- Obligation postulates.  These are intentionally named as obligations rather
-- than theorem witnesses; they do not promote G4.
postulate
  obligationFirstOrderGeometryFields :
    G4FirstOrderGeometryObligations canonicalG4CurrentGRInputs

  obligationFirstOrderSourcedEinsteinFields :
    G4FirstOrderSourcedEinsteinObligations canonicalG4CurrentGRInputs

  obligationFirstOrderSpinePreservationFields :
    G4FirstOrderSpinePreservationObligations

record GRFirstOrderGravityScope : Setω where
  field
    status :
      G4FirstOrderGravityScopeStatus

    currentGRInputs :
      G4CurrentGRInputs

    firstOrderGeometryObligations :
      G4FirstOrderGeometryObligations currentGRInputs

    sourcedEinsteinObligations :
      G4FirstOrderSourcedEinsteinObligations currentGRInputs

    spinePreservationObligations :
      G4FirstOrderSpinePreservationObligations

    missingFields :
      List G4FirstOrderMissingField

    obstructionCertificates :
      List G4FirstOrderGravityObstructionCertificate

    fSquaredVersusRBoundary :
      List String

    noPromotionBoundary :
      List String

canonicalGRFirstOrderGravityScope :
  GRFirstOrderGravityScope
canonicalGRFirstOrderGravityScope =
  record
    { status =
        obligationSurfaceOnlyNoPromotion
    ; currentGRInputs =
        canonicalG4CurrentGRInputs
    ; firstOrderGeometryObligations =
        obligationFirstOrderGeometryFields
    ; sourcedEinsteinObligations =
        obligationFirstOrderSourcedEinsteinFields
    ; spinePreservationObligations =
        obligationFirstOrderSpinePreservationFields
    ; missingFields =
        missingStructureGroupTheorem
        ∷ missingVierbeinCarrier
        ∷ missingSpinConnectionCarrier
        ∷ missingCurvatureTwoForm
        ∷ missingPalatiniBFActionRestriction
        ∷ missingMacDowellMansouriBreakingOrScopedSubstitute
        ∷ missingBFMacDowellMansouriActionEquivalence
        ∷ missingCouplingEmbeddingIndexCaveat
        ∷ missingW4StressEnergySource
        ∷ missingEinsteinEquationConsumer
        ∷ missingFirstOrderSpinePreservationSection
        ∷ []
    ; obstructionCertificates =
        canonicalG4FirstOrderGravityObstructionCertificates
    ; fSquaredVersusRBoundary =
        "A curvature-norm/Yang-Mills F^2 route yields a quadratic curvature invariant, not the Einstein-Hilbert R action"
        ∷ "The first-order route must supply a vierbein/spin-connection action whose restriction is Palatini, BF, or MacDowell-Mansouri shaped"
        ∷ "The route must also prove BF/MacDowell-Mansouri action equivalence and discharge coupling and embedding-index caveats for the selected structure-group embedding"
        ∷ "This module records that route as obligations; it does not resolve the mismatch"
        ∷ []
    ; noPromotionBoundary =
        "This scope does not construct a G4 GR theorem or Einstein equation theorem"
        ∷ "This scope does not select an accepted first-order structure group, including E8 or SO(2,3)"
        ∷ "This scope does not construct vierbein, spin connection, curvature, or first-order action restriction proofs"
        ∷ "This scope does not construct BF/MacDowell-Mansouri equivalence, coupling normalization, or embedding-index discharge proofs"
        ∷ "This scope does not promote the internal MDL stress-energy bridge to authority-backed physical stress-energy"
        ∷ "This scope does not construct GRQFTClosurePromotionReceipt"
        ∷ "This scope does not satisfy the G6 section-GR dependency"
        ∷ []
    }

record GRFiniteRSurfaceToBridgeLaw
  (surface : GRFirstOrderGravityScope) : Setω where
  field
    firstOrderGeometryBridgeLaw :
      G4FirstOrderGeometryObligations
        (GRFirstOrderGravityScope.currentGRInputs surface)

    sourcedEinsteinBridgeLaw :
      G4FirstOrderSourcedEinsteinObligations
        (GRFirstOrderGravityScope.currentGRInputs surface)

    spinePreservationBridgeLaw :
      G4FirstOrderSpinePreservationObligations

    namedKernelObligations :
      GRFiniteRKernelNamedObligations

    bridgeLawBoundary :
      List String

record GRFiniteRClosureTheoremTarget
  (surface : GRFirstOrderGravityScope)
  (bridgeLaw : GRFiniteRSurfaceToBridgeLaw surface) : Setω where
  field
    targetStatus :
      GRFiniteRClosureTheoremTargetStatus

    targetTheoremName :
      String

    requiredBridgeLaw :
      GRFiniteRSurfaceToBridgeLaw surface

    remainingMissingFields :
      List G4FirstOrderMissingField

    closureTargetBoundary :
      List String

record GRFiniteRTheoremKernel : Setω where
  field
    surface :
      GRFirstOrderGravityScope

    bridgeLaw :
      GRFiniteRSurfaceToBridgeLaw surface

    closureTheoremTarget :
      GRFiniteRClosureTheoremTarget surface bridgeLaw

    kernelBoundary :
      List String

canonicalGRFiniteRSurfaceToBridgeLaw :
  GRFiniteRSurfaceToBridgeLaw canonicalGRFirstOrderGravityScope
canonicalGRFiniteRSurfaceToBridgeLaw =
  record
    { firstOrderGeometryBridgeLaw =
        obligationFirstOrderGeometryFields
    ; sourcedEinsteinBridgeLaw =
        obligationFirstOrderSourcedEinsteinFields
    ; spinePreservationBridgeLaw =
        obligationFirstOrderSpinePreservationFields
    ; namedKernelObligations =
        record
          { finiteRGeometryObligation =
              "supply finite-r first-order geometry: structure group, vierbein, spin connection, curvature two-form, and action restriction"
          ; finiteRBianchiObligation =
              "prove the finite-r Bianchi identity or scoped discrete substitute for the selected curvature carrier"
          ; finiteRMatterCouplingObligation =
              "couple finite-r curvature to an authority-backed matter stress-energy source through the sourced Einstein consumer"
          ; stressEnergyConservationObligation =
              "provide the covariant-conservation/compatibility law tying W4 stress-energy to the finite-r Einstein equation target"
          ; firstOrderEinsteinTargetObligation =
              "derive the sourced first-order Einstein equation target from the geometry and matter-coupling bridge laws"
          ; namedObligationBoundary =
              "These named obligations are route labels over the existing first-order geometry and sourced-Einstein obligation records"
              ∷ "They do not prove finite-r Bianchi, matter coupling, conservation, or Einstein-equation closure"
              ∷ []
          }
    ; bridgeLawBoundary =
        "surface -> bridge law: canonical GR scope inputs are routed to finite-r first-order geometry, Bianchi, matter-coupling, sourced-Einstein, and spine-preservation obligations"
        ∷ "The bridge law is obligation-backed only; it does not construct GR finite-r closure or an Einstein equation theorem"
        ∷ []
    }

canonicalGRFiniteRClosureTheoremTarget :
  GRFiniteRClosureTheoremTarget
    canonicalGRFirstOrderGravityScope
    canonicalGRFiniteRSurfaceToBridgeLaw
canonicalGRFiniteRClosureTheoremTarget =
  record
    { targetStatus =
        closureTheoremTargetObligationOnlyNoPromotion
    ; targetTheoremName =
        "GRFiniteRFirstOrderClosureTheorem"
    ; requiredBridgeLaw =
        canonicalGRFiniteRSurfaceToBridgeLaw
    ; remainingMissingFields =
        GRFirstOrderGravityScope.missingFields
          canonicalGRFirstOrderGravityScope
    ; closureTargetBoundary =
        "closure theorem target: derive finite-r first-order GR closure from Bianchi and matter-coupling bridge laws"
        ∷ "The target remains uninhabited as a theorem; this record only names the target and its required bridge-law packet"
        ∷ "G6 section-GR and GRQFT promotion remain outside this target until their receipt surfaces are actually supplied"
        ∷ []
    }

canonicalGRFiniteRTheoremKernel :
  GRFiniteRTheoremKernel
canonicalGRFiniteRTheoremKernel =
  record
    { surface =
        canonicalGRFirstOrderGravityScope
    ; bridgeLaw =
        canonicalGRFiniteRSurfaceToBridgeLaw
    ; closureTheoremTarget =
        canonicalGRFiniteRClosureTheoremTarget
    ; kernelBoundary =
        "GR theorem-kernel route: surface -> bridge law -> closure theorem target"
        ∷ "The kernel is a typed obligation packet and does not promote GR finite-r closure"
        ∷ []
    }

data GRFiniteRW4BianchiMatterReadiness : Set where
  blockedBeforeW4CalibrationAndFiniteRBianchi :
    GRFiniteRW4BianchiMatterReadiness

data GRFiniteRW4BianchiMatterMissingField : Set where
  missingW4MatterStressEnergyInterfaceReceipt :
    GRFiniteRW4BianchiMatterMissingField

  missingFiniteRGeometrySelection :
    GRFiniteRW4BianchiMatterMissingField

  missingFiniteRBianchiLaw :
    GRFiniteRW4BianchiMatterMissingField

  missingFiniteRStressEnergyCompatibility :
    GRFiniteRW4BianchiMatterMissingField

  missingFiniteRSourcedEinsteinLaw :
    GRFiniteRW4BianchiMatterMissingField

canonicalGRFiniteRW4BianchiMatterMissingFields :
  List GRFiniteRW4BianchiMatterMissingField
canonicalGRFiniteRW4BianchiMatterMissingFields =
  missingW4MatterStressEnergyInterfaceReceipt
  ∷ missingFiniteRGeometrySelection
  ∷ missingFiniteRBianchiLaw
  ∷ missingFiniteRStressEnergyCompatibility
  ∷ missingFiniteRSourcedEinsteinLaw
  ∷ []

record GRFiniteRW4BianchiMatterTheoremObligation
  (receipt : EEC.W4MatterStressEnergyInterfaceReceipt) : Setω where
  field
    FiniteRGeometryCarrier :
      Set

    FiniteRCurvatureCarrier :
      Set

    finiteRCurvatureFromGeometry :
      FiniteRGeometryCarrier →
      FiniteRCurvatureCarrier

    finiteRBianchiLaw :
      FiniteRCurvatureCarrier →
      Set

    finiteRBianchiAtCurvature :
      (geometry : FiniteRGeometryCarrier) →
      finiteRBianchiLaw
        (finiteRCurvatureFromGeometry geometry)

    FiniteRStressEnergyCarrier :
      Set

    w4StressEnergyToFiniteR :
      EEC.W4StressEnergyConsumerCarrier receipt →
      FiniteRStressEnergyCarrier

    finiteRStressEnergyCompatibilityLaw :
      FiniteRStressEnergyCarrier →
      FiniteRCurvatureCarrier →
      Set

    finiteRStressEnergyCompatible :
      (w4StressEnergy : EEC.W4StressEnergyConsumerCarrier receipt) →
      (geometry : FiniteRGeometryCarrier) →
      finiteRStressEnergyCompatibilityLaw
        (w4StressEnergyToFiniteR w4StressEnergy)
        (finiteRCurvatureFromGeometry geometry)

    FiniteREinsteinEquationCarrier :
      Set

    finiteREinsteinConsumer :
      FiniteRStressEnergyCarrier →
      FiniteRCurvatureCarrier →
      FiniteREinsteinEquationCarrier

    finiteRSourcedEinsteinLaw :
      FiniteREinsteinEquationCarrier →
      Set

    finiteRSourcedEinsteinAtConsumer :
      (w4StressEnergy : EEC.W4StressEnergyConsumerCarrier receipt) →
      (geometry : FiniteRGeometryCarrier) →
      finiteRSourcedEinsteinLaw
        (finiteREinsteinConsumer
          (w4StressEnergyToFiniteR w4StressEnergy)
          (finiteRCurvatureFromGeometry geometry))

    theoremBoundary :
      List String

record GRFiniteRW4BianchiMatterObligationSurface : Setω where
  field
    readiness :
      GRFiniteRW4BianchiMatterReadiness

    finiteRKernel :
      GRFiniteRTheoremKernel

    einsteinCandidate :
      EEC.EinsteinEquationCandidateObligationSurface

    w4MatterStressEnergyDiagnostic :
      EEC.W4MatterStressEnergyInterfaceDiagnostic

    w4FirstMissing :
      EEC.W4MatterStressEnergyInterfaceMissingField

    w4FirstMissingIsAnchor :
      w4FirstMissing
      ≡
      EEC.missingW4AnchorArtifactReceiptForMatterStress

    missingFields :
      List GRFiniteRW4BianchiMatterMissingField

    missingFieldsAreCanonical :
      missingFields
      ≡
      canonicalGRFiniteRW4BianchiMatterMissingFields

    theoremObligationName :
      String

    requiredReceiptName :
      String

    finiteRBianchiObligationName :
      String

    finiteRStressEnergyCompatibilityName :
      String

    finiteRSourcedEinsteinLawName :
      String

    w4ReceiptImpossibleHere :
      EEC.W4MatterStressEnergyInterfaceReceipt →
      ⊥

    acceptedDYAdequacyStillImpossibleHere :
      EEC.W4MatterStressEnergyInterfaceReceipt →
      ⊥

    obligationBoundary :
      List String

    nonPromotionBoundary :
      List String

canonicalGRFiniteRW4BianchiMatterObligationSurface :
  GRFiniteRW4BianchiMatterObligationSurface
canonicalGRFiniteRW4BianchiMatterObligationSurface =
  record
    { readiness =
        blockedBeforeW4CalibrationAndFiniteRBianchi
    ; finiteRKernel =
        canonicalGRFiniteRTheoremKernel
    ; einsteinCandidate =
        EEC.canonicalEinsteinEquationCandidateObligationSurface
    ; w4MatterStressEnergyDiagnostic =
        EEC.canonicalW4MatterStressEnergyInterfaceDiagnostic
    ; w4FirstMissing =
        EEC.W4MatterStressEnergyInterfaceDiagnostic.firstMissing
          EEC.canonicalW4MatterStressEnergyInterfaceDiagnostic
    ; w4FirstMissingIsAnchor =
        EEC.W4MatterStressEnergyInterfaceDiagnostic.firstMissingIsW4AnchorArtifactReceipt
          EEC.canonicalW4MatterStressEnergyInterfaceDiagnostic
    ; missingFields =
        canonicalGRFiniteRW4BianchiMatterMissingFields
    ; missingFieldsAreCanonical =
        refl
    ; theoremObligationName =
        "GRFiniteRW4BianchiMatterTheoremObligation"
    ; requiredReceiptName =
        "DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
    ; finiteRBianchiObligationName =
        "finiteRBianchiAtCurvature"
    ; finiteRStressEnergyCompatibilityName =
        "finiteRStressEnergyCompatible"
    ; finiteRSourcedEinsteinLawName =
        "finiteRSourcedEinsteinAtConsumer"
    ; w4ReceiptImpossibleHere =
        EEC.w4MatterStressEnergyInterfaceReceiptImpossibleHere
    ; acceptedDYAdequacyStillImpossibleHere =
        EEC.w4MatterStressEnergyInterfaceReceiptImpossibleWithoutAcceptedDYAdequacy
    ; obligationBoundary =
        "The theorem obligation is parameterized by a future W4MatterStressEnergyInterfaceReceipt; this module does not construct that receipt"
        ∷ "The finite-r Bianchi law is required for the selected curvature carrier before any finite-r GR closure claim"
        ∷ "The W4 stress-energy consumer must be compatible with the same finite-r curvature carrier before the sourced Einstein law can be consumed"
        ∷ "The sourced Einstein law is downstream of both finite-r Bianchi and W4 matter/stress-energy compatibility"
        ∷ []
    ; nonPromotionBoundary =
        "This surface does not construct Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "This surface does not construct AcceptedDYPDFBackedW4Adequacy"
        ∷ "This surface does not construct W4MatterStressEnergyInterfaceReceipt"
        ∷ "This surface does not prove finite-r Bianchi"
        ∷ "This surface does not prove G_mu_nu = 8pi T_mu_nu"
        ∷ "This surface does not promote GR, G4, G6, W4, W5, or GR/QFT closure"
        ∷ []
    }
