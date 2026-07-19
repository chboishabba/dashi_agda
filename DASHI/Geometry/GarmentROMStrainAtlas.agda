module DASHI.Geometry.GarmentROMStrainAtlas where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Garment ROM strain/rub atlas.
--
-- This is the formal boundary for the proposed "Ken-doll + skintight suit"
-- workflow:
--
--   rigged body -> anatomically admissible pose cover -> suit deformation
--   -> contact/friction observation -> pose-wise atlas -> aggregate atlas.
--
-- The module deliberately does not identify geometric stretch with material
-- stress, contact with pressure, or accumulated slip with human discomfort.
-- Those require constitutive calibration and empirical validation receipts.

------------------------------------------------------------------------
-- Pipeline vocabulary.

data GarmentROMStage : Set where
  neutralBodyStage : GarmentROMStage
  rigAttachmentStage : GarmentROMStage
  anatomicalROMStage : GarmentROMStage
  poseCoverStage : GarmentROMStage
  clothSolveStage : GarmentROMStage
  contactSolveStage : GarmentROMStage
  patchMetricStage : GarmentROMStage
  atlasAggregationStage : GarmentROMStage
  empiricalCalibrationStage : GarmentROMStage

data GarmentMetricKind : Set where
  warpStretchMetric : GarmentMetricKind
  weftStretchMetric : GarmentMetricKind
  areaStretchMetric : GarmentMetricKind
  shearMetric : GarmentMetricKind
  bendMetric : GarmentMetricKind
  contactMetric : GarmentMetricKind
  tangentialSlipMetric : GarmentMetricKind
  frictionWorkMetric : GarmentMetricKind
  residenceMetric : GarmentMetricKind
  seamLoadMetric : GarmentMetricKind

data GarmentNonPromotionGuard : Set where
  NoGeometricStretchEqualsStressClaim : GarmentNonPromotionGuard
  NoContactEqualsPressureClaim : GarmentNonPromotionGuard
  NoSlipEqualsChafingClaim : GarmentNonPromotionGuard
  NoRigidBodyEqualsLivingTissueClaim : GarmentNonPromotionGuard
  NoIndependentJointSamplingEqualsHumanMotionClaim : GarmentNonPromotionGuard
  NoFinitePoseCoverEqualsFullROMClaim : GarmentNonPromotionGuard
  NoUncalibratedSolverEqualsPhysicalGarmentClaim : GarmentNonPromotionGuard
  NoComfortOrInjuryAuthorityClaim : GarmentNonPromotionGuard

defaultGarmentROMStages : List GarmentROMStage
defaultGarmentROMStages =
  neutralBodyStage
  ∷ rigAttachmentStage
  ∷ anatomicalROMStage
  ∷ poseCoverStage
  ∷ clothSolveStage
  ∷ contactSolveStage
  ∷ patchMetricStage
  ∷ atlasAggregationStage
  ∷ empiricalCalibrationStage
  ∷ []

defaultGarmentMetricKinds : List GarmentMetricKind
defaultGarmentMetricKinds =
  warpStretchMetric
  ∷ weftStretchMetric
  ∷ areaStretchMetric
  ∷ shearMetric
  ∷ bendMetric
  ∷ contactMetric
  ∷ tangentialSlipMetric
  ∷ frictionWorkMetric
  ∷ residenceMetric
  ∷ seamLoadMetric
  ∷ []

defaultGarmentNonPromotionGuards : List GarmentNonPromotionGuard
defaultGarmentNonPromotionGuards =
  NoGeometricStretchEqualsStressClaim
  ∷ NoContactEqualsPressureClaim
  ∷ NoSlipEqualsChafingClaim
  ∷ NoRigidBodyEqualsLivingTissueClaim
  ∷ NoIndependentJointSamplingEqualsHumanMotionClaim
  ∷ NoFinitePoseCoverEqualsFullROMClaim
  ∷ NoUncalibratedSolverEqualsPhysicalGarmentClaim
  ∷ NoComfortOrInjuryAuthorityClaim
  ∷ []

------------------------------------------------------------------------
-- Rig and anatomical range-of-motion surface.
--
-- JointState is intentionally abstract.  It may be Euler angles, quaternions,
-- exponential coordinates, or a learned pose latent.  ROMAdmissible carries
-- coupled anatomical admissibility, so this formalism does not assume that
-- independent per-joint box constraints describe human motion.

record RiggedBodySurface : Set₁ where
  field
    Joint : Set
    JointState : Joint → Set
    Pose : Set
    NeutralPose : Pose

    jointStateAt :
      Pose →
      (joint : Joint) →
      JointState joint

    BodyPoint : Set
    BodyPosition : Pose → BodyPoint → Set

    ROMAdmissible : Pose → Set
    selfCollisionFree : Pose → Set
    supportAdmissible : Pose → Set

    rigReading : String

open RiggedBodySurface public

record AdmissibleBodyPose
    (body : RiggedBodySurface) : Set where
  field
    pose : Pose body
    romWitness : ROMAdmissible body pose
    collisionWitness : selfCollisionFree body pose
    supportWitness : supportAdmissible body pose

open AdmissibleBodyPose public

------------------------------------------------------------------------
-- Pose cover.
--
-- A finite or generated pose set is not silently equated with the whole ROM.
-- Coverage is represented by an explicit relation and a coverage receipt.

record ROMPoseCover
    (body : RiggedBodySurface) : Set₁ where
  field
    Sample : Set
    samplePose : Sample → AdmissibleBodyPose body

    PoseDistance : Pose body → Pose body → Set
    CoverRadius : Set

    coveredBy :
      Pose body →
      Sample →
      Set

    coveredBySound :
      (target : Pose body) →
      (sample : Sample) →
      coveredBy target sample →
      PoseDistance target (pose (samplePose sample))

    fullAdmissibleCoverage : Set
    coverageReceipt : fullAdmissibleCoverage

    coupledSamplingUsed : Bool
    coupledSamplingUsedIsTrue : coupledSamplingUsed ≡ true

    coverReading : String

open ROMPoseCover public

------------------------------------------------------------------------
-- Suit shell and body attachment.
--
-- MaterialPoint is the persistent Lagrangian identity of a patch on the suit.
-- This is the crucial anti-pathology boundary: a patch is tracked through
-- motion rather than reprojected independently at every pose.

record SkinTightGarmentSurface
    (body : RiggedBodySurface) : Set₁ where
  field
    MaterialPoint : Set
    GarmentPatch : Set
    Seam : Set

    patchOf : MaterialPoint → GarmentPatch
    seamIncident : GarmentPatch → Seam → Set

    RestPosition : MaterialPoint → Set
    restBodyAnchor : MaterialPoint → BodyPoint body

    WarpDirection : GarmentPatch → Set
    WeftDirection : GarmentPatch → Set

    MaterialClass : Set
    materialAt : GarmentPatch → MaterialClass

    EaseField : GarmentPatch → Set
    ThicknessField : GarmentPatch → Set

    persistentMaterialIdentity : Set
    attachmentReceipt : persistentMaterialIdentity

    garmentReading : String

open SkinTightGarmentSurface public

------------------------------------------------------------------------
-- Pose-wise cloth/contact solve boundary.

record GarmentPoseSolve
    {body : RiggedBodySurface}
    (garment : SkinTightGarmentSurface body)
    (admissiblePose : AdmissibleBodyPose body) : Set₁ where
  field
    DeformedPosition : MaterialPoint garment → Set

    deformationGradient : GarmentPatch garment → Set
    stretchTensor : GarmentPatch garment → Set
    bendState : GarmentPatch garment → Set

    ContactState : GarmentPatch garment → Set
    contactState :
      (patch : GarmentPatch garment) →
      ContactState patch

    TangentialSlip : GarmentPatch garment → Set
    tangentialSlip :
      (patch : GarmentPatch garment) →
      TangentialSlip patch

    SeamLoad : Seam garment → Set
    seamLoad :
      (seam : Seam garment) →
      SeamLoad seam

    bodyNonPenetration : Set
    garmentSelfCollisionFree : Set
    materialContinuity : Set
    seamContinuity : Set

    bodyNonPenetrationReceipt : bodyNonPenetration
    garmentSelfCollisionReceipt : garmentSelfCollisionFree
    materialContinuityReceipt : materialContinuity
    seamContinuityReceipt : seamContinuity

    solveReading : String

open GarmentPoseSolve public

------------------------------------------------------------------------
-- Derived metric surface.
--
-- Metrics remain typed separately.  In particular, friction work cannot be
-- manufactured from slip alone: it consumes both contact and slip channels.

record GarmentPatchMetricSurface
    {body : RiggedBodySurface}
    {garment : SkinTightGarmentSurface body}
    {admissiblePose : AdmissibleBodyPose body}
    (solve : GarmentPoseSolve garment admissiblePose) : Set₁ where
  field
    WarpStretch : GarmentPatch garment → Set
    WeftStretch : GarmentPatch garment → Set
    AreaStretch : GarmentPatch garment → Set
    Shear : GarmentPatch garment → Set
    Bend : GarmentPatch garment → Set
    ContactLoad : GarmentPatch garment → Set
    SlipMagnitude : GarmentPatch garment → Set
    FrictionWork : GarmentPatch garment → Set
    SeamLoadMagnitude : Seam garment → Set

    warpStretch :
      (patch : GarmentPatch garment) →
      WarpStretch patch

    weftStretch :
      (patch : GarmentPatch garment) →
      WeftStretch patch

    areaStretch :
      (patch : GarmentPatch garment) →
      AreaStretch patch

    shear :
      (patch : GarmentPatch garment) →
      Shear patch

    bend :
      (patch : GarmentPatch garment) →
      Bend patch

    contactLoad :
      (patch : GarmentPatch garment) →
      ContactLoad patch

    slipMagnitude :
      (patch : GarmentPatch garment) →
      SlipMagnitude patch

    frictionWork :
      (patch : GarmentPatch garment) →
      ContactState solve patch →
      TangentialSlip solve patch →
      FrictionWork patch

    seamLoadMagnitude :
      (seam : Seam garment) →
      SeamLoadMagnitude seam

    metricReading : String

open GarmentPatchMetricSurface public

------------------------------------------------------------------------
-- Pose atlas and aggregation.

record PosewiseGarmentAtlas
    {body : RiggedBodySurface}
    (garment : SkinTightGarmentSurface body)
    (cover : ROMPoseCover body) : Set₁ where
  field
    solveAt :
      (sample : Sample cover) →
      GarmentPoseSolve garment (samplePose cover sample)

    metricsAt :
      (sample : Sample cover) →
      GarmentPatchMetricSurface (solveAt sample)

    poseWeight : Sample cover → Set
    transitionAdmissible : Sample cover → Sample cover → Set

    atlasReading : String

open PosewiseGarmentAtlas public

record GarmentROMAggregateAtlas
    {body : RiggedBodySurface}
    {garment : SkinTightGarmentSurface body}
    {cover : ROMPoseCover body}
    (atlas : PosewiseGarmentAtlas garment cover) : Set₁ where
  field
    PatchAggregate : GarmentPatch garment → Set
    SeamAggregate : Seam garment → Set

    WorstCaseStretch : GarmentPatch garment → Set
    CumulativeFrictionWork : GarmentPatch garment → Set
    ContactResidence : GarmentPatch garment → Set
    WorstCaseSeamLoad : Seam garment → Set

    aggregatePatch :
      (patch : GarmentPatch garment) →
      PatchAggregate patch

    aggregateSeam :
      (seam : Seam garment) →
      SeamAggregate seam

    worstCaseStretch :
      (patch : GarmentPatch garment) →
      WorstCaseStretch patch

    cumulativeFrictionWork :
      (patch : GarmentPatch garment) →
      CumulativeFrictionWork patch

    contactResidence :
      (patch : GarmentPatch garment) →
      ContactResidence patch

    worstCaseSeamLoad :
      (seam : Seam garment) →
      WorstCaseSeamLoad seam

    maximaConsumeAllSamples : Set
    cumulativeMetricsConsumeTransitions : Set

    maximaReceipt : maximaConsumeAllSamples
    transitionReceipt : cumulativeMetricsConsumeTransitions

    aggregateReading : String

open GarmentROMAggregateAtlas public

------------------------------------------------------------------------
-- Calibration and interpretation gate.
--
-- The geometry pipeline may run without this gate, but physical stress,
-- pressure, chafing, comfort, or injury-risk interpretations may not be
-- promoted without it.

record GarmentEmpiricalCalibrationGate
    {body : RiggedBodySurface}
    {garment : SkinTightGarmentSurface body}
    {cover : ROMPoseCover body}
    {atlas : PosewiseGarmentAtlas garment cover}
    (aggregate : GarmentROMAggregateAtlas atlas) : Set₁ where
  field
    MaterialCalibrationReceipt : Set
    ContactCalibrationReceipt : Set
    FrictionCalibrationReceipt : Set
    BodyComplianceReceipt : Set
    HumanValidationReceipt : Set

    materialCalibration : MaterialCalibrationReceipt
    contactCalibration : ContactCalibrationReceipt
    frictionCalibration : FrictionCalibrationReceipt
    bodyComplianceCalibration : BodyComplianceReceipt
    humanValidation : HumanValidationReceipt

    geometricAtlasAvailable : Bool
    geometricAtlasAvailableIsTrue : geometricAtlasAvailable ≡ true

    physicalStressPromoted : Bool
    physicalPressurePromoted : Bool
    chafingRiskPromoted : Bool
    comfortAuthorityPromoted : Bool
    injuryAuthorityPromoted : Bool

    comfortAuthorityPromotedIsFalse :
      comfortAuthorityPromoted ≡ false

    injuryAuthorityPromotedIsFalse :
      injuryAuthorityPromoted ≡ false

    calibrationReading : String

open GarmentEmpiricalCalibrationGate public

------------------------------------------------------------------------
-- Top-level bridge bundle.

record GarmentROMStrainAtlasBridge : Set₁ where
  field
    body : RiggedBodySurface
    garment : SkinTightGarmentSurface body
    cover : ROMPoseCover body
    atlas : PosewiseGarmentAtlas garment cover
    aggregate : GarmentROMAggregateAtlas atlas
    calibration : GarmentEmpiricalCalibrationGate aggregate

    stages : List GarmentROMStage
    metrics : List GarmentMetricKind
    guards : List GarmentNonPromotionGuard

    stagesCanonical : stages ≡ defaultGarmentROMStages
    metricsCanonical : metrics ≡ defaultGarmentMetricKinds
    guardsCanonical : guards ≡ defaultGarmentNonPromotionGuards

    finiteCoverEqualsFullROMClaim : Bool
    uncalibratedPhysicalAuthorityClaim : Bool
    comfortOrInjuryAuthorityClaim : Bool

    finiteCoverEqualsFullROMClaimIsFalse :
      finiteCoverEqualsFullROMClaim ≡ false

    uncalibratedPhysicalAuthorityClaimIsFalse :
      uncalibratedPhysicalAuthorityClaim ≡ false

    comfortOrInjuryAuthorityClaimIsFalse :
      comfortOrInjuryAuthorityClaim ≡ false

    bridgeReading : String

open GarmentROMStrainAtlasBridge public

------------------------------------------------------------------------
-- Canonical fail-closed theorem surface.

record GarmentROMNonPromotionCertificate
    (bridge : GarmentROMStrainAtlasBridge) : Set where
  field
    guardSetPresent :
      guards bridge ≡ defaultGarmentNonPromotionGuards

    finiteCoverNotIdentifiedWithFullROM :
      finiteCoverEqualsFullROMClaim bridge ≡ false

    uncalibratedPhysicalAuthorityBlocked :
      uncalibratedPhysicalAuthorityClaim bridge ≡ false

    comfortAndInjuryAuthorityBlocked :
      comfortOrInjuryAuthorityClaim bridge ≡ false

open GarmentROMNonPromotionCertificate public

canonicalGarmentROMNonPromotionCertificate :
  (bridge : GarmentROMStrainAtlasBridge) →
  GarmentROMNonPromotionCertificate bridge
canonicalGarmentROMNonPromotionCertificate bridge =
  record
    { guardSetPresent = guardsCanonical bridge
    ; finiteCoverNotIdentifiedWithFullROM =
        finiteCoverEqualsFullROMClaimIsFalse bridge
    ; uncalibratedPhysicalAuthorityBlocked =
        uncalibratedPhysicalAuthorityClaimIsFalse bridge
    ; comfortAndInjuryAuthorityBlocked =
        comfortOrInjuryAuthorityClaimIsFalse bridge
    }
