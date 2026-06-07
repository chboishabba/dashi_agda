module DASHI.Physics.Closure.NSLeiRenTianRadialZeroModeAuthorityBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSMicrolocalDefectMassConstructionBoundary as Micro
import DASHI.Physics.Closure.NSRankOneProjectionCommutatorFormula as RankOne
import DASHI.Physics.Closure.NSSigmaNonRadialCommutatorLowerBoundTarget as Sigma
import DASHI.Physics.Closure.NSSprint163TopologicalAlignmentObstructionBoundaryReceipt as S163

------------------------------------------------------------------------
-- Lei-Ren-Tian radial zero-mode authority boundary.
--
-- External source:
--
--   Lei-Ren-Tian, arXiv:2501.08976, Corollary 1.5.
--
-- Boundary interpretation recorded here:
--
--   The great-circle vorticity-direction obstruction is treated as an
--   external authority theorem target for excluding an NS radial zero-mode
--   support scenario.  This module does not internally prove Lei-Ren-Tian,
--   does not construct the microlocal defect measure, does not close the
--   pressure bootstrap, does not prove NSCriticalResidualNonPositive, and
--   does not promote Clay Navier-Stokes.
--
-- The requested NSZeroModeSetClassificationBoundary module is not present
-- in this repository at this sprint.  This surface therefore consumes the
-- available boundary anchors:
--
--   * NSMicrolocalDefectMassConstructionBoundary;
--   * NSSprint163TopologicalAlignmentObstructionBoundaryReceipt;
--   * NSSigmaNonRadialCommutatorLowerBoundTarget;
--   * NSRankOneProjectionCommutatorFormula.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Source metadata.

leiRenTianArxivId : String
leiRenTianArxivId =
  "arXiv:2501.08976"

leiRenTianCorollary : String
leiRenTianCorollary =
  "Corollary 1.5"

leiRenTianAuthorityClaim : String
leiRenTianAuthorityClaim =
  "A singular point forces the vorticity direction set I to intersect every great circle on S^2."

leiRenTianBoundaryUse : String
leiRenTianBoundaryUse =
  "External authority boundary for radial zero-mode exclusion, not an internal DASHI proof."

data LeiRenTianSourceMetadataRow : Set where
  sourceAuthorsLeiRenTian2025 :
    LeiRenTianSourceMetadataRow
  sourceArxiv250108976 :
    LeiRenTianSourceMetadataRow
  sourceCorollaryOnePointFive :
    LeiRenTianSourceMetadataRow
  greatCircleVorticityDirectionObstruction :
    LeiRenTianSourceMetadataRow
  externalAuthorityBoundaryNotInternalProof :
    LeiRenTianSourceMetadataRow

canonicalLeiRenTianSourceMetadataRows :
  List LeiRenTianSourceMetadataRow
canonicalLeiRenTianSourceMetadataRows =
  sourceAuthorsLeiRenTian2025
  ∷ sourceArxiv250108976
  ∷ sourceCorollaryOnePointFive
  ∷ greatCircleVorticityDirectionObstruction
  ∷ externalAuthorityBoundaryNotInternalProof
  ∷ []

leiRenTianSourceMetadataRowCount : Nat
leiRenTianSourceMetadataRowCount =
  listLength canonicalLeiRenTianSourceMetadataRows

leiRenTianSourceMetadataRowCountIs5 :
  leiRenTianSourceMetadataRowCount ≡ 5
leiRenTianSourceMetadataRowCountIs5 =
  refl

------------------------------------------------------------------------
-- Zero-mode carriers.

data NSZeroModeSetCarrier : Set where
  pressureStrainDefectLaplacianZeroModeSet :
    NSZeroModeSetCarrier

data NSRadialZeroModeCarrier : Set where
  radialMaximalStrainZeroMode :
    NSZeroModeSetCarrier →
    NSRadialZeroModeCarrier

data NSTangentialZeroModeCarrier : Set where
  tangentialPressureStarvedZeroMode :
    NSZeroModeSetCarrier →
    NSTangentialZeroModeCarrier

data VorticityDirectionSetCarrier : Set where
  leiRenTianDirectionSetI :
    VorticityDirectionSetCarrier

data GreatCircleIntersectionAuthority : Set where
  intersectsEveryGreatCircleAuthority :
    VorticityDirectionSetCarrier →
    GreatCircleIntersectionAuthority

data RadialZeroModeExclusionBoundary : Set where
  radialZeroModeExcludedByGreatCircleAuthority :
    NSRadialZeroModeCarrier →
    GreatCircleIntersectionAuthority →
    RadialZeroModeExclusionBoundary

canonicalZeroModeSet : NSZeroModeSetCarrier
canonicalZeroModeSet =
  pressureStrainDefectLaplacianZeroModeSet

canonicalRadialZeroMode : NSRadialZeroModeCarrier
canonicalRadialZeroMode =
  radialMaximalStrainZeroMode canonicalZeroModeSet

canonicalTangentialZeroMode : NSTangentialZeroModeCarrier
canonicalTangentialZeroMode =
  tangentialPressureStarvedZeroMode canonicalZeroModeSet

canonicalVorticityDirectionSet : VorticityDirectionSetCarrier
canonicalVorticityDirectionSet =
  leiRenTianDirectionSetI

canonicalGreatCircleAuthority : GreatCircleIntersectionAuthority
canonicalGreatCircleAuthority =
  intersectsEveryGreatCircleAuthority canonicalVorticityDirectionSet

canonicalRadialZeroModeExclusionBoundary :
  RadialZeroModeExclusionBoundary
canonicalRadialZeroModeExclusionBoundary =
  radialZeroModeExcludedByGreatCircleAuthority
    canonicalRadialZeroMode
    canonicalGreatCircleAuthority

------------------------------------------------------------------------
-- Boundary rows and blockers.

data RadialZeroModeAuthoritySupportRow : Set where
  rankOneDefectFormulaZeroModesSupport :
    RadialZeroModeAuthoritySupportRow
  sigmaNonRadialTargetSupport :
    RadialZeroModeAuthoritySupportRow
  sprint163TopologicalAlignmentVocabularySupport :
    RadialZeroModeAuthoritySupportRow
  microlocalDefectMassBoundarySupport :
    RadialZeroModeAuthoritySupportRow
  leiRenTianGreatCircleAuthoritySupport :
    RadialZeroModeAuthoritySupportRow
  radialZeroModeExclusionTargetSupport :
    RadialZeroModeAuthoritySupportRow

canonicalRadialZeroModeAuthoritySupportRows :
  List RadialZeroModeAuthoritySupportRow
canonicalRadialZeroModeAuthoritySupportRows =
  rankOneDefectFormulaZeroModesSupport
  ∷ sigmaNonRadialTargetSupport
  ∷ sprint163TopologicalAlignmentVocabularySupport
  ∷ microlocalDefectMassBoundarySupport
  ∷ leiRenTianGreatCircleAuthoritySupport
  ∷ radialZeroModeExclusionTargetSupport
  ∷ []

radialZeroModeAuthoritySupportRowCount : Nat
radialZeroModeAuthoritySupportRowCount =
  listLength canonicalRadialZeroModeAuthoritySupportRows

radialZeroModeAuthoritySupportRowCountIs6 :
  radialZeroModeAuthoritySupportRowCount ≡ 6
radialZeroModeAuthoritySupportRowCountIs6 =
  refl

data RadialZeroModeAuthorityBlocker : Set where
  zeroModeSetClassificationModuleAbsent :
    RadialZeroModeAuthorityBlocker
  leiRenTianTheoremNotInternallyFormalized :
    RadialZeroModeAuthorityBlocker
  missingRadialZeroModeNowhereDenseProof :
    RadialZeroModeAuthorityBlocker
  missingMicrolocalMeasureSupportTransfer :
    RadialZeroModeAuthorityBlocker
  missingTangentialZeroModePressureStarvation :
    RadialZeroModeAuthorityBlocker
  missingWedgeCollapseExclusion :
    RadialZeroModeAuthorityBlocker
  missingNoZeroModeDegeneracyRidingCascade :
    RadialZeroModeAuthorityBlocker
  missingNSCriticalResidualNonPositive :
    RadialZeroModeAuthorityBlocker
  missingFullLocalDefectMonotonicity :
    RadialZeroModeAuthorityBlocker
  missingMechanismExhaustionForFullClayNS :
    RadialZeroModeAuthorityBlocker
  clayNavierStokesPromotionClosed :
    RadialZeroModeAuthorityBlocker

canonicalRadialZeroModeAuthorityBlockers :
  List RadialZeroModeAuthorityBlocker
canonicalRadialZeroModeAuthorityBlockers =
  zeroModeSetClassificationModuleAbsent
  ∷ leiRenTianTheoremNotInternallyFormalized
  ∷ missingRadialZeroModeNowhereDenseProof
  ∷ missingMicrolocalMeasureSupportTransfer
  ∷ missingTangentialZeroModePressureStarvation
  ∷ missingWedgeCollapseExclusion
  ∷ missingNoZeroModeDegeneracyRidingCascade
  ∷ missingNSCriticalResidualNonPositive
  ∷ missingFullLocalDefectMonotonicity
  ∷ missingMechanismExhaustionForFullClayNS
  ∷ clayNavierStokesPromotionClosed
  ∷ []

radialZeroModeAuthorityBlockerCount : Nat
radialZeroModeAuthorityBlockerCount =
  listLength canonicalRadialZeroModeAuthorityBlockers

radialZeroModeAuthorityBlockerCountIs11 :
  radialZeroModeAuthorityBlockerCount ≡ 11
radialZeroModeAuthorityBlockerCountIs11 =
  refl

data RadialZeroModeAuthorityStatusRow : Set where
  leiRenTianSourceMetadataRecordedStatus :
    RadialZeroModeAuthorityStatusRow
  greatCircleObstructionAuthorityBoundaryRecordedStatus :
    RadialZeroModeAuthorityStatusRow
  radialZeroModeExclusionBoundaryTypedStatus :
    RadialZeroModeAuthorityStatusRow
  internalFormalizationFalseStatus :
    RadialZeroModeAuthorityStatusRow
  microlocalMeasureFalseStatus :
    RadialZeroModeAuthorityStatusRow
  nsCriticalResidualFalseStatus :
    RadialZeroModeAuthorityStatusRow
  clayPromotionFalseStatus :
    RadialZeroModeAuthorityStatusRow

canonicalRadialZeroModeAuthorityStatusRows :
  List RadialZeroModeAuthorityStatusRow
canonicalRadialZeroModeAuthorityStatusRows =
  leiRenTianSourceMetadataRecordedStatus
  ∷ greatCircleObstructionAuthorityBoundaryRecordedStatus
  ∷ radialZeroModeExclusionBoundaryTypedStatus
  ∷ internalFormalizationFalseStatus
  ∷ microlocalMeasureFalseStatus
  ∷ nsCriticalResidualFalseStatus
  ∷ clayPromotionFalseStatus
  ∷ []

radialZeroModeAuthorityStatusRowCount : Nat
radialZeroModeAuthorityStatusRowCount =
  listLength canonicalRadialZeroModeAuthorityStatusRows

radialZeroModeAuthorityStatusRowCountIs7 :
  radialZeroModeAuthorityStatusRowCount ≡ 7
radialZeroModeAuthorityStatusRowCountIs7 =
  refl

------------------------------------------------------------------------
-- Promotion and governance guards.

LeiRenTianSourceMetadataRecorded : Bool
LeiRenTianSourceMetadataRecorded =
  true

LeiRenTianGreatCircleAuthorityBoundaryRecorded : Bool
LeiRenTianGreatCircleAuthorityBoundaryRecorded =
  true

RadialZeroModeExclusionBoundaryTyped : Bool
RadialZeroModeExclusionBoundaryTyped =
  true

RankOneDefectFormulaAnchorImported : Bool
RankOneDefectFormulaAnchorImported =
  true

SigmaNonRadialTargetAnchorImported : Bool
SigmaNonRadialTargetAnchorImported =
  true

Sprint163TopologicalAlignmentAnchorImported : Bool
Sprint163TopologicalAlignmentAnchorImported =
  true

MicrolocalDefectMassBoundaryAnchorImported : Bool
MicrolocalDefectMassBoundaryAnchorImported =
  true

LeiRenTianTheoremInternallyFormalized : Bool
LeiRenTianTheoremInternallyFormalized =
  false

RadialZeroModeInternallyExcluded : Bool
RadialZeroModeInternallyExcluded =
  false

MicrolocalDefectMassConstructed : Bool
MicrolocalDefectMassConstructed =
  false

NSCriticalResidualNonPositive : Bool
NSCriticalResidualNonPositive =
  false

FullLocalDefectMonotonicity : Bool
FullLocalDefectMonotonicity =
  false

MechanismExhaustionForFullClayNS : Bool
MechanismExhaustionForFullClayNS =
  false

full_clay_ns_solved : Bool
full_clay_ns_solved =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

leiRenTianSourceMetadataRecordedIsTrue :
  LeiRenTianSourceMetadataRecorded ≡ true
leiRenTianSourceMetadataRecordedIsTrue =
  refl

leiRenTianGreatCircleAuthorityBoundaryRecordedIsTrue :
  LeiRenTianGreatCircleAuthorityBoundaryRecorded ≡ true
leiRenTianGreatCircleAuthorityBoundaryRecordedIsTrue =
  refl

radialZeroModeExclusionBoundaryTypedIsTrue :
  RadialZeroModeExclusionBoundaryTyped ≡ true
radialZeroModeExclusionBoundaryTypedIsTrue =
  refl

rankOneDefectFormulaAnchorImportedIsTrue :
  RankOneDefectFormulaAnchorImported ≡ true
rankOneDefectFormulaAnchorImportedIsTrue =
  refl

sigmaNonRadialTargetAnchorImportedIsTrue :
  SigmaNonRadialTargetAnchorImported ≡ true
sigmaNonRadialTargetAnchorImportedIsTrue =
  refl

sprint163TopologicalAlignmentAnchorImportedIsTrue :
  Sprint163TopologicalAlignmentAnchorImported ≡ true
sprint163TopologicalAlignmentAnchorImportedIsTrue =
  refl

microlocalDefectMassBoundaryAnchorImportedIsTrue :
  MicrolocalDefectMassBoundaryAnchorImported ≡ true
microlocalDefectMassBoundaryAnchorImportedIsTrue =
  refl

leiRenTianTheoremInternallyFormalizedIsFalse :
  LeiRenTianTheoremInternallyFormalized ≡ false
leiRenTianTheoremInternallyFormalizedIsFalse =
  refl

radialZeroModeInternallyExcludedIsFalse :
  RadialZeroModeInternallyExcluded ≡ false
radialZeroModeInternallyExcludedIsFalse =
  refl

microlocalDefectMassConstructedIsFalse :
  MicrolocalDefectMassConstructed ≡ false
microlocalDefectMassConstructedIsFalse =
  refl

nsCriticalResidualNonPositiveIsFalse :
  NSCriticalResidualNonPositive ≡ false
nsCriticalResidualNonPositiveIsFalse =
  refl

fullLocalDefectMonotonicityIsFalse :
  FullLocalDefectMonotonicity ≡ false
fullLocalDefectMonotonicityIsFalse =
  refl

mechanismExhaustionForFullClayNSIsFalse :
  MechanismExhaustionForFullClayNS ≡ false
mechanismExhaustionForFullClayNSIsFalse =
  refl

fullClayNSSolvedSnakeIsFalse :
  full_clay_ns_solved ≡ false
fullClayNSSolvedSnakeIsFalse =
  refl

fullClayNSSolvedIsFalse :
  fullClayNSSolved ≡ false
fullClayNSSolvedIsFalse =
  refl

clayNavierStokesPromotedIsFalse :
  clayNavierStokesPromoted ≡ false
clayNavierStokesPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

------------------------------------------------------------------------
-- ORCSLPGF.

organizationString : String
organizationString =
  "O: NSLeiRenTianRadialZeroModeAuthorityBoundary is worker lane 3's external-authority boundary for radial NS zero modes."

requirementString : String
requirementString =
  "R: Record Lei-Ren-Tian arXiv:2501.08976 Corollary 1.5 as great-circle vorticity-direction authority support for radial zero-mode exclusion."

codeArtifactString : String
codeArtifactString =
  "C: The module exports source metadata, zero-mode carriers, radial exclusion boundary target, support/status/blocker rows, booleans, and equality receipts."

stateString : String
stateString =
  "S: Rank-one zero-mode algebra, Sprint163 topology vocabulary, Sigma target, and microlocal defect-mass boundary are consumed; internal proof and microlocal measure construction remain open."

latticeString : String
latticeString =
  "L: defect Laplacian zero modes -> radial zero-mode support scenario -> Lei-Ren-Tian great-circle obstruction authority -> radial case boundary -> residual/Clay blockers."

proposalString : String
proposalString =
  "P: Promote only an authority-backed theorem boundary for the radial zero-mode case; keep internal theorem completion and Clay promotion false."

governanceString : String
governanceString =
  "G: External authority is recorded as metadata and boundary support; internal formalization, microlocal defect mass, NSCriticalResidual, Clay NS, and terminal promotion are false."

gapString : String
gapString =
  "F: Missing evidence is internal formalization of Lei-Ren-Tian, proof that the radial zero-mode set misses a great circle in the active bundle, transfer from microlocal support to vorticity direction set I, and closure of all non-radial/tangential/wedge cases."

record NSLeiRenTianRadialZeroModeAuthorityORCSLPGF : Set where
  constructor nsLeiRenTianRadialZeroModeAuthorityORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ gapString

open NSLeiRenTianRadialZeroModeAuthorityORCSLPGF public

canonicalNSLeiRenTianRadialZeroModeAuthorityORCSLPGF :
  NSLeiRenTianRadialZeroModeAuthorityORCSLPGF
canonicalNSLeiRenTianRadialZeroModeAuthorityORCSLPGF =
  nsLeiRenTianRadialZeroModeAuthorityORCSLPGF
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    gapString
    refl

------------------------------------------------------------------------
-- Canonical receipt.

record NSLeiRenTianRadialZeroModeAuthorityBoundaryReceipt : Setω where
  constructor nsLeiRenTianRadialZeroModeAuthorityBoundaryReceipt
  field
    gateName :
      String
    gateNameIsCanonical :
      gateName ≡ "RadialZeroModeDeathByLeiRenTianAuthorityBoundary"

    sourceArxivId :
      String
    sourceArxivIdIsCanonical :
      sourceArxivId ≡ leiRenTianArxivId

    sourceCorollary :
      String
    sourceCorollaryIsCanonical :
      sourceCorollary ≡ leiRenTianCorollary

    authorityClaim :
      String
    authorityClaimIsCanonical :
      authorityClaim ≡ leiRenTianAuthorityClaim

    boundaryUse :
      String
    boundaryUseIsCanonical :
      boundaryUse ≡ leiRenTianBoundaryUse

    sourceMetadataRows :
      List LeiRenTianSourceMetadataRow
    sourceMetadataRowsAreCanonical :
      sourceMetadataRows ≡ canonicalLeiRenTianSourceMetadataRows
    sourceMetadataRowCount :
      Nat
    sourceMetadataRowCountIsCanonical :
      sourceMetadataRowCount ≡ leiRenTianSourceMetadataRowCount
    sourceMetadataRowCountProof :
      sourceMetadataRowCount ≡ 5

    rankOneAnchorImported :
      RankOneDefectFormulaAnchorImported ≡ true
    sigmaTargetAnchorImported :
      SigmaNonRadialTargetAnchorImported ≡ true
    sprint163AnchorImported :
      Sprint163TopologicalAlignmentAnchorImported ≡ true
    microlocalBoundaryAnchorImported :
      MicrolocalDefectMassBoundaryAnchorImported ≡ true

    rankOneStatusRows :
      List RankOne.RankOneProjectionCommutatorStatus
    rankOneStatusRowsAreCanonical :
      rankOneStatusRows
      ≡
      RankOne.canonicalRankOneProjectionCommutatorStatus

    sigmaTargetRecorded :
      Sigma.SigmaNonRadialCommutatorLowerBoundTargetRecorded ≡ true

    sprint163SourceRows :
      List S163.Sprint163SourceRow
    sprint163SourceRowsAreCanonical :
      sprint163SourceRows ≡ S163.canonicalSprint163SourceRows

    microlocalBoundaryRecorded :
      Micro.NSMicrolocalDefectMassConstructionBoundaryRecorded ≡ true

    zeroModeSet :
      NSZeroModeSetCarrier
    zeroModeSetIsCanonical :
      zeroModeSet ≡ canonicalZeroModeSet
    radialZeroMode :
      NSRadialZeroModeCarrier
    radialZeroModeIsCanonical :
      radialZeroMode ≡ canonicalRadialZeroMode
    tangentialZeroMode :
      NSTangentialZeroModeCarrier
    tangentialZeroModeIsCanonical :
      tangentialZeroMode ≡ canonicalTangentialZeroMode
    vorticityDirectionSet :
      VorticityDirectionSetCarrier
    vorticityDirectionSetIsCanonical :
      vorticityDirectionSet ≡ canonicalVorticityDirectionSet
    greatCircleAuthority :
      GreatCircleIntersectionAuthority
    greatCircleAuthorityIsCanonical :
      greatCircleAuthority ≡ canonicalGreatCircleAuthority
    radialZeroModeExclusionBoundary :
      RadialZeroModeExclusionBoundary
    radialZeroModeExclusionBoundaryIsCanonical :
      radialZeroModeExclusionBoundary
      ≡
      canonicalRadialZeroModeExclusionBoundary

    supportRows :
      List RadialZeroModeAuthoritySupportRow
    supportRowsAreCanonical :
      supportRows ≡ canonicalRadialZeroModeAuthoritySupportRows
    supportRowCount :
      Nat
    supportRowCountIsCanonical :
      supportRowCount ≡ radialZeroModeAuthoritySupportRowCount
    supportRowCountProof :
      supportRowCount ≡ 6

    blockerRows :
      List RadialZeroModeAuthorityBlocker
    blockerRowsAreCanonical :
      blockerRows ≡ canonicalRadialZeroModeAuthorityBlockers
    blockerRowCount :
      Nat
    blockerRowCountIsCanonical :
      blockerRowCount ≡ radialZeroModeAuthorityBlockerCount
    blockerRowCountProof :
      blockerRowCount ≡ 11

    statusRows :
      List RadialZeroModeAuthorityStatusRow
    statusRowsAreCanonical :
      statusRows ≡ canonicalRadialZeroModeAuthorityStatusRows
    statusRowCount :
      Nat
    statusRowCountIsCanonical :
      statusRowCount ≡ radialZeroModeAuthorityStatusRowCount
    statusRowCountProof :
      statusRowCount ≡ 7

    leiRenTianTheoremInternallyFormalizedFalse :
      LeiRenTianTheoremInternallyFormalized ≡ false
    radialZeroModeInternallyExcludedFalse :
      RadialZeroModeInternallyExcluded ≡ false
    microlocalDefectMassConstructedFalse :
      MicrolocalDefectMassConstructed ≡ false
    nsCriticalResidualNonPositiveFalse :
      NSCriticalResidualNonPositive ≡ false
    fullLocalDefectMonotonicityFalse :
      FullLocalDefectMonotonicity ≡ false
    mechanismExhaustionForFullClayNSFalse :
      MechanismExhaustionForFullClayNS ≡ false
    clayNavierStokesPromotedFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

    orcslpgf :
      NSLeiRenTianRadialZeroModeAuthorityORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf
      ≡
      canonicalNSLeiRenTianRadialZeroModeAuthorityORCSLPGF

open NSLeiRenTianRadialZeroModeAuthorityBoundaryReceipt public

canonicalNSLeiRenTianRadialZeroModeAuthorityBoundaryReceipt :
  NSLeiRenTianRadialZeroModeAuthorityBoundaryReceipt
canonicalNSLeiRenTianRadialZeroModeAuthorityBoundaryReceipt =
  nsLeiRenTianRadialZeroModeAuthorityBoundaryReceipt
    "RadialZeroModeDeathByLeiRenTianAuthorityBoundary"
    refl
    leiRenTianArxivId
    refl
    leiRenTianCorollary
    refl
    leiRenTianAuthorityClaim
    refl
    leiRenTianBoundaryUse
    refl
    canonicalLeiRenTianSourceMetadataRows
    refl
    leiRenTianSourceMetadataRowCount
    refl
    leiRenTianSourceMetadataRowCountIs5
    refl
    refl
    refl
    refl
    RankOne.canonicalRankOneProjectionCommutatorStatus
    refl
    refl
    S163.canonicalSprint163SourceRows
    refl
    refl
    canonicalZeroModeSet
    refl
    canonicalRadialZeroMode
    refl
    canonicalTangentialZeroMode
    refl
    canonicalVorticityDirectionSet
    refl
    canonicalGreatCircleAuthority
    refl
    canonicalRadialZeroModeExclusionBoundary
    refl
    canonicalRadialZeroModeAuthoritySupportRows
    refl
    radialZeroModeAuthoritySupportRowCount
    refl
    radialZeroModeAuthoritySupportRowCountIs6
    canonicalRadialZeroModeAuthorityBlockers
    refl
    radialZeroModeAuthorityBlockerCount
    refl
    radialZeroModeAuthorityBlockerCountIs11
    canonicalRadialZeroModeAuthorityStatusRows
    refl
    radialZeroModeAuthorityStatusRowCount
    refl
    radialZeroModeAuthorityStatusRowCountIs7
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    canonicalNSLeiRenTianRadialZeroModeAuthorityORCSLPGF
    refl
