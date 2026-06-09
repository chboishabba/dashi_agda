module DASHI.Physics.Closure.NSTangentialZeroModePressureStarvationBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSMicrolocalDefectMassConstructionBoundary as Micro
import DASHI.Physics.Closure.NSNonRadialityQuantificationAverage as NonRadial
import DASHI.Physics.Closure.NSRankOneProjectionCommutatorFormula as RankOne
import DASHI.Physics.Closure.NSZeroModeSetClassificationBoundary as ZeroMode

------------------------------------------------------------------------
-- Tangential zero-mode pressure-starvation boundary for the NS P0 lane.
--
-- This surface records the deterministic theorem target:
--
--   support(mu) subset Z_tan  ==>  P_r = o(D_r)
--
-- where Z_tan is the pressure/strain zero-mode sector satisfying
-- e_+(theta) perpendicular theta.  The Buaria/Bodenschatz/Pumir
-- turbulence evidence (arXiv:2006.01312) is recorded only as supporting
-- evidence for the depletion direction, not as a deterministic theorem
-- and not as a Clay proof.
--
-- The in-repo NSZeroModeSetClassificationBoundary is consumed as a
-- fail-closed boundary receipt.  It records Z_rad union Z_tan and the
-- tangential starvation target, but it does not promote DNS evidence,
-- pressure-starvation, residual depletion, Clay NS, or terminal unification.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data NSZeroModeSector : Set where
  radialZeroModeSector :
    NSZeroModeSector
  tangentialZeroModeSector :
    NSZeroModeSector
  sigmaWedgeDegeneracySector :
    NSZeroModeSector
  leakagePositiveComplementSector :
    NSZeroModeSector

canonicalZeroModeSectors : List NSZeroModeSector
canonicalZeroModeSectors =
  radialZeroModeSector
  ∷ tangentialZeroModeSector
  ∷ sigmaWedgeDegeneracySector
  ∷ leakagePositiveComplementSector
  ∷ []

zeroModeSectorCount : Nat
zeroModeSectorCount =
  listLength canonicalZeroModeSectors

zeroModeSectorCountIs4 :
  zeroModeSectorCount ≡ 4
zeroModeSectorCountIs4 =
  refl

data TangentialZeroModeCondition : Set where
  ePlusPerpendicularTheta :
    TangentialZeroModeCondition
  pressureRieszAlignedChannelVanishes :
    TangentialZeroModeCondition
  defectLaplacianEigenvalueZero :
    TangentialZeroModeCondition

canonicalTangentialZeroModeConditions :
  List TangentialZeroModeCondition
canonicalTangentialZeroModeConditions =
  ePlusPerpendicularTheta
  ∷ pressureRieszAlignedChannelVanishes
  ∷ defectLaplacianEigenvalueZero
  ∷ []

tangentialZeroModeConditionCount : Nat
tangentialZeroModeConditionCount =
  listLength canonicalTangentialZeroModeConditions

tangentialZeroModeConditionCountIs3 :
  tangentialZeroModeConditionCount ≡ 3
tangentialZeroModeConditionCountIs3 =
  refl

data PressureStarvationEstimateTarget : Set where
  pressureFluxLittleOOfCriticalDefect :
    PressureStarvationEstimateTarget
  alignedPressureFluxVanishesOnZTangential :
    PressureStarvationEstimateTarget
  noPositiveCriticalResidualFromTangentialZeroMode :
    PressureStarvationEstimateTarget

canonicalPressureStarvationTargets :
  List PressureStarvationEstimateTarget
canonicalPressureStarvationTargets =
  pressureFluxLittleOOfCriticalDefect
  ∷ alignedPressureFluxVanishesOnZTangential
  ∷ noPositiveCriticalResidualFromTangentialZeroMode
  ∷ []

pressureStarvationTargetCount : Nat
pressureStarvationTargetCount =
  listLength canonicalPressureStarvationTargets

pressureStarvationTargetCountIs3 :
  pressureStarvationTargetCount ≡ 3
pressureStarvationTargetCountIs3 =
  refl

data DNSEvidenceRow : Set where
  buariaBodenschatzPumirArxiv200601312 :
    DNSEvidenceRow
  intenseEnstrophyIntermediateEigenvectorAlignmentObserved :
    DNSEvidenceRow
  maximalEigenvectorAlignmentDepletionObserved :
    DNSEvidenceRow
  evidenceNotDeterministicProof :
    DNSEvidenceRow

canonicalDNSEvidenceRows : List DNSEvidenceRow
canonicalDNSEvidenceRows =
  buariaBodenschatzPumirArxiv200601312
  ∷ intenseEnstrophyIntermediateEigenvectorAlignmentObserved
  ∷ maximalEigenvectorAlignmentDepletionObserved
  ∷ evidenceNotDeterministicProof
  ∷ []

dnsEvidenceRowCount : Nat
dnsEvidenceRowCount =
  listLength canonicalDNSEvidenceRows

dnsEvidenceRowCountIs4 :
  dnsEvidenceRowCount ≡ 4
dnsEvidenceRowCountIs4 =
  refl

data TangentialStarvationSupportRow : Set where
  rankOneDefectZeroModeFormulaSupport :
    TangentialStarvationSupportRow
  fallbackNonRadialAverageSupport :
    TangentialStarvationSupportRow
  zeroModeClassificationBoundarySupport :
    TangentialStarvationSupportRow
  microlocalDefectMeasureSupportTarget :
    TangentialStarvationSupportRow
  dnsEvidenceSupportOnly :
    TangentialStarvationSupportRow
  deterministicAncientProfileEstimateStillMissing :
    TangentialStarvationSupportRow

canonicalTangentialStarvationSupportRows :
  List TangentialStarvationSupportRow
canonicalTangentialStarvationSupportRows =
  rankOneDefectZeroModeFormulaSupport
  ∷ fallbackNonRadialAverageSupport
  ∷ zeroModeClassificationBoundarySupport
  ∷ microlocalDefectMeasureSupportTarget
  ∷ dnsEvidenceSupportOnly
  ∷ deterministicAncientProfileEstimateStillMissing
  ∷ []

tangentialStarvationSupportRowCount : Nat
tangentialStarvationSupportRowCount =
  listLength canonicalTangentialStarvationSupportRows

tangentialStarvationSupportRowCountIs6 :
  tangentialStarvationSupportRowCount ≡ 6
tangentialStarvationSupportRowCountIs6 =
  refl

data TangentialStarvationBlocker : Set where
  zeroModeClassificationConsumedButNotPromoted :
    TangentialStarvationBlocker
  missingDeterministicMaximalEigenvectorDepletion :
    TangentialStarvationBlocker
  missingAncientProfileBlowupRescalingSurvival :
    TangentialStarvationBlocker
  missingPressureFluxLittleOEstimate :
    TangentialStarvationBlocker
  missingTangentialSupportToResidualNonPositive :
    TangentialStarvationBlocker
  missingMicrolocalDefectMassConstruction :
    TangentialStarvationBlocker
  missingNoZeroModeDegeneracyRidingCascade :
    TangentialStarvationBlocker
  missingFullLocalDefectMonotonicity :
    TangentialStarvationBlocker
  missingMechanismExhaustionForFullClayNS :
    TangentialStarvationBlocker

canonicalTangentialStarvationBlockers :
  List TangentialStarvationBlocker
canonicalTangentialStarvationBlockers =
  zeroModeClassificationConsumedButNotPromoted
  ∷ missingDeterministicMaximalEigenvectorDepletion
  ∷ missingAncientProfileBlowupRescalingSurvival
  ∷ missingPressureFluxLittleOEstimate
  ∷ missingTangentialSupportToResidualNonPositive
  ∷ missingMicrolocalDefectMassConstruction
  ∷ missingNoZeroModeDegeneracyRidingCascade
  ∷ missingFullLocalDefectMonotonicity
  ∷ missingMechanismExhaustionForFullClayNS
  ∷ []

tangentialStarvationBlockerCount : Nat
tangentialStarvationBlockerCount =
  listLength canonicalTangentialStarvationBlockers

tangentialStarvationBlockerCountIs9 :
  tangentialStarvationBlockerCount ≡ 9
tangentialStarvationBlockerCountIs9 =
  refl

data TangentialStarvationPromotion : Set where

tangentialStarvationPromotionImpossibleHere :
  TangentialStarvationPromotion →
  ⊥
tangentialStarvationPromotionImpossibleHere ()

theoremName : String
theoremName =
  "NSTangentialZeroModePressureStarvationBoundary"

tangentialZeroModeText : String
tangentialZeroModeText =
  "Z_tan is the zero-mode sector where e_plus(theta) is perpendicular to theta and the aligned pressure channel is starved."

targetEstimateText : String
targetEstimateText =
  "support(mu) subset Z_tan implies pressure flux P_r = o(D_r) before any positive critical residual can persist."

dnsEvidenceText : String
dnsEvidenceText =
  "Buaria/Bodenschatz/Pumir arXiv:2006.01312 supports maximal-eigenvector depletion statistically; it is evidence, not deterministic proof."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Tangential pressure-starvation is recorded as a deterministic theorem target; DNS evidence, non-radial averaging, and microlocal boundary support do not promote Clay NS or terminal unification."

NSTangentialZeroModePressureStarvationBoundaryRecorded : Bool
NSTangentialZeroModePressureStarvationBoundaryRecorded =
  true

FallbackAnchorsConsumed : Bool
FallbackAnchorsConsumed =
  true

RankOneZeroModeFormulaConsumed : Bool
RankOneZeroModeFormulaConsumed =
  true

TangentialZeroModeSetTyped : Bool
TangentialZeroModeSetTyped =
  true

PressureFluxLittleOTargetTyped : Bool
PressureFluxLittleOTargetTyped =
  true

DNSEvidenceRecorded : Bool
DNSEvidenceRecorded =
  true

DNSEvidencePromotedAsProof : Bool
DNSEvidencePromotedAsProof =
  false

ZeroModeClassificationConsumedAsBoundary : Bool
ZeroModeClassificationConsumedAsBoundary =
  true

ZeroModeClassificationPromotedAsStarvationProof : Bool
ZeroModeClassificationPromotedAsStarvationProof =
  false

DeterministicDepletionLemmaProved : Bool
DeterministicDepletionLemmaProved =
  false

AncientProfileSurvivalProved : Bool
AncientProfileSurvivalProved =
  false

TangentialZeroModePressureStarvationProved : Bool
TangentialZeroModePressureStarvationProved =
  false

NSCriticalResidualNonPositiveFromTangentialZeroMode : Bool
NSCriticalResidualNonPositiveFromTangentialZeroMode =
  false

MicrolocalDefectMassConstructed : Bool
MicrolocalDefectMassConstructed =
  false

NoZeroModeDegeneracyRidingCascade : Bool
NoZeroModeDegeneracyRidingCascade =
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

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

organizationString : String
organizationString =
  "O: Worker lane 3 owns only the tangential NS zero-mode pressure-starvation boundary."

requirementString : String
requirementString =
  "R: Record support(mu) subset Z_tan implies P_r=o(D_r) as a deterministic theorem target, while keeping DNS evidence as evidence only."

codeArtifactString : String
codeArtifactString =
  "C: DASHI.Physics.Closure.NSTangentialZeroModePressureStarvationBoundary defines zero-mode sectors, tangential conditions, pressure-starvation targets, DNS evidence rows, blocker rows, the consumed zero-mode classification boundary, fallback anchors, booleans, and equality receipts."

stateString : String
stateString =
  "S: Rank-one zero-mode algebra, the zero-mode classification boundary, finite non-radial averaging, and microlocal defect-mass boundary support are consumed; deterministic ancient-profile depletion and pressure flux little-o estimates remain unproved."

latticeString : String
latticeString =
  "L: rank-one formula -> Z_tan definition -> DNS evidence-only support -> deterministic depletion blocker -> P_r=o(D_r) blocker -> residual nonpositive blocker -> Clay mechanism exhaustion blocker."

proposalString : String
proposalString =
  "P: Use this module as the normalized target for proving tangential zero-mode pressure starvation; do not promote the DNS evidence or finite support rows as proof."

governanceString : String
governanceString =
  "G: DNS evidence promoted-as-proof, deterministic depletion, pressure starvation, residual depletion, Clay NS, and terminal promotion guards remain false."

gapString : String
gapString =
  "F: Missing evidence is a deterministic estimate for ancient suitable blowup profiles showing tangential zero-mode support starves pressure flux at o(D_r), plus microlocal defect mass and mechanism exhaustion."

record NSTangentialZeroModePressureStarvationORCSLPGF : Set where
  constructor nsTangentialZeroModePressureStarvationORCSLPGF
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

open NSTangentialZeroModePressureStarvationORCSLPGF public

canonicalNSTangentialZeroModePressureStarvationORCSLPGF :
  NSTangentialZeroModePressureStarvationORCSLPGF
canonicalNSTangentialZeroModePressureStarvationORCSLPGF =
  nsTangentialZeroModePressureStarvationORCSLPGF
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

record NSTangentialZeroModePressureStarvationBoundaryReceipt : Setω where
  constructor nsTangentialZeroModePressureStarvationBoundaryReceipt
  field
    gateName :
      String
    gateNameIsCanonical :
      gateName ≡ theoremName

    rankOneFormulaAnchor :
      RankOne.NSRankOneProjectionCommutatorFormula
    rankOneFormulaRecorded :
      RankOne.correctedFormulaRecorded rankOneFormulaAnchor ≡ true
    rankOneClayStillFalse :
      RankOne.navierStokesClayPromoted rankOneFormulaAnchor ≡ false
    rankOneTerminalStillFalse :
      RankOne.terminalPromotion rankOneFormulaAnchor ≡ false

    zeroModeClassificationAnchor :
      ZeroMode.NSZeroModeSetClassificationBoundaryReceipt
    zeroModeClassificationBoundaryRecorded :
      ZeroMode.NSZeroModeSetClassificationBoundaryRecorded ≡ true
    zeroModeClassificationTangentialTargetRecorded :
      ZeroMode.TangentialZeroModePressureStarvationTargetRecorded ≡ true
    zeroModeClassificationStarvationStillFalse :
      ZeroMode.TangentialZeroModePressureStarvationProved ≡ false
    zeroModeClassificationSupportExhaustionStillFalse :
      ZeroMode.SupportClassificationExhausted ≡ false
    zeroModeClassificationClayStillFalse :
      ZeroMode.clayNavierStokesPromoted ≡ false
    zeroModeClassificationTerminalStillFalse :
      ZeroMode.terminalPromotion ≡ false

    nonRadialAverageAnchor :
      NonRadial.NSNonRadialityQuantificationAverageReceipt
    nonRadialAverageFiniteSupportRecorded :
      NonRadial.FiniteFourSampleAverageRecorded ≡ true
    nonRadialAverageAnalyticStillFalse :
      NonRadial.AnalyticAnnularIntegralLowerBoundProved ≡ false
    nonRadialAverageClayStillFalse :
      NonRadial.clayNavierStokesPromoted ≡ false

    microlocalDefectMassAnchor :
      Micro.NSMicrolocalDefectMassConstructionBoundaryReceipt
    microlocalBoundaryRecorded :
      Micro.NSMicrolocalDefectMassConstructionBoundaryRecorded ≡ true
    microlocalMassStillFalse :
      Micro.MicrolocalDefectMassConstructed ≡ false
    microlocalPressureBootstrapStillFalse :
      Micro.PressureNonlocalityBootstrapClosed ≡ false

    zeroModeSectors :
      List NSZeroModeSector
    zeroModeSectorsAreCanonical :
      zeroModeSectors ≡ canonicalZeroModeSectors
    recordedZeroModeSectorCount :
      Nat
    zeroModeSectorCountIsFour :
      recordedZeroModeSectorCount ≡ 4

    tangentialZeroModeConditions :
      List TangentialZeroModeCondition
    tangentialZeroModeConditionsAreCanonical :
      tangentialZeroModeConditions
      ≡
      canonicalTangentialZeroModeConditions
    recordedTangentialZeroModeConditionCount :
      Nat
    tangentialZeroModeConditionCountIsThree :
      recordedTangentialZeroModeConditionCount ≡ 3

    pressureStarvationTargets :
      List PressureStarvationEstimateTarget
    pressureStarvationTargetsAreCanonical :
      pressureStarvationTargets ≡ canonicalPressureStarvationTargets
    recordedPressureStarvationTargetCount :
      Nat
    pressureStarvationTargetCountIsThree :
      recordedPressureStarvationTargetCount ≡ 3

    dnsEvidenceRows :
      List DNSEvidenceRow
    dnsEvidenceRowsAreCanonical :
      dnsEvidenceRows ≡ canonicalDNSEvidenceRows
    recordedDNSEvidenceRowCount :
      Nat
    dnsEvidenceRowCountIsFour :
      recordedDNSEvidenceRowCount ≡ 4

    supportRows :
      List TangentialStarvationSupportRow
    supportRowsAreCanonical :
      supportRows ≡ canonicalTangentialStarvationSupportRows
    recordedSupportRowCount :
      Nat
    supportRowCountIsSix :
      recordedSupportRowCount ≡ 6

    blockers :
      List TangentialStarvationBlocker
    blockersAreCanonical :
      blockers ≡ canonicalTangentialStarvationBlockers
    recordedBlockerCount :
      Nat
    blockerCountIsNine :
      recordedBlockerCount ≡ 9

    orcslpgf :
      NSTangentialZeroModePressureStarvationORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTangentialZeroModePressureStarvationORCSLPGF

    targetEstimate :
      String
    targetEstimateIsCanonical :
      targetEstimate ≡ targetEstimateText
    dnsEvidence :
      String
    dnsEvidenceIsCanonical :
      dnsEvidence ≡ dnsEvidenceText
    tangentialZeroModeDescription :
      String
    tangentialZeroModeDescriptionIsCanonical :
      tangentialZeroModeDescription ≡ tangentialZeroModeText
    nonPromotionBoundary :
      String
    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary ≡ nonPromotionBoundaryText

    boundaryRecorded :
      NSTangentialZeroModePressureStarvationBoundaryRecorded ≡ true
    fallbackAnchorsConsumed :
      FallbackAnchorsConsumed ≡ true
    rankOneZeroModeFormulaConsumed :
      RankOneZeroModeFormulaConsumed ≡ true
    tangentialZeroModeSetTyped :
      TangentialZeroModeSetTyped ≡ true
    pressureFluxLittleOTargetTyped :
      PressureFluxLittleOTargetTyped ≡ true
    dnsEvidenceRecorded :
      DNSEvidenceRecorded ≡ true
    dnsEvidencePromotedAsProofFalse :
      DNSEvidencePromotedAsProof ≡ false
    zeroModeClassificationConsumedAsBoundaryTrue :
      ZeroModeClassificationConsumedAsBoundary ≡ true
    zeroModeClassificationPromotedAsStarvationProofFalse :
      ZeroModeClassificationPromotedAsStarvationProof ≡ false
    deterministicDepletionLemmaProvedFalse :
      DeterministicDepletionLemmaProved ≡ false
    ancientProfileSurvivalProvedFalse :
      AncientProfileSurvivalProved ≡ false
    tangentialZeroModePressureStarvationProvedFalse :
      TangentialZeroModePressureStarvationProved ≡ false
    criticalResidualFromTangentialZeroModeFalse :
      NSCriticalResidualNonPositiveFromTangentialZeroMode ≡ false
    microlocalDefectMassConstructedFalse :
      MicrolocalDefectMassConstructed ≡ false
    noZeroModeDegeneracyRidingCascadeFalse :
      NoZeroModeDegeneracyRidingCascade ≡ false
    fullLocalDefectMonotonicityFalse :
      FullLocalDefectMonotonicity ≡ false
    mechanismExhaustionForFullClayNSFalse :
      MechanismExhaustionForFullClayNS ≡ false
    fullClayNSSolvedFalse :
      full_clay_ns_solved ≡ false
    clayNavierStokesPromotedFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

    promotionFlags :
      List TangentialStarvationPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    remainingObligations :
      List String

open NSTangentialZeroModePressureStarvationBoundaryReceipt public

canonicalNSTangentialZeroModePressureStarvationBoundaryReceipt :
  NSTangentialZeroModePressureStarvationBoundaryReceipt
canonicalNSTangentialZeroModePressureStarvationBoundaryReceipt =
  nsTangentialZeroModePressureStarvationBoundaryReceipt
    theoremName
    refl
    RankOne.canonicalNSRankOneProjectionCommutatorFormula
    refl
    refl
    refl
    ZeroMode.canonicalNSZeroModeSetClassificationBoundaryReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    NonRadial.canonicalNSNonRadialityQuantificationAverageReceipt
    refl
    refl
    refl
    Micro.canonicalNSMicrolocalDefectMassConstructionBoundaryReceipt
    refl
    refl
    refl
    canonicalZeroModeSectors
    refl
    zeroModeSectorCount
    refl
    canonicalTangentialZeroModeConditions
    refl
    tangentialZeroModeConditionCount
    refl
    canonicalPressureStarvationTargets
    refl
    pressureStarvationTargetCount
    refl
    canonicalDNSEvidenceRows
    refl
    dnsEvidenceRowCount
    refl
    canonicalTangentialStarvationSupportRows
    refl
    tangentialStarvationSupportRowCount
    refl
    canonicalTangentialStarvationBlockers
    refl
    tangentialStarvationBlockerCount
    refl
    canonicalNSTangentialZeroModePressureStarvationORCSLPGF
    refl
    targetEstimateText
    refl
    dnsEvidenceText
    refl
    tangentialZeroModeText
    refl
    nonPromotionBoundaryText
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    []
    refl
    ("prove deterministic maximal-eigenvector depletion for ancient suitable blowup profiles"
    ∷ "show support(mu) subset Z_tan forces pressure flux P_r=o(D_r) with scale-correct localization"
    ∷ "construct microlocal defect mass before using the pressure-starvation target in the NS mechanism tree"
    ∷ "upgrade DNS evidence to an independent deterministic theorem or keep it as evidence-only"
    ∷ "prove no zero-mode degeneracy-riding cascade and full local defect monotonicity before any Clay NS promotion"
    ∷ [])

nsTangentialZeroModeBoundaryRecorded :
  NSTangentialZeroModePressureStarvationBoundaryRecorded ≡ true
nsTangentialZeroModeBoundaryRecorded =
  refl

dnsEvidenceIsRecordedButNotProof :
  DNSEvidenceRecorded ≡ true
dnsEvidenceIsRecordedButNotProof =
  refl

dnsEvidencePromotedAsProofStillFalse :
  DNSEvidencePromotedAsProof ≡ false
dnsEvidencePromotedAsProofStillFalse =
  refl

tangentialPressureStarvationStillTarget :
  TangentialZeroModePressureStarvationProved ≡ false
tangentialPressureStarvationStillTarget =
  refl

rankOneFormulaConsumedByTangentialBoundary :
  RankOne.correctedFormulaRecorded
    (rankOneFormulaAnchor
      canonicalNSTangentialZeroModePressureStarvationBoundaryReceipt)
  ≡
  true
rankOneFormulaConsumedByTangentialBoundary =
  refl

nonRadialAverageConsumedByTangentialBoundary :
  NonRadial.FiniteFourSampleAverageRecorded ≡ true
nonRadialAverageConsumedByTangentialBoundary =
  refl

microlocalBoundaryConsumedByTangentialBoundary :
  Micro.NSMicrolocalDefectMassConstructionBoundaryRecorded ≡ true
microlocalBoundaryConsumedByTangentialBoundary =
  refl

tangentialZeroModeKeepsMicrolocalMassFalse :
  Micro.MicrolocalDefectMassConstructed ≡ false
tangentialZeroModeKeepsMicrolocalMassFalse =
  refl

tangentialZeroModeKeepsNSClayFalse :
  clayNavierStokesPromoted ≡ false
tangentialZeroModeKeepsNSClayFalse =
  refl

tangentialZeroModeKeepsTerminalFalse :
  terminalPromotion ≡ false
tangentialZeroModeKeepsTerminalFalse =
  refl
