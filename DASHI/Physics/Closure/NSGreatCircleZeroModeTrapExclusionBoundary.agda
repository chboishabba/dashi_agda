module DASHI.Physics.Closure.NSGreatCircleZeroModeTrapExclusionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSLeiRenTianRadialZeroModeAuthorityBoundary as LRT
import DASHI.Physics.Closure.NSZeroModeSetClassificationBoundary as ZClass
import DASHI.Physics.Closure.ProjectionNonlocalityDefectLaplacianZeroModeSheaf as Sheaf

------------------------------------------------------------------------
-- Great-circle zero-mode trap exclusion boundary.
--
-- This worker-lane module records the general zero-mode trap criterion:
--
--   if a candidate angular zero-mode trap Z misses some great circle, then
--   no singular high-vorticity direction set I can be contained in Z,
--   provided Lei-Ren-Tian's great-circle theorem is accepted as an external
--   authority input.
--
-- It integrates the existing defect-Laplacian zero-mode sheaf, the NS
-- zero-mode classification boundary, and the Lei-Ren-Tian authority boundary.
-- It does not internally prove Lei-Ren-Tian, does not classify all
-- great-circle-hitting zero-mode subsets, does not construct microlocal mass,
-- does not prove critical-residual depletion or full local defect
-- monotonicity, and does not promote Clay Navier-Stokes or terminal
-- unification.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Angular trap carriers.

data AngularZeroModeTrap : Set where
  candidateZeroModeTrap :
    AngularZeroModeTrap

  coneZeroModeTrap :
    AngularZeroModeTrap

  wedgeZeroModeTrap :
    AngularZeroModeTrap

  classifiedNSZeroModeTrap :
    AngularZeroModeTrap

  greatCircleHittingZeroModeSubset :
    AngularZeroModeTrap

data GreatCircleWitness : Set where
  missedGreatCircle :
    AngularZeroModeTrap →
    GreatCircleWitness

  everyGreatCircleHit :
    AngularZeroModeTrap →
    GreatCircleWitness

data HighVorticityDirectionSet : Set where
  singularDirectionSetI :
    HighVorticityDirectionSet

data DirectionSetContainment : Set where
  directionSetContainedInTrap :
    HighVorticityDirectionSet →
    AngularZeroModeTrap →
    DirectionSetContainment

data LeiRenTianExternalInput : Set where
  singularDirectionSetHitsEveryGreatCircle :
    HighVorticityDirectionSet →
    LeiRenTianExternalInput

data TrapExclusionBoundary : Set where
  excludedByGreatCircleCriterion :
    (trap : AngularZeroModeTrap) →
    GreatCircleWitness →
    DirectionSetContainment →
    LeiRenTianExternalInput →
    TrapExclusionBoundary

canonicalDirectionSet : HighVorticityDirectionSet
canonicalDirectionSet =
  singularDirectionSetI

canonicalTrap : AngularZeroModeTrap
canonicalTrap =
  candidateZeroModeTrap

canonicalMissedGreatCircle : GreatCircleWitness
canonicalMissedGreatCircle =
  missedGreatCircle canonicalTrap

canonicalContainment : DirectionSetContainment
canonicalContainment =
  directionSetContainedInTrap canonicalDirectionSet canonicalTrap

canonicalLRTInput : LeiRenTianExternalInput
canonicalLRTInput =
  singularDirectionSetHitsEveryGreatCircle canonicalDirectionSet

canonicalTrapExclusionBoundary : TrapExclusionBoundary
canonicalTrapExclusionBoundary =
  excludedByGreatCircleCriterion
    canonicalTrap
    canonicalMissedGreatCircle
    canonicalContainment
    canonicalLRTInput

------------------------------------------------------------------------
-- Mechanism tree branches requested for this lane.

data GreatCircleTrapMechanismBranch : Set where
  awayFromZeroModesPaysLeakage :
    GreatCircleTrapMechanismBranch

  coneWedgeOrZeroModeTrapMissesGreatCircle :
    GreatCircleTrapMechanismBranch

  greatCircleHittingZeroModeSubsetRemains :
    GreatCircleTrapMechanismBranch

  sectorSwitchingRequiresCompactness :
    GreatCircleTrapMechanismBranch

canonicalGreatCircleTrapBranches :
  List GreatCircleTrapMechanismBranch
canonicalGreatCircleTrapBranches =
  awayFromZeroModesPaysLeakage
  ∷ coneWedgeOrZeroModeTrapMissesGreatCircle
  ∷ greatCircleHittingZeroModeSubsetRemains
  ∷ sectorSwitchingRequiresCompactness
  ∷ []

greatCircleTrapBranchCount : Nat
greatCircleTrapBranchCount =
  listLength canonicalGreatCircleTrapBranches

greatCircleTrapBranchCountIs4 :
  greatCircleTrapBranchCount ≡ 4
greatCircleTrapBranchCountIs4 =
  refl

branchDescription : GreatCircleTrapMechanismBranch → String
branchDescription awayFromZeroModesPaysLeakage =
  "mass away from zero modes pays projection/nonlocality defect-laplacian leakage"
branchDescription coneWedgeOrZeroModeTrapMissesGreatCircle =
  "cone, wedge, or zero-mode trap missing a great circle is excluded by Lei-Ren-Tian"
branchDescription greatCircleHittingZeroModeSubsetRemains =
  "great-circle-hitting zero-mode subset remains as classification/depletion target"
branchDescription sectorSwitchingRequiresCompactness =
  "sector switching across scales requires a compactness or microlocal stabilization target"

data GreatCircleTrapBranchTarget : Set where
  leakageAwayFromZeroModeTarget :
    GreatCircleTrapBranchTarget

  lrtGreatCircleTrapExclusionTarget :
    GreatCircleTrapBranchTarget

  greatCircleHittingSubsetClassificationTarget :
    GreatCircleTrapBranchTarget

  sectorSwitchingCompactnessTarget :
    GreatCircleTrapBranchTarget

branchTarget : GreatCircleTrapMechanismBranch → GreatCircleTrapBranchTarget
branchTarget awayFromZeroModesPaysLeakage =
  leakageAwayFromZeroModeTarget
branchTarget coneWedgeOrZeroModeTrapMissesGreatCircle =
  lrtGreatCircleTrapExclusionTarget
branchTarget greatCircleHittingZeroModeSubsetRemains =
  greatCircleHittingSubsetClassificationTarget
branchTarget sectorSwitchingRequiresCompactness =
  sectorSwitchingCompactnessTarget

------------------------------------------------------------------------
-- Boundary rows.

data GreatCircleTrapSupportRow : Set where
  defectLaplacianZeroModeSheafAnchor :
    GreatCircleTrapSupportRow

  nsZeroModeSetClassificationAnchor :
    GreatCircleTrapSupportRow

  leiRenTianGreatCircleAuthorityAnchor :
    GreatCircleTrapSupportRow

  highVorticityDirectionSetCarrierRow :
    GreatCircleTrapSupportRow

  missedGreatCircleWitnessCarrierRow :
    GreatCircleTrapSupportRow

  trapContainmentCarrierRow :
    GreatCircleTrapSupportRow

  trapExclusionBoundaryCarrierRow :
    GreatCircleTrapSupportRow

canonicalGreatCircleTrapSupportRows :
  List GreatCircleTrapSupportRow
canonicalGreatCircleTrapSupportRows =
  defectLaplacianZeroModeSheafAnchor
  ∷ nsZeroModeSetClassificationAnchor
  ∷ leiRenTianGreatCircleAuthorityAnchor
  ∷ highVorticityDirectionSetCarrierRow
  ∷ missedGreatCircleWitnessCarrierRow
  ∷ trapContainmentCarrierRow
  ∷ trapExclusionBoundaryCarrierRow
  ∷ []

greatCircleTrapSupportRowCount : Nat
greatCircleTrapSupportRowCount =
  listLength canonicalGreatCircleTrapSupportRows

greatCircleTrapSupportRowCountIs7 :
  greatCircleTrapSupportRowCount ≡ 7
greatCircleTrapSupportRowCountIs7 =
  refl

data GreatCircleTrapStatusRow : Set where
  externalLRTInputRecordedStatus :
    GreatCircleTrapStatusRow

  greatCircleTrapCriterionTypedStatus :
    GreatCircleTrapStatusRow

  leakageBranchTypedStatus :
    GreatCircleTrapStatusRow

  lrtTrapExclusionBranchTypedStatus :
    GreatCircleTrapStatusRow

  hittingSubsetTargetTypedStatus :
    GreatCircleTrapStatusRow

  sectorSwitchingTargetTypedStatus :
    GreatCircleTrapStatusRow

  microlocalMassFalseStatus :
    GreatCircleTrapStatusRow

  nsResidualFalseStatus :
    GreatCircleTrapStatusRow

  clayPromotionFalseStatus :
    GreatCircleTrapStatusRow

canonicalGreatCircleTrapStatusRows :
  List GreatCircleTrapStatusRow
canonicalGreatCircleTrapStatusRows =
  externalLRTInputRecordedStatus
  ∷ greatCircleTrapCriterionTypedStatus
  ∷ leakageBranchTypedStatus
  ∷ lrtTrapExclusionBranchTypedStatus
  ∷ hittingSubsetTargetTypedStatus
  ∷ sectorSwitchingTargetTypedStatus
  ∷ microlocalMassFalseStatus
  ∷ nsResidualFalseStatus
  ∷ clayPromotionFalseStatus
  ∷ []

greatCircleTrapStatusRowCount : Nat
greatCircleTrapStatusRowCount =
  listLength canonicalGreatCircleTrapStatusRows

greatCircleTrapStatusRowCountIs9 :
  greatCircleTrapStatusRowCount ≡ 9
greatCircleTrapStatusRowCountIs9 =
  refl

data GreatCircleTrapBlocker : Set where
  missingLeiRenTianInternalFormalization :
    GreatCircleTrapBlocker

  missingZeroModeGreatCircleGeometryClassification :
    GreatCircleTrapBlocker

  missingGreatCircleHittingSubsetDepletion :
    GreatCircleTrapBlocker

  missingLeakageAwayFromZeroModesEstimate :
    GreatCircleTrapBlocker

  missingSectorSwitchingCompactness :
    GreatCircleTrapBlocker

  missingMicrolocalDefectMassConstruction :
    GreatCircleTrapBlocker

  missingNSCriticalResidualNonPositive :
    GreatCircleTrapBlocker

  missingFullLocalDefectMonotonicity :
    GreatCircleTrapBlocker

  missingMechanismExhaustionForFullClayNS :
    GreatCircleTrapBlocker

  clayNavierStokesPromotionClosed :
    GreatCircleTrapBlocker

canonicalGreatCircleTrapBlockers :
  List GreatCircleTrapBlocker
canonicalGreatCircleTrapBlockers =
  missingLeiRenTianInternalFormalization
  ∷ missingZeroModeGreatCircleGeometryClassification
  ∷ missingGreatCircleHittingSubsetDepletion
  ∷ missingLeakageAwayFromZeroModesEstimate
  ∷ missingSectorSwitchingCompactness
  ∷ missingMicrolocalDefectMassConstruction
  ∷ missingNSCriticalResidualNonPositive
  ∷ missingFullLocalDefectMonotonicity
  ∷ missingMechanismExhaustionForFullClayNS
  ∷ clayNavierStokesPromotionClosed
  ∷ []

greatCircleTrapBlockerCount : Nat
greatCircleTrapBlockerCount =
  listLength canonicalGreatCircleTrapBlockers

greatCircleTrapBlockerCountIs10 :
  greatCircleTrapBlockerCount ≡ 10
greatCircleTrapBlockerCountIs10 =
  refl

------------------------------------------------------------------------
-- Promotion guard: this boundary exports no inhabitant of promotion.

data NSGreatCircleZeroModeTrapPromotion : Set where

nsGreatCircleZeroModeTrapPromotionImpossibleHere :
  NSGreatCircleZeroModeTrapPromotion →
  ⊥
nsGreatCircleZeroModeTrapPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Canonical strings.

gateName : String
gateName =
  "NSGreatCircleZeroModeTrapExclusionBoundary"

trapCriterionText : String
trapCriterionText =
  "If an angular zero-mode trap Z misses a great circle, Lei-Ren-Tian excludes a singular high-vorticity direction set I contained in Z."

mechanismTreeText : String
mechanismTreeText =
  "away from zero modes -> leakage; trap missing great circle -> LRT exclusion; great-circle-hitting zero-mode subset -> classification/depletion target; sector switching -> compactness target"

nonPromotionText : String
nonPromotionText =
  "This module records a theorem boundary only; microlocal mass, residual depletion, full local defect monotonicity, Clay NS, and terminal promotion remain false."

organizationString : String
organizationString =
  "O: Worker 3 owns the NS great-circle zero-mode trap exclusion boundary module only."

requirementString : String
requirementString =
  "R: Encode the Lei-Ren-Tian great-circle criterion as a general zero-mode trap exclusion boundary with the requested four mechanism branches."

codeArtifactString : String
codeArtifactString =
  "C: DASHI.Physics.Closure.NSGreatCircleZeroModeTrapExclusionBoundary exports angular trap carriers, branch targets, support/status/blocker rows, fail-closed guards, ORCSLPGF, and a canonical receipt."

stateString : String
stateString =
  "S: Existing defect-Laplacian zero-mode sheaf, NS zero-mode classification, and Lei-Ren-Tian authority boundary are imported; general great-circle-hitting zero-mode classification and microlocal mass remain open."

latticeString : String
latticeString =
  "L: defect-Laplacian zero modes -> angular trap geometry -> LRT great-circle obstruction for avoidant traps -> remaining hitting/depletion/compactness targets -> microlocal mass -> residual and Clay blockers."

proposalString : String
proposalString =
  "P: Promote only the typed boundary for cone/wedge/zero-mode traps that miss a great circle; keep analytic and Clay promotions false."

governanceString : String
governanceString =
  "G: External authority is consumed as a boundary input; no internal LRT proof, no microlocal mass, no NSCriticalResidual, no full local monotonicity, no Clay NS, and no terminal promotion."

gapString : String
gapString =
  "F: Remaining evidence deficit is zero-mode great-circle geometry classification, depletion for great-circle-hitting zero-mode subsets, leakage estimates, sector-switching compactness, and microlocal defect mass."

record NSGreatCircleZeroModeTrapORCSLPGF : Set where
  constructor nsGreatCircleZeroModeTrapORCSLPGF
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

open NSGreatCircleZeroModeTrapORCSLPGF public

canonicalNSGreatCircleZeroModeTrapORCSLPGF :
  NSGreatCircleZeroModeTrapORCSLPGF
canonicalNSGreatCircleZeroModeTrapORCSLPGF =
  nsGreatCircleZeroModeTrapORCSLPGF
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
-- Fail-closed booleans.

NSGreatCircleZeroModeTrapExclusionBoundaryRecorded : Bool
NSGreatCircleZeroModeTrapExclusionBoundaryRecorded =
  true

DefectLaplacianZeroModeSheafAnchorImported : Bool
DefectLaplacianZeroModeSheafAnchorImported =
  Sheaf.zeroModeSheafRecorded

NSZeroModeSetClassificationAnchorImported : Bool
NSZeroModeSetClassificationAnchorImported =
  ZClass.NSZeroModeSetClassificationBoundaryRecorded

LeiRenTianGreatCircleAuthorityAnchorImported : Bool
LeiRenTianGreatCircleAuthorityAnchorImported =
  LRT.LeiRenTianGreatCircleAuthorityBoundaryRecorded

GreatCircleTrapCriterionTyped : Bool
GreatCircleTrapCriterionTyped =
  true

AwayFromZeroModesLeakageBranchRecorded : Bool
AwayFromZeroModesLeakageBranchRecorded =
  true

LRTMissedGreatCircleTrapExclusionBranchRecorded : Bool
LRTMissedGreatCircleTrapExclusionBranchRecorded =
  true

GreatCircleHittingZeroModeSubsetTargetRecorded : Bool
GreatCircleHittingZeroModeSubsetTargetRecorded =
  true

SectorSwitchingCompactnessTargetRecorded : Bool
SectorSwitchingCompactnessTargetRecorded =
  true

LeiRenTianTheoremInternallyFormalized : Bool
LeiRenTianTheoremInternallyFormalized =
  false

ZeroModeGreatCircleGeometryClassified : Bool
ZeroModeGreatCircleGeometryClassified =
  false

GreatCircleHittingZeroModeSubsetDepleted : Bool
GreatCircleHittingZeroModeSubsetDepleted =
  false

LeakageAwayFromZeroModesProved : Bool
LeakageAwayFromZeroModesProved =
  false

SectorSwitchingCompactnessProved : Bool
SectorSwitchingCompactnessProved =
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

nsGreatCircleZeroModeTrapBoundaryRecordedIsTrue :
  NSGreatCircleZeroModeTrapExclusionBoundaryRecorded ≡ true
nsGreatCircleZeroModeTrapBoundaryRecordedIsTrue =
  refl

defectLaplacianZeroModeSheafAnchorImportedIsTrue :
  DefectLaplacianZeroModeSheafAnchorImported ≡ true
defectLaplacianZeroModeSheafAnchorImportedIsTrue =
  Sheaf.zeroModeSheafRecordedIsTrue

nsZeroModeSetClassificationAnchorImportedIsTrue :
  NSZeroModeSetClassificationAnchorImported ≡ true
nsZeroModeSetClassificationAnchorImportedIsTrue =
  refl

leiRenTianGreatCircleAuthorityAnchorImportedIsTrue :
  LeiRenTianGreatCircleAuthorityAnchorImported ≡ true
leiRenTianGreatCircleAuthorityAnchorImportedIsTrue =
  LRT.leiRenTianGreatCircleAuthorityBoundaryRecordedIsTrue

greatCircleTrapCriterionTypedIsTrue :
  GreatCircleTrapCriterionTyped ≡ true
greatCircleTrapCriterionTypedIsTrue =
  refl

awayFromZeroModesLeakageBranchRecordedIsTrue :
  AwayFromZeroModesLeakageBranchRecorded ≡ true
awayFromZeroModesLeakageBranchRecordedIsTrue =
  refl

lrtMissedGreatCircleTrapExclusionBranchRecordedIsTrue :
  LRTMissedGreatCircleTrapExclusionBranchRecorded ≡ true
lrtMissedGreatCircleTrapExclusionBranchRecordedIsTrue =
  refl

greatCircleHittingZeroModeSubsetTargetRecordedIsTrue :
  GreatCircleHittingZeroModeSubsetTargetRecorded ≡ true
greatCircleHittingZeroModeSubsetTargetRecordedIsTrue =
  refl

sectorSwitchingCompactnessTargetRecordedIsTrue :
  SectorSwitchingCompactnessTargetRecorded ≡ true
sectorSwitchingCompactnessTargetRecordedIsTrue =
  refl

leiRenTianTheoremInternallyFormalizedIsFalse :
  LeiRenTianTheoremInternallyFormalized ≡ false
leiRenTianTheoremInternallyFormalizedIsFalse =
  refl

zeroModeGreatCircleGeometryClassifiedIsFalse :
  ZeroModeGreatCircleGeometryClassified ≡ false
zeroModeGreatCircleGeometryClassifiedIsFalse =
  refl

greatCircleHittingZeroModeSubsetDepletedIsFalse :
  GreatCircleHittingZeroModeSubsetDepleted ≡ false
greatCircleHittingZeroModeSubsetDepletedIsFalse =
  refl

leakageAwayFromZeroModesProvedIsFalse :
  LeakageAwayFromZeroModesProved ≡ false
leakageAwayFromZeroModesProvedIsFalse =
  refl

sectorSwitchingCompactnessProvedIsFalse :
  SectorSwitchingCompactnessProved ≡ false
sectorSwitchingCompactnessProvedIsFalse =
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
-- Canonical receipt.

record NSGreatCircleZeroModeTrapExclusionBoundaryReceipt : Setω where
  constructor nsGreatCircleZeroModeTrapExclusionBoundaryReceipt
  field
    theoremName :
      String
    theoremNameIsCanonical :
      theoremName ≡ gateName

    trapCriterion :
      String
    trapCriterionIsCanonical :
      trapCriterion ≡ trapCriterionText

    mechanismTree :
      String
    mechanismTreeIsCanonical :
      mechanismTree ≡ mechanismTreeText

    sheafAnchorRecorded :
      Sheaf.zeroModeSheafRecorded ≡ true
    sheafNSInstanceRow :
      Sheaf.ZeroModeInstanceRow
    sheafNSInstanceRowIsCanonical :
      sheafNSInstanceRow ≡ Sheaf.nsZeroModeInstanceRow

    zeroModeClassificationAnchor :
      ZClass.NSZeroModeSetClassificationBoundaryReceipt
    zeroModeClassificationRecorded :
      ZClass.NSZeroModeSetClassificationBoundaryRecorded ≡ true
    zeroModeClassificationMicrolocalMassFalse :
      ZClass.MicrolocalDefectMassConstructed ≡ false
    zeroModeClassificationClayFalse :
      ZClass.clayNavierStokesPromoted ≡ false

    leiRenTianAuthorityAnchor :
      LRT.NSLeiRenTianRadialZeroModeAuthorityBoundaryReceipt
    leiRenTianAuthorityRecorded :
      LRT.LeiRenTianGreatCircleAuthorityBoundaryRecorded ≡ true
    leiRenTianInternalProofStillFalse :
      LRT.LeiRenTianTheoremInternallyFormalized ≡ false
    leiRenTianMicrolocalMassStillFalse :
      LRT.MicrolocalDefectMassConstructed ≡ false
    leiRenTianClayStillFalse :
      LRT.clayNavierStokesPromoted ≡ false

    directionSet :
      HighVorticityDirectionSet
    directionSetIsCanonical :
      directionSet ≡ canonicalDirectionSet

    trap :
      AngularZeroModeTrap
    trapIsCanonical :
      trap ≡ canonicalTrap

    missedGreatCircleWitness :
      GreatCircleWitness
    missedGreatCircleWitnessIsCanonical :
      missedGreatCircleWitness ≡ canonicalMissedGreatCircle

    containment :
      DirectionSetContainment
    containmentIsCanonical :
      containment ≡ canonicalContainment

    lrtInput :
      LeiRenTianExternalInput
    lrtInputIsCanonical :
      lrtInput ≡ canonicalLRTInput

    exclusionBoundary :
      TrapExclusionBoundary
    exclusionBoundaryIsCanonical :
      exclusionBoundary ≡ canonicalTrapExclusionBoundary

    branches :
      List GreatCircleTrapMechanismBranch
    branchesAreCanonical :
      branches ≡ canonicalGreatCircleTrapBranches
    branchCount :
      Nat
    branchCountIs4 :
      branchCount ≡ 4

    awayBranchDescription :
      branchDescription awayFromZeroModesPaysLeakage
      ≡
      "mass away from zero modes pays projection/nonlocality defect-laplacian leakage"
    lrtBranchDescription :
      branchDescription coneWedgeOrZeroModeTrapMissesGreatCircle
      ≡
      "cone, wedge, or zero-mode trap missing a great circle is excluded by Lei-Ren-Tian"
    hittingBranchDescription :
      branchDescription greatCircleHittingZeroModeSubsetRemains
      ≡
      "great-circle-hitting zero-mode subset remains as classification/depletion target"
    switchingBranchDescription :
      branchDescription sectorSwitchingRequiresCompactness
      ≡
      "sector switching across scales requires a compactness or microlocal stabilization target"

    awayBranchTarget :
      branchTarget awayFromZeroModesPaysLeakage
      ≡
      leakageAwayFromZeroModeTarget
    lrtBranchTarget :
      branchTarget coneWedgeOrZeroModeTrapMissesGreatCircle
      ≡
      lrtGreatCircleTrapExclusionTarget
    hittingBranchTarget :
      branchTarget greatCircleHittingZeroModeSubsetRemains
      ≡
      greatCircleHittingSubsetClassificationTarget
    switchingBranchTarget :
      branchTarget sectorSwitchingRequiresCompactness
      ≡
      sectorSwitchingCompactnessTarget

    supportRows :
      List GreatCircleTrapSupportRow
    supportRowsAreCanonical :
      supportRows ≡ canonicalGreatCircleTrapSupportRows
    supportRowCount :
      Nat
    supportRowCountIs7 :
      supportRowCount ≡ 7

    statusRows :
      List GreatCircleTrapStatusRow
    statusRowsAreCanonical :
      statusRows ≡ canonicalGreatCircleTrapStatusRows
    statusRowCount :
      Nat
    statusRowCountIs9 :
      statusRowCount ≡ 9

    blockers :
      List GreatCircleTrapBlocker
    blockersAreCanonical :
      blockers ≡ canonicalGreatCircleTrapBlockers
    blockerCount :
      Nat
    blockerCountIs10 :
      blockerCount ≡ 10

    boundaryRecorded :
      NSGreatCircleZeroModeTrapExclusionBoundaryRecorded ≡ true
    defectLaplacianZeroModeSheafAnchorImported :
      DefectLaplacianZeroModeSheafAnchorImported ≡ true
    nsZeroModeSetClassificationAnchorImported :
      NSZeroModeSetClassificationAnchorImported ≡ true
    leiRenTianGreatCircleAuthorityAnchorImported :
      LeiRenTianGreatCircleAuthorityAnchorImported ≡ true
    greatCircleTrapCriterionTyped :
      GreatCircleTrapCriterionTyped ≡ true
    awayFromZeroModesLeakageBranchRecorded :
      AwayFromZeroModesLeakageBranchRecorded ≡ true
    lrtMissedGreatCircleTrapExclusionBranchRecorded :
      LRTMissedGreatCircleTrapExclusionBranchRecorded ≡ true
    greatCircleHittingZeroModeSubsetTargetRecorded :
      GreatCircleHittingZeroModeSubsetTargetRecorded ≡ true
    sectorSwitchingCompactnessTargetRecorded :
      SectorSwitchingCompactnessTargetRecorded ≡ true

    leiRenTianTheoremInternallyFormalizedFalse :
      LeiRenTianTheoremInternallyFormalized ≡ false
    zeroModeGreatCircleGeometryClassifiedFalse :
      ZeroModeGreatCircleGeometryClassified ≡ false
    greatCircleHittingZeroModeSubsetDepletedFalse :
      GreatCircleHittingZeroModeSubsetDepleted ≡ false
    leakageAwayFromZeroModesProvedFalse :
      LeakageAwayFromZeroModesProved ≡ false
    sectorSwitchingCompactnessProvedFalse :
      SectorSwitchingCompactnessProved ≡ false
    microlocalDefectMassConstructedFalse :
      MicrolocalDefectMassConstructed ≡ false
    nsCriticalResidualNonPositiveFalse :
      NSCriticalResidualNonPositive ≡ false
    fullLocalDefectMonotonicityFalse :
      FullLocalDefectMonotonicity ≡ false
    mechanismExhaustionForFullClayNSFalse :
      MechanismExhaustionForFullClayNS ≡ false
    fullClayNSSolvedSnakeFalse :
      full_clay_ns_solved ≡ false
    fullClayNSSolvedFalse :
      fullClayNSSolved ≡ false
    clayNavierStokesPromotedFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

    promotionFlags :
      List NSGreatCircleZeroModeTrapPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    nonPromotionBoundary :
      String
    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary ≡ nonPromotionText

    orcslpgf :
      NSGreatCircleZeroModeTrapORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSGreatCircleZeroModeTrapORCSLPGF

    remainingObligations :
      List String

open NSGreatCircleZeroModeTrapExclusionBoundaryReceipt public

canonicalNSGreatCircleZeroModeTrapExclusionBoundaryReceipt :
  NSGreatCircleZeroModeTrapExclusionBoundaryReceipt
canonicalNSGreatCircleZeroModeTrapExclusionBoundaryReceipt =
  nsGreatCircleZeroModeTrapExclusionBoundaryReceipt
    gateName
    refl
    trapCriterionText
    refl
    mechanismTreeText
    refl
    Sheaf.zeroModeSheafRecordedIsTrue
    Sheaf.nsZeroModeInstanceRow
    refl
    ZClass.canonicalNSZeroModeSetClassificationBoundaryReceipt
    refl
    refl
    refl
    LRT.canonicalNSLeiRenTianRadialZeroModeAuthorityBoundaryReceipt
    refl
    refl
    refl
    refl
    canonicalDirectionSet
    refl
    canonicalTrap
    refl
    canonicalMissedGreatCircle
    refl
    canonicalContainment
    refl
    canonicalLRTInput
    refl
    canonicalTrapExclusionBoundary
    refl
    canonicalGreatCircleTrapBranches
    refl
    greatCircleTrapBranchCount
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    canonicalGreatCircleTrapSupportRows
    refl
    greatCircleTrapSupportRowCount
    refl
    canonicalGreatCircleTrapStatusRows
    refl
    greatCircleTrapStatusRowCount
    refl
    canonicalGreatCircleTrapBlockers
    refl
    greatCircleTrapBlockerCount
    refl
    refl
    defectLaplacianZeroModeSheafAnchorImportedIsTrue
    nsZeroModeSetClassificationAnchorImportedIsTrue
    leiRenTianGreatCircleAuthorityAnchorImportedIsTrue
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
    nonPromotionText
    refl
    canonicalNSGreatCircleZeroModeTrapORCSLPGF
    refl
    ( "classify which NS zero-mode components miss a great circle"
      ∷ "prove depletion or rigidity for any great-circle-hitting zero-mode subset"
      ∷ "prove leakage away from zero modes"
      ∷ "prove sector-switching compactness or microlocal stabilization"
      ∷ "construct nontrivial microlocal defect mass from arbitrary blowup sequences"
      ∷ "derive NSCriticalResidualNonPositive and FullLocalDefectMonotonicity"
      ∷ "keep Clay Navier-Stokes and terminal promotion false until mechanism exhaustion is proved"
      ∷ [] )

nsGreatCircleZeroModeTrapBoundaryConsumesSheaf :
  Sheaf.zeroModeSheafRecorded ≡ true
nsGreatCircleZeroModeTrapBoundaryConsumesSheaf =
  Sheaf.zeroModeSheafRecordedIsTrue

nsGreatCircleZeroModeTrapBoundaryConsumesClassification :
  ZClass.NSZeroModeSetClassificationBoundaryRecorded ≡ true
nsGreatCircleZeroModeTrapBoundaryConsumesClassification =
  refl

nsGreatCircleZeroModeTrapBoundaryConsumesLRTAuthority :
  LRT.LeiRenTianGreatCircleAuthorityBoundaryRecorded ≡ true
nsGreatCircleZeroModeTrapBoundaryConsumesLRTAuthority =
  LRT.leiRenTianGreatCircleAuthorityBoundaryRecordedIsTrue

nsGreatCircleZeroModeTrapBoundaryKeepsMicrolocalMassFalse :
  MicrolocalDefectMassConstructed ≡ false
nsGreatCircleZeroModeTrapBoundaryKeepsMicrolocalMassFalse =
  microlocalDefectMassConstructedIsFalse

nsGreatCircleZeroModeTrapBoundaryKeepsClayFalse :
  clayNavierStokesPromoted ≡ false
nsGreatCircleZeroModeTrapBoundaryKeepsClayFalse =
  clayNavierStokesPromotedIsFalse

nsGreatCircleZeroModeTrapBoundaryKeepsTerminalFalse :
  terminalPromotion ≡ false
nsGreatCircleZeroModeTrapBoundaryKeepsTerminalFalse =
  terminalPromotionIsFalse

------------------------------------------------------------------------
-- Explicit fail-closed boundary envelope.

canonicalGreatCircleTrapRemainingObligations :
  List String
canonicalGreatCircleTrapRemainingObligations =
  "classify which NS zero-mode components miss a great circle"
  ∷ "prove depletion or rigidity for any great-circle-hitting zero-mode subset"
  ∷ "prove leakage away from zero modes"
  ∷ "prove sector-switching compactness or microlocal stabilization"
  ∷ "construct nontrivial microlocal defect mass from arbitrary blowup sequences"
  ∷ "derive NSCriticalResidualNonPositive and FullLocalDefectMonotonicity"
  ∷ "keep Clay Navier-Stokes and terminal promotion false until mechanism exhaustion is proved"
  ∷ []

greatCircleTrapRemainingObligationCount : Nat
greatCircleTrapRemainingObligationCount =
  listLength canonicalGreatCircleTrapRemainingObligations

greatCircleTrapRemainingObligationCountIs7 :
  greatCircleTrapRemainingObligationCount ≡ 7
greatCircleTrapRemainingObligationCountIs7 =
  refl

record NSGreatCircleZeroModeTrapFailClosedEnvelope : Setω where
  constructor nsGreatCircleZeroModeTrapFailClosedEnvelope
  field
    receipt :
      NSGreatCircleZeroModeTrapExclusionBoundaryReceipt
    receiptIsCanonical :
      receipt ≡ canonicalNSGreatCircleZeroModeTrapExclusionBoundaryReceipt

    externalAuthorityAcceptedAsBoundaryOnly :
      LRT.LeiRenTianGreatCircleAuthorityBoundaryRecorded ≡ true
    internalLeiRenTianProofAbsent :
      LeiRenTianTheoremInternallyFormalized ≡ false

    typedCriterionRecorded :
      TrapExclusionBoundary
    typedCriterionRecordedIsCanonical :
      typedCriterionRecorded ≡ canonicalTrapExclusionBoundary

    branches :
      List GreatCircleTrapMechanismBranch
    branchesAreCanonical :
      branches ≡ canonicalGreatCircleTrapBranches
    branchCountProof :
      listLength branches ≡ 4

    supportRows :
      List GreatCircleTrapSupportRow
    supportRowsAreCanonical :
      supportRows ≡ canonicalGreatCircleTrapSupportRows
    supportRowCountProof :
      listLength supportRows ≡ 7

    statusRows :
      List GreatCircleTrapStatusRow
    statusRowsAreCanonical :
      statusRows ≡ canonicalGreatCircleTrapStatusRows
    statusRowCountProof :
      listLength statusRows ≡ 9

    blockers :
      List GreatCircleTrapBlocker
    blockersAreCanonical :
      blockers ≡ canonicalGreatCircleTrapBlockers
    blockerCountProof :
      listLength blockers ≡ 10

    remainingObligations :
      List String
    remainingObligationsAreCanonical :
      remainingObligations ≡ canonicalGreatCircleTrapRemainingObligations
    remainingObligationCountProof :
      listLength remainingObligations ≡ 7

    promotionFlags :
      List NSGreatCircleZeroModeTrapPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []
    noPromotionPossibleHere :
      NSGreatCircleZeroModeTrapPromotion →
      ⊥

    microlocalMassStillFalse :
      MicrolocalDefectMassConstructed ≡ false
    criticalResidualStillFalse :
      NSCriticalResidualNonPositive ≡ false
    fullLocalMonotonicityStillFalse :
      FullLocalDefectMonotonicity ≡ false
    claySolvedStillFalse :
      full_clay_ns_solved ≡ false
    clayPromotionStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionStillFalse :
      terminalPromotion ≡ false

open NSGreatCircleZeroModeTrapFailClosedEnvelope public

canonicalNSGreatCircleZeroModeTrapFailClosedEnvelope :
  NSGreatCircleZeroModeTrapFailClosedEnvelope
canonicalNSGreatCircleZeroModeTrapFailClosedEnvelope =
  nsGreatCircleZeroModeTrapFailClosedEnvelope
    canonicalNSGreatCircleZeroModeTrapExclusionBoundaryReceipt
    refl
    LRT.leiRenTianGreatCircleAuthorityBoundaryRecordedIsTrue
    refl
    canonicalTrapExclusionBoundary
    refl
    canonicalGreatCircleTrapBranches
    refl
    greatCircleTrapBranchCountIs4
    canonicalGreatCircleTrapSupportRows
    refl
    greatCircleTrapSupportRowCountIs7
    canonicalGreatCircleTrapStatusRows
    refl
    greatCircleTrapStatusRowCountIs9
    canonicalGreatCircleTrapBlockers
    refl
    greatCircleTrapBlockerCountIs10
    canonicalGreatCircleTrapRemainingObligations
    refl
    greatCircleTrapRemainingObligationCountIs7
    []
    refl
    nsGreatCircleZeroModeTrapPromotionImpossibleHere
    refl
    refl
    refl
    refl
    refl
    refl

canonicalNSGreatCircleZeroModeTrapFailClosedSummary :
  String
canonicalNSGreatCircleZeroModeTrapFailClosedSummary =
  "Fail-closed: the great-circle trap criterion is typed from external LRT authority, but classification, depletion, leakage, compactness, microlocal mass, residual monotonicity, Clay NS, and terminal promotion remain blocked."
