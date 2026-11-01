module DASHI.Physics.Closure.ClaySubmissionCandidateMathBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Clay submission candidate math boundary.
--
-- This standalone receipt records candidate math surfaces only.  It uses
-- Agda builtins, imports no repository modules, and keeps all proof and
-- Clay eligibility gates fail-closed.

modulePath : String
modulePath =
  "DASHI/Physics/Closure/ClaySubmissionCandidateMathBoundary.agda"

boundaryName : String
boundaryName =
  "Clay submission candidate math boundary"

data CandidateSurface : Set where
  NSAStationarityCandidate :
    CandidateSurface
  NSCKappaBiasCandidate :
    CandidateSurface
  YMAFiniteDominationCandidate :
    CandidateSurface

record CandidateReceipt : Set where
  constructor mkCandidateReceipt
  field
    surface :
      CandidateSurface
    surfaceName :
      String
    candidateRecorded :
      Bool
    candidateRecordedIsTrue :
      candidateRecorded ≡ true
    proofPromoted :
      Bool
    proofPromotedIsFalse :
      proofPromoted ≡ false
    clayEligible :
      Bool
    clayEligibleIsFalse :
      clayEligible ≡ false
    mathAnchor :
      String
    boundaryText :
      String

open CandidateReceipt public

wREnergyODEAnchor : String
wREnergyODEAnchor =
  "W_r energy ODE: define W_r = U_r - U_infty and close the local enstrophy energy ODE before any NS-A promotion."

ouBiasBalanceAnchor : String
ouBiasBalanceAnchor =
  "OU bias balance: Ornstein-Uhlenbeck bias neutrality is recorded as a candidate balance, not as proof promotion."

bochnerWeitzenbockDominationAnchor : String
bochnerWeitzenbockDominationAnchor =
  "Bochner-Weitzenbock domination: finite Yang-Mills domination candidate for H_d on Omega_perp, not Clay eligibility."

ymALocalCalculationAnchor : String
ymALocalCalculationAnchor =
  "YM-A local calculation: constants are locally computable and no arithmetic obstruction is recorded, but the operator theorem and H3a intake are still missing."

nsaStationarityReceipt : CandidateReceipt
nsaStationarityReceipt =
  mkCandidateReceipt
    NSAStationarityCandidate
    "NSAStationarityCandidate"
    true
    refl
    false
    refl
    false
    refl
    wREnergyODEAnchor
    "NS-A stationarity candidate recorded at the W_r energy ODE boundary; proofPromoted=false and clayEligible=false."

nscKappaBiasReceipt : CandidateReceipt
nscKappaBiasReceipt =
  mkCandidateReceipt
    NSCKappaBiasCandidate
    "NSCKappaBiasCandidate"
    true
    refl
    false
    refl
    false
    refl
    ouBiasBalanceAnchor
    "NS-C kappa bias candidate records OU bias balance and depends on NS-A; proofPromoted=false and clayEligible=false."

ymaFiniteDominationReceipt : CandidateReceipt
ymaFiniteDominationReceipt =
  mkCandidateReceipt
    YMAFiniteDominationCandidate
    "YMAFiniteDominationCandidate"
    true
    refl
    false
    refl
    false
    refl
    bochnerWeitzenbockDominationAnchor
    "YM-A finite domination candidate records Bochner-Weitzenbock domination plus local candidate arithmetic and depends on H3a for Clay use; proofPromoted=false and clayEligible=false."

record YMAArithmeticReceipt : Set where
  constructor mkYMAArithmeticReceipt
  field
    arithmeticAnchor :
      String
    ymAConstantsLocallyComputable :
      Bool
    ymAConstantsLocallyComputableIsTrue :
      ymAConstantsLocallyComputable ≡ true
    ymAArithmeticObstructionAbsent :
      Bool
    ymAArithmeticObstructionAbsentIsTrue :
      ymAArithmeticObstructionAbsent ≡ true
    ymAOperatorTheoremStillMissing :
      Bool
    ymAOperatorTheoremStillMissingIsTrue :
      ymAOperatorTheoremStillMissing ≡ true
    ymAH3aStillMissing :
      Bool
    ymAH3aStillMissingIsTrue :
      ymAH3aStillMissing ≡ true
    arithmeticText :
      String

open YMAArithmeticReceipt public

ymALocalCalculationCandidateArithmetic : YMAArithmeticReceipt
ymALocalCalculationCandidateArithmetic =
  mkYMAArithmeticReceipt
    ymALocalCalculationAnchor
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "YM-A local calculation is recorded only as candidate arithmetic: ymAConstantsLocallyComputable=true, ymAArithmeticObstructionAbsent=true, ymAOperatorTheoremStillMissing=true, and ymAH3aStillMissing=true."

ymAConstantsLocallyComputableRecordedIsTrue :
  ymAConstantsLocallyComputable ymALocalCalculationCandidateArithmetic ≡ true
ymAConstantsLocallyComputableRecordedIsTrue = refl

ymAArithmeticObstructionAbsentRecordedIsTrue :
  ymAArithmeticObstructionAbsent ymALocalCalculationCandidateArithmetic ≡ true
ymAArithmeticObstructionAbsentRecordedIsTrue = refl

ymAOperatorTheoremStillMissingRecordedIsTrue :
  ymAOperatorTheoremStillMissing ymALocalCalculationCandidateArithmetic ≡ true
ymAOperatorTheoremStillMissingRecordedIsTrue = refl

ymAH3aStillMissingRecordedIsTrue :
  ymAH3aStillMissing ymALocalCalculationCandidateArithmetic ≡ true
ymAH3aStillMissingRecordedIsTrue = refl

kingGammaAuthoritySlot : String
kingGammaAuthoritySlot =
  "King gamma authority slot recorded"

balabanH3aAuthoritySlot : String
balabanH3aAuthoritySlot =
  "Balaban H3a authority slot recorded"

osWightmanAuthoritySlot : String
osWightmanAuthoritySlot =
  "OS/Wightman authority slot recorded"

ymAuthorityBackedSubmissionNarrative : String
ymAuthorityBackedSubmissionNarrative =
  "YM authority-backed submission posture narrative recorded: external authority slots are recorded, externalAcceptancePending=true, and terminal promotion remains closed."

record YMAuthorityBackedSubmissionPosture : Set where
  constructor mkYMAuthorityBackedSubmissionPosture
  field
    narrativeRecorded :
      Bool
    narrativeRecordedIsTrue :
      narrativeRecorded ≡ true
    kingGammaAuthoritySlotRecorded :
      Bool
    kingGammaAuthoritySlotRecordedIsTrue :
      kingGammaAuthoritySlotRecorded ≡ true
    balabanH3aAuthoritySlotRecorded :
      Bool
    balabanH3aAuthoritySlotRecordedIsTrue :
      balabanH3aAuthoritySlotRecorded ≡ true
    osWightmanAuthoritySlotRecorded :
      Bool
    osWightmanAuthoritySlotRecordedIsTrue :
      osWightmanAuthoritySlotRecorded ≡ true
    externalAcceptancePending :
      Bool
    externalAcceptancePendingIsTrue :
      externalAcceptancePending ≡ true
    h3aInternalized :
      Bool
    h3aInternalizedIsFalse :
      h3aInternalized ≡ false
    clayEligibleWithoutExternalAuthority :
      Bool
    clayEligibleWithoutExternalAuthorityIsFalse :
      clayEligibleWithoutExternalAuthority ≡ false
    ymClayPromoted :
      Bool
    ymClayPromotedIsFalse :
      ymClayPromoted ≡ false
    terminalPromotion :
      Bool
    terminalPromotionIsFalse :
      terminalPromotion ≡ false
    narrativeText :
      String
    kingGammaAuthorityText :
      String
    balabanH3aAuthorityText :
      String
    osWightmanAuthorityText :
      String

open YMAuthorityBackedSubmissionPosture public

ymAuthorityBackedSubmissionPosture :
  YMAuthorityBackedSubmissionPosture
ymAuthorityBackedSubmissionPosture =
  mkYMAuthorityBackedSubmissionPosture
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    ymAuthorityBackedSubmissionNarrative
    kingGammaAuthoritySlot
    balabanH3aAuthoritySlot
    osWightmanAuthoritySlot

narrativeRecordedForYMAuthorityPostureIsTrue :
  narrativeRecorded ymAuthorityBackedSubmissionPosture ≡ true
narrativeRecordedForYMAuthorityPostureIsTrue = refl

kingGammaAuthoritySlotRecordedForYMAuthorityPostureIsTrue :
  kingGammaAuthoritySlotRecorded ymAuthorityBackedSubmissionPosture ≡ true
kingGammaAuthoritySlotRecordedForYMAuthorityPostureIsTrue = refl

balabanH3aAuthoritySlotRecordedForYMAuthorityPostureIsTrue :
  balabanH3aAuthoritySlotRecorded ymAuthorityBackedSubmissionPosture ≡ true
balabanH3aAuthoritySlotRecordedForYMAuthorityPostureIsTrue = refl

osWightmanAuthoritySlotRecordedForYMAuthorityPostureIsTrue :
  osWightmanAuthoritySlotRecorded ymAuthorityBackedSubmissionPosture ≡ true
osWightmanAuthoritySlotRecordedForYMAuthorityPostureIsTrue = refl

externalAcceptancePendingForYMAuthorityPostureIsTrue :
  externalAcceptancePending ymAuthorityBackedSubmissionPosture ≡ true
externalAcceptancePendingForYMAuthorityPostureIsTrue = refl

h3aInternalizedForYMAuthorityPostureIsFalse :
  h3aInternalized ymAuthorityBackedSubmissionPosture ≡ false
h3aInternalizedForYMAuthorityPostureIsFalse = refl

clayEligibleWithoutExternalAuthorityForYMAuthorityPostureIsFalse :
  clayEligibleWithoutExternalAuthority ymAuthorityBackedSubmissionPosture ≡ false
clayEligibleWithoutExternalAuthorityForYMAuthorityPostureIsFalse = refl

ymClayPromotedForYMAuthorityPostureIsFalse :
  ymClayPromoted ymAuthorityBackedSubmissionPosture ≡ false
ymClayPromotedForYMAuthorityPostureIsFalse = refl

terminalPromotionForYMAuthorityPostureIsFalse :
  terminalPromotion ymAuthorityBackedSubmissionPosture ≡ false
terminalPromotionForYMAuthorityPostureIsFalse = refl

ymAArithmeticProofPromoted : Bool
ymAArithmeticProofPromoted = false

ymAArithmeticProofPromotedIsFalse :
  ymAArithmeticProofPromoted ≡ false
ymAArithmeticProofPromotedIsFalse = refl

ymAArithmeticClayEligible : Bool
ymAArithmeticClayEligible = false

ymAArithmeticClayEligibleIsFalse :
  ymAArithmeticClayEligible ≡ false
ymAArithmeticClayEligibleIsFalse = refl

candidateReceipts : List CandidateReceipt
candidateReceipts =
  nsaStationarityReceipt
  ∷ nscKappaBiasReceipt
  ∷ ymaFiniteDominationReceipt
  ∷ []

nsaCandidateRecordedIsTrue :
  candidateRecorded nsaStationarityReceipt ≡ true
nsaCandidateRecordedIsTrue = refl

nsaProofPromotedIsFalse :
  proofPromoted nsaStationarityReceipt ≡ false
nsaProofPromotedIsFalse = refl

nsaClayEligibleIsFalse :
  clayEligible nsaStationarityReceipt ≡ false
nsaClayEligibleIsFalse = refl

nscCandidateRecordedIsTrue :
  candidateRecorded nscKappaBiasReceipt ≡ true
nscCandidateRecordedIsTrue = refl

nscProofPromotedIsFalse :
  proofPromoted nscKappaBiasReceipt ≡ false
nscProofPromotedIsFalse = refl

nscClayEligibleIsFalse :
  clayEligible nscKappaBiasReceipt ≡ false
nscClayEligibleIsFalse = refl

ymaCandidateRecordedIsTrue :
  candidateRecorded ymaFiniteDominationReceipt ≡ true
ymaCandidateRecordedIsTrue = refl

ymaProofPromotedIsFalse :
  proofPromoted ymaFiniteDominationReceipt ≡ false
ymaProofPromotedIsFalse = refl

ymaClayEligibleIsFalse :
  clayEligible ymaFiniteDominationReceipt ≡ false
ymaClayEligibleIsFalse = refl

data DependencyEdge : Set where
  nsc-depends-on-nsa :
    DependencyEdge
  ym-clay-depends-on-h3a :
    DependencyEdge

record DependencyReceipt : Set where
  constructor mkDependencyReceipt
  field
    edge :
      DependencyEdge
    fromSurface :
      String
    toSurface :
      String
    dependencyRecorded :
      Bool
    dependencyRecordedIsTrue :
      dependencyRecorded ≡ true
    dependencyText :
      String

open DependencyReceipt public

nscDependsOnNSA : DependencyReceipt
nscDependsOnNSA =
  mkDependencyReceipt
    nsc-depends-on-nsa
    "NS-C"
    "NS-A"
    true
    refl
    "NS-C dependsOn NS-A: kappa/OU bias balance is downstream of stationarity-rate control."

ymClayDependsOnH3a : DependencyReceipt
ymClayDependsOnH3a =
  mkDependencyReceipt
    ym-clay-depends-on-h3a
    "YM Clay"
    "H3a"
    true
    refl
    "YM Clay dependsOn H3a: Bochner-Weitzenbock finite domination is only a candidate surface until the H3a continuum intake is available."

dependencyReceipts : List DependencyReceipt
dependencyReceipts =
  nscDependsOnNSA
  ∷ ymClayDependsOnH3a
  ∷ []

nscDependsOnNSARecordedIsTrue :
  dependencyRecorded nscDependsOnNSA ≡ true
nscDependsOnNSARecordedIsTrue = refl

ymClayDependsOnH3aRecordedIsTrue :
  dependencyRecorded ymClayDependsOnH3a ≡ true
ymClayDependsOnH3aRecordedIsTrue = refl

candidateMathBoundaryRecorded : Bool
candidateMathBoundaryRecorded = true

candidateMathBoundaryRecordedIsTrue :
  candidateMathBoundaryRecorded ≡ true
candidateMathBoundaryRecordedIsTrue = refl

candidateMathBoundaryProofPromoted : Bool
candidateMathBoundaryProofPromoted = false

candidateMathBoundaryProofPromotedIsFalse :
  candidateMathBoundaryProofPromoted ≡ false
candidateMathBoundaryProofPromotedIsFalse = refl

candidateMathBoundaryClayEligible : Bool
candidateMathBoundaryClayEligible = false

candidateMathBoundaryClayEligibleIsFalse :
  candidateMathBoundaryClayEligible ≡ false
candidateMathBoundaryClayEligibleIsFalse = refl

oCard : String
oCard =
  "O: Record three Clay submission candidate math surfaces without importing non-builtin proof authority."

rCard : String
rCard =
  "R: Requirements are candidateRecorded=true, proofPromoted=false, clayEligible=false, NS-C dependsOn NS-A, and YM Clay dependsOn H3a."

cCard : String
cCard =
  "C: Candidate surfaces are NSAStationarityCandidate, NSCKappaBiasCandidate, and YMAFiniteDominationCandidate; YM-A candidate arithmetic records local constants and arithmetic obstruction absence only."

sCard : String
sCard =
  "S: Boundary state is receipt-only; W_r energy ODE, OU bias balance, Bochner-Weitzenbock domination, and YM-A local calculation are string anchors."

lCard : String
lCard =
  "L: NS-A stationarity -> NS-C kappa bias; YM-A constants/arithmetic -> candidate arithmetic only; H3a continuum intake and the operator theorem -> YM Clay eligibility; no promotion is inferred here."

pCard : String
pCard =
  "P: Proposal is a builtin-only Agda receipt suitable for narrow agda --no-libraries checking."

gCard : String
gCard =
  "G: Governance gate remains fail-closed: proofPromoted=false and clayEligible=false for every candidate, including YM-A candidate arithmetic."

fCard : String
fCard =
  "F: Follow-up proof work must replace these candidate anchors before any Clay submission promotion."

controlCards : List String
controlCards =
  oCard
  ∷ rCard
  ∷ cCard
  ∷ sCard
  ∷ lCard
  ∷ pCard
  ∷ gCard
  ∷ fCard
  ∷ []
