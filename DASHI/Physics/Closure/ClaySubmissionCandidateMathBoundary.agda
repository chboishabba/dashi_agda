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
    "YM-A finite domination candidate records Bochner-Weitzenbock domination and depends on H3a for Clay use; proofPromoted=false and clayEligible=false."

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
  "C: Candidate surfaces are NSAStationarityCandidate, NSCKappaBiasCandidate, and YMAFiniteDominationCandidate."

sCard : String
sCard =
  "S: Boundary state is receipt-only; W_r energy ODE, OU bias balance, and Bochner-Weitzenbock domination are string anchors."

lCard : String
lCard =
  "L: NS-A stationarity -> NS-C kappa bias; H3a continuum intake -> YM Clay eligibility; no promotion is inferred here."

pCard : String
pCard =
  "P: Proposal is a builtin-only Agda receipt suitable for narrow agda --no-libraries checking."

gCard : String
gCard =
  "G: Governance gate remains fail-closed: proofPromoted=false and clayEligible=false for every candidate."

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
