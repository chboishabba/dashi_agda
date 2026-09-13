module DASHI.Culture.MissingDeceasedTwentyScientistCompositeApplicationProofDebtExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistEmbodiedTechnologyBidiExact as E
import DASHI.Culture.MissingDeceasedTwentyScientistEmbodiedReferenceRuntimeBidiExact as R

------------------------------------------------------------------------
-- COMPOSITE-APPLICATION PROOF-DEBT ROUTER
--
-- Hard gates are unpaid identity/authorship prerequisites that block the
-- current roster-fibre instantiation.  Soft residuals are ordinary science,
-- calibration, qualification, replay or custody debts.  Neither class proves
-- that an application is impossible, historically deployed, or operationally
-- qualified.
------------------------------------------------------------------------

data ProofDebtKind : Set where
  identityHardGate authorshipHardGate sourceReplayDebt calibrationDebt
  qualificationDebt operatingWindowDebt validationDebt custodyDebt : ProofDebtKind

record ProofDebtItem : Set where
  constructor proof-debt-item
  field
    kind : ProofDebtKind
    owner : String
    missingCoordinate : String
    blocksCurrentRosterInstantiation : Bool

open ProofDebtItem public

record CompositeApplicationProofDebt : Set where
  constructor composite-application-proof-debt
  field
    application : E.CompositeApplication
    hardGateCount : Nat
    hardGates : List ProofDebtItem
    softResiduals : List ProofDebtItem
    currentRosterInstantiationRunnable : Bool
    boundedReading : String

open CompositeApplicationProofDebt public

longDurationProofDebt : CompositeApplicationProofDebt
longDurationProofDebt = composite-application-proof-debt
  E.longDurationSciencePlatform
  0
  []
  (proof-debt-item qualificationDebt "Joshua Kyle LeBlanc" "device-level qualification/failure evidence" false ∷
   proof-debt-item sourceReplayDebt "Frank W. Maiwald" "raw action-spectrum intensity/calibration data" false ∷
   proof-debt-item operatingWindowDebt "Monica Jacinto / Monica Reza" "descendant oxygen-service process/qualification window" false ∷
   proof-debt-item sourceReplayDebt "Zhou Guangyuan" "multi-sample aerogel process/property table" false ∷
   proof-debt-item validationDebt "Zhang Daibing" "source-exact autonomy/control replay" false ∷
   proof-debt-item custodyDebt "Nuno F. G. Loureiro" "Viriato repository/simulation-state handover" false ∷ [])
  true
  "No identity/authorship hard gate blocks the current abstract roster instantiation, but substantial qualification, replay and custody debt remains."

extremeEnvironmentProofDebt : CompositeApplicationProofDebt
extremeEnvironmentProofDebt = composite-application-proof-debt
  E.extremeEnvironmentResearchTestbed
  1
  (proof-debt-item identityHardGate "Anthony Chavez" "same-person weld between missing-person and LANL/Scorpius engineering identities" true ∷ [])
  (proof-debt-item qualificationDebt "Joshua Kyle LeBlanc" "harsh-environment device qualification" false ∷
   proof-debt-item operatingWindowDebt "Monica Jacinto / Monica Reza" "oxygen-service material window" false ∷
   proof-debt-item sourceReplayDebt "Ning Li" "later apparatus/control continuity" false ∷
   proof-debt-item sourceReplayDebt "Fang Daining" "energy functional/geometry/band arrays" false ∷
   proof-debt-item sourceReplayDebt "Yan Hong" "heat-source/geometry/shock-response curves" false ∷ [])
  false
  "The current roster-specific instantiation is gated by Chavez identity. The application class itself is not claimed impossible; other qualified diagnostic implementations could exist."

autonomousSurveyProofDebt : CompositeApplicationProofDebt
autonomousSurveyProofDebt = composite-application-proof-debt
  E.autonomousRemoteSurveyPlatform
  0
  []
  (proof-debt-item sourceReplayDebt "Carl J. Grillmair" "source survey slice and orbit uncertainty" false ∷
   proof-debt-item sourceReplayDebt "Michael David Hicks" "source lightcurve/viewing geometry" false ∷
   proof-debt-item validationDebt "Chen Shuming" "source verification graph/stimulus/coverage example" false ∷
   proof-debt-item sourceReplayDebt "Feng Yanghe" "source classifier equations/data" false ∷
   proof-debt-item sourceReplayDebt "Zhang Xiaoxin" "forecast hyperparameters/code/data" false ∷
   proof-debt-item validationDebt "Zhang Daibing" "source autonomy/control replay" false ∷
   proof-debt-item qualificationDebt "Liu Donghao" "authored DSMM scoring/assessment example" false ∷ [])
  true
  "No roster identity/authorship hard gate is required, but the abstract application remains under-validated and under-qualified."

multiDomainLabProofDebt : CompositeApplicationProofDebt
multiDomainLabProofDebt = composite-application-proof-debt
  E.multiDomainResearchLaboratory
  1
  (proof-debt-item authorshipHardGate "Amy Eskridge" "Amy-authored/recorded technical equations or apparatus object" true ∷ [])
  (proof-debt-item sourceReplayDebt "Frank W. Maiwald" "raw spectrum/calibration data" false ∷
   proof-debt-item validationDebt "Jason R. Thomas" "source assay and target-validation chain" false ∷
   proof-debt-item sourceReplayDebt "Ning Li" "later apparatus/control matrix" false ∷
   proof-debt-item validationDebt "Li Minyong" "one exact molecule/probe replay" false ∷
   proof-debt-item validationDebt "Chen Shuming" "source hardware-verification example" false ∷
   proof-debt-item qualificationDebt "Liu Donghao" "source-authored governance assessment semantics" false ∷ [])
  false
  "The current roster-specific anomalous-force slot is authorship-gated on Amy. That does not imply a multi-domain laboratory is impossible without that slot."

longDurationHardGateCount : Nat
longDurationHardGateCount = 0

extremeEnvironmentHardGateCount : Nat
extremeEnvironmentHardGateCount = 1

autonomousSurveyHardGateCount : Nat
autonomousSurveyHardGateCount = 0

multiDomainLabHardGateCount : Nat
multiDomainLabHardGateCount = 1

proofDebtProfiles : List CompositeApplicationProofDebt
proofDebtProfiles =
  longDurationProofDebt ∷ extremeEnvironmentProofDebt ∷
  autonomousSurveyProofDebt ∷ multiDomainLabProofDebt ∷ []

softResidualDoesNotEqualHardGate : Bool
softResidualDoesNotEqualHardGate = true

gatedRosterFibreImpliesApplicationImpossible : Bool
gatedRosterFibreImpliesApplicationImpossible = false

noHardGateImpliesOperationalQualification : Bool
noHardGateImpliesOperationalQualification = false

runtimePlanImpliesHistoricalDeployment : Bool
runtimePlanImpliesHistoricalDeployment = false

proofDebtRouterCanPrioritiseAcquisition : Bool
proofDebtRouterCanPrioritiseAcquisition = true
