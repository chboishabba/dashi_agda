module DASHI.Biology.DrosophilaSymbolicInterfaceLearningRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Biology.DrosophilaSymbolicInterfaceLearningExact as Symbolic
import DASHI.Core.AttributedSourceCore as Source

record DrosophilaSymbolicInterfaceRegression : Set where
  constructor drosophilaSymbolicInterfaceRegression
  field
    symbolicActuatorRemainsArtificial :
      Symbolic.actuatorKind Symbolic.canonicalSocialDemoExperiment
      ≡ Symbolic.artificialSymbolicActuator

    fizzBuzzDoesNotPromoteGeneralCompetence :
      Symbolic.FizzBuzzGeneralProgrammingPermission → ⊥

    socialClaimDoesNotCreateScientificAuthority :
      Source.citationCreatesAuthority Symbolic.socialDemoSource ≡ false

    implementationRecoveryStillOpen :
      Symbolic.primaryImplementationLocated
        Symbolic.canonicalPythonDemoImplementationDebt
      ≡ false

    adjacentAssistanceStillDoesNotTransfer :
      Symbolic.AdjacentDemoAssistanceTransferPermission → ⊥

    sameObjectIdentityStillUnpaid :
      Symbolic.sameObjectReceiptPresent Symbolic.canonicalIdentityCorroboration
      ≡ false

    negativePublicSearchStillDoesNotProveAbsence :
      Symbolic.PublicSearchExhaustionPermission → ⊥

    publicArtifactStillUnrecovered :
      Symbolic.exactPythonDemoArtifactLocated
        Symbolic.canonicalPublicArtifactSearchReceipt
      ≡ false

    connectomeAdvantageStillNeedsNulls :
      Symbolic.ConnectomeCausalAdvantagePermission → ⊥

    jamesMetaphysicalBoundaryPreserved :
      Symbolic.metaphysicalDeterminismPaid
        Symbolic.canonicalSymbolicInterfaceBoundarySummary
      ≡ false

open DrosophilaSymbolicInterfaceRegression public

canonicalDrosophilaSymbolicInterfaceRegression :
  DrosophilaSymbolicInterfaceRegression
canonicalDrosophilaSymbolicInterfaceRegression =
  drosophilaSymbolicInterfaceRegression
    refl
    Symbolic.fizzBuzzDoesNotEstablishGeneralProgrammingCompetence
    Symbolic.socialDemoCitationCreatesNoAuthority
    Symbolic.primaryImplementationStillUnpaid
    Symbolic.adjacentDemoAssistanceDoesNotTransferToPythonRun
    Symbolic.sameObjectIdentityStillUnpaid
    Symbolic.publicSearchNotFoundDoesNotProveNoArtifact
    Symbolic.publicArtifactStillNotLocated
    Symbolic.connectomeAdvantageRequiresNullComparison
    Symbolic.jamesDeterminismBoundaryPreserved
