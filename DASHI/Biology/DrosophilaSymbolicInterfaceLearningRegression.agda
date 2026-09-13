module DASHI.Biology.DrosophilaSymbolicInterfaceLearningRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Biology.DrosophilaSymbolicInterfaceLearningExact as Symbolic

record DrosophilaSymbolicInterfaceRegression : Set where
  constructor drosophilaSymbolicInterfaceRegression
  field
    symbolicActuatorRemainsArtificial :
      Symbolic.actuatorKind Symbolic.canonicalSocialDemoExperiment
      ≡ Symbolic.artificialSymbolicActuator

    fizzBuzzDoesNotPromoteGeneralCompetence :
      Symbolic.FizzBuzzGeneralProgrammingPermission → ⊥

    socialClaimDoesNotCreateScientificAuthority :
      Symbolic.Source.citationCreatesAuthority Symbolic.socialDemoSource ≡ false

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
    Agda.Builtin.Equality.refl
    Symbolic.fizzBuzzDoesNotEstablishGeneralProgrammingCompetence
    Symbolic.socialDemoCitationCreatesNoAuthority
    Symbolic.connectomeAdvantageRequiresNullComparison
    Symbolic.jamesDeterminismBoundaryPreserved
