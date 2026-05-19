module DASHI.Physics.Closure.DiscreteEinsteinTensorNextThreadIndex where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ContinuumLimitTheorem as CL
import DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT as DCRT
import DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate as DET
import DASHI.Physics.Closure.EinsteinEquationCandidate as EEC
import DASHI.Physics.Closure.SchwarzschildLimitCandidate as SLC

------------------------------------------------------------------------
-- Discrete Einstein tensor next-thread index.
--
-- This module is a routing index only.  Schwarzschild and continuum surfaces
-- are candidate/request surfaces, so the next admissible GR thread is not a
-- promotion step.  It is the bounded sequence that must close a carrier-
-- internal discrete Einstein tensor route before any finite-r Bianchi, W4
-- matter coupling, metric/connection error-bound, or GR/QFT consumer claim can
-- be promoted.

data DiscreteEinsteinTensorNextThreadStatus : Set where
  indexedNextThreadOnlyNoGRPromotion :
    DiscreteEinsteinTensorNextThreadStatus

data DiscreteEinsteinTensorNextThreadDependency : Set where
  dependencyDiscreteEinsteinTensorCandidate :
    DiscreteEinsteinTensorNextThreadDependency
  dependencyCRTConnectionDiagnostic :
    DiscreteEinsteinTensorNextThreadDependency
  dependencySchwarzschildLimitCandidate :
    DiscreteEinsteinTensorNextThreadDependency
  dependencyContinuumLimitTheoremCandidate :
    DiscreteEinsteinTensorNextThreadDependency
  dependencyW4MatterStressEnergyInterface :
    DiscreteEinsteinTensorNextThreadDependency

data DiscreteEinsteinTensorNextThreadKillCondition : Set where
  killMissingCarrierInternalNonFlatConnectionFromCRT :
    DiscreteEinsteinTensorNextThreadKillCondition
  killMissingDiscreteDifferenceDelta :
    DiscreteEinsteinTensorNextThreadKillCondition
  killMissingNonFlatGammaConnectionCoefficients :
    DiscreteEinsteinTensorNextThreadKillCondition
  killMissingCurvatureToRicciContraction :
    DiscreteEinsteinTensorNextThreadKillCondition
  killMissingFiniteRBianchiWitness :
    DiscreteEinsteinTensorNextThreadKillCondition
  killMissingDiscreteEinsteinTensorLaw :
    DiscreteEinsteinTensorNextThreadKillCondition
  killMissingW4MatterStressEnergyInterfaceReceipt :
    DiscreteEinsteinTensorNextThreadKillCondition
  killMissingMetricErrorBound :
    DiscreteEinsteinTensorNextThreadKillCondition
  killMissingConnectionErrorBound :
    DiscreteEinsteinTensorNextThreadKillCondition
  killSchwarzschildCandidateOnlyNoStandardDerivation :
    DiscreteEinsteinTensorNextThreadKillCondition
  killContinuumCandidateOnlyNoScalingTheorem :
    DiscreteEinsteinTensorNextThreadKillCondition

data DiscreteEinsteinTensorNextThreadUnsupportedClaim : Set where
  unsupportedNonFlatGRPromotion :
    DiscreteEinsteinTensorNextThreadUnsupportedClaim
  unsupportedFiniteRBianchiClosure :
    DiscreteEinsteinTensorNextThreadUnsupportedClaim
  unsupportedW4MatterCouplingClosure :
    DiscreteEinsteinTensorNextThreadUnsupportedClaim
  unsupportedMetricConnectionContinuumErrorClosure :
    DiscreteEinsteinTensorNextThreadUnsupportedClaim
  unsupportedSchwarzschildDerivation :
    DiscreteEinsteinTensorNextThreadUnsupportedClaim
  unsupportedG6CommutativityFromGRCandidate :
    DiscreteEinsteinTensorNextThreadUnsupportedClaim

canonicalDiscreteEinsteinTensorNextThreadDependencies :
  List DiscreteEinsteinTensorNextThreadDependency
canonicalDiscreteEinsteinTensorNextThreadDependencies =
  dependencyDiscreteEinsteinTensorCandidate
  ∷ dependencyCRTConnectionDiagnostic
  ∷ dependencySchwarzschildLimitCandidate
  ∷ dependencyContinuumLimitTheoremCandidate
  ∷ dependencyW4MatterStressEnergyInterface
  ∷ []

canonicalDiscreteEinsteinTensorNextThreadKillConditions :
  List DiscreteEinsteinTensorNextThreadKillCondition
canonicalDiscreteEinsteinTensorNextThreadKillConditions =
  killMissingCarrierInternalNonFlatConnectionFromCRT
  ∷ killMissingDiscreteDifferenceDelta
  ∷ killMissingNonFlatGammaConnectionCoefficients
  ∷ killMissingCurvatureToRicciContraction
  ∷ killMissingFiniteRBianchiWitness
  ∷ killMissingDiscreteEinsteinTensorLaw
  ∷ killMissingW4MatterStressEnergyInterfaceReceipt
  ∷ killMissingMetricErrorBound
  ∷ killMissingConnectionErrorBound
  ∷ killSchwarzschildCandidateOnlyNoStandardDerivation
  ∷ killContinuumCandidateOnlyNoScalingTheorem
  ∷ []

canonicalDiscreteEinsteinTensorNextThreadUnsupportedClaims :
  List DiscreteEinsteinTensorNextThreadUnsupportedClaim
canonicalDiscreteEinsteinTensorNextThreadUnsupportedClaims =
  unsupportedNonFlatGRPromotion
  ∷ unsupportedFiniteRBianchiClosure
  ∷ unsupportedW4MatterCouplingClosure
  ∷ unsupportedMetricConnectionContinuumErrorClosure
  ∷ unsupportedSchwarzschildDerivation
  ∷ unsupportedG6CommutativityFromGRCandidate
  ∷ []

record DiscreteEinsteinTensorNextThreadIndex : Setω where
  field
    status :
      DiscreteEinsteinTensorNextThreadStatus

    discreteEinsteinTensorDiagnostic :
      DET.DiscreteEinsteinTensorCandidateDiagnostic

    crtConnectionDiagnostic :
      DCRT.DiscreteConnectionCandidateFromCRTDiagnostic

    schwarzschildLimitCandidate :
      SLC.SchwarzschildLimitCandidateDiagnostic

    continuumLimitTheoremCandidate :
      CL.ContinuumLimitTheoremCandidate

    w4MatterStressEnergyInterface :
      EEC.W4MatterStressEnergyInterfaceDiagnostic

    exactDependencies :
      List DiscreteEinsteinTensorNextThreadDependency

    exactDependenciesAreCanonical :
      exactDependencies
      ≡
      canonicalDiscreteEinsteinTensorNextThreadDependencies

    firstKillCondition :
      DiscreteEinsteinTensorNextThreadKillCondition

    firstKillConditionIsCRTConnection :
      firstKillCondition
      ≡
      killMissingCarrierInternalNonFlatConnectionFromCRT

    tensorConstructionRequestName :
      String

    tensorConstructionMissingPrimitives :
      List DET.DiscreteEinsteinTensorConstructionMissingPrimitive

    tensorConstructionMissingPrimitivesAreCanonical :
      tensorConstructionMissingPrimitives
      ≡
      DET.canonicalDiscreteEinsteinTensorConstructionMissingPrimitives

    killConditions :
      List DiscreteEinsteinTensorNextThreadKillCondition

    killConditionsAreCanonical :
      killConditions
      ≡
      canonicalDiscreteEinsteinTensorNextThreadKillConditions

    unsupportedClaims :
      List DiscreteEinsteinTensorNextThreadUnsupportedClaim

    unsupportedClaimsAreCanonical :
      unsupportedClaims
      ≡
      canonicalDiscreteEinsteinTensorNextThreadUnsupportedClaims

    nextThreadLabel :
      String

    nextActionableReceipt :
      String

    dependencyBoundary :
      List String

    noPromotionBoundary :
      List String

canonicalDiscreteEinsteinTensorNextThreadIndex :
  DiscreteEinsteinTensorNextThreadIndex
canonicalDiscreteEinsteinTensorNextThreadIndex =
  record
    { status =
        indexedNextThreadOnlyNoGRPromotion
    ; discreteEinsteinTensorDiagnostic =
        DET.canonicalDiscreteEinsteinTensorCandidateDiagnostic
    ; crtConnectionDiagnostic =
        DCRT.canonicalDiscreteConnectionCandidateFromCRTDiagnostic
    ; schwarzschildLimitCandidate =
        SLC.canonicalSchwarzschildLimitCandidateDiagnostic
    ; continuumLimitTheoremCandidate =
        CL.canonicalContinuumLimitTheoremCandidate
    ; w4MatterStressEnergyInterface =
        EEC.canonicalW4MatterStressEnergyInterfaceDiagnostic
    ; exactDependencies =
        canonicalDiscreteEinsteinTensorNextThreadDependencies
    ; exactDependenciesAreCanonical =
        refl
    ; firstKillCondition =
        killMissingCarrierInternalNonFlatConnectionFromCRT
    ; firstKillConditionIsCRTConnection =
        refl
    ; tensorConstructionRequestName =
        DET.DiscreteEinsteinTensorCandidateDiagnostic.tensorConstructionRequestName
          DET.canonicalDiscreteEinsteinTensorCandidateDiagnostic
    ; tensorConstructionMissingPrimitives =
        DET.canonicalDiscreteEinsteinTensorConstructionMissingPrimitives
    ; tensorConstructionMissingPrimitivesAreCanonical =
        refl
    ; killConditions =
        canonicalDiscreteEinsteinTensorNextThreadKillConditions
    ; killConditionsAreCanonical =
        refl
    ; unsupportedClaims =
        canonicalDiscreteEinsteinTensorNextThreadUnsupportedClaims
    ; unsupportedClaimsAreCanonical =
        refl
    ; nextThreadLabel =
        "discrete Einstein tensor finite-r next thread"
    ; nextActionableReceipt =
        "carrier-internal non-flat CRT/J connection or shift law, discrete Δ and Γ over the selected carrier/index/scalar surface, Riemann/Ricci/scalar-curvature contraction laws, finite-r Bianchi witness, discrete Einstein tensor law, W4 stress-energy coupling, and metric/connection error bounds"
    ; dependencyBoundary =
        "DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate is flat/diagnostic only"
        ∷ "DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate.DiscreteEinsteinTensorConstructionRequestSurface names the uninhabited Δ/Γ/Riemann/Ricci/scalar/Einstein tensor request"
        ∷ "DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT records CRT/J as first-missing connection data"
        ∷ "DASHI.Physics.Closure.SchwarzschildLimitCandidate is a request surface, not a standard Schwarzschild derivation"
        ∷ "DASHI.Physics.Closure.ContinuumLimitTheorem is a theorem-request surface, not a continuum scaling theorem"
        ∷ "DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt remains uninhabited here"
        ∷ []
    ; noPromotionBoundary =
        "This index does not construct a carrier-internal non-flat connection"
        ∷ "This index does not prove finite-r Bianchi cancellation"
        ∷ "This index does not construct W4 matter/stress-energy coupling"
        ∷ "This index does not prove metric or connection error bounds"
        ∷ "This index does not promote Schwarzschild, continuum, non-flat GR, GR/QFT, W4, or G6"
        ∷ []
    }

discreteEinsteinTensorNextThreadExactStatus :
  DiscreteEinsteinTensorNextThreadIndex.status
    canonicalDiscreteEinsteinTensorNextThreadIndex
  ≡
  indexedNextThreadOnlyNoGRPromotion
discreteEinsteinTensorNextThreadExactStatus = refl

discreteEinsteinTensorNextThreadExactFirstKill :
  DiscreteEinsteinTensorNextThreadIndex.firstKillCondition
    canonicalDiscreteEinsteinTensorNextThreadIndex
  ≡
  killMissingCarrierInternalNonFlatConnectionFromCRT
discreteEinsteinTensorNextThreadExactFirstKill = refl
