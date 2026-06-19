module DASHI.Physics.Closure.NSCollapseBoundaryQCommutatorEstimateReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Fail-closed receipt for the collapse-boundary Q(t) commutator route.
--
-- This module records the detailed derivative bookkeeping for
--
--   Q(t) = integral |<omega,e2>|^2 / g12^2 dH2
--
-- on the moving boundary.  The receipt names the moving boundary measure
-- term, advective flux, vorticity stretching numerator, Rellich-Kato e2
-- rotation, g12 denominator derivative, pressure Hessian terms, the
-- singular F123 contribution, and the desired estimate dQ/dt <= C Q.
--
-- The route remains non-promoting: closure stays false, Clay stays false,
-- and the commutator/absorption blockers are recorded explicitly.

data NSCollapseBoundaryQCommutatorEstimateStatus : Set where
  qCommutatorRouteRecorded_noClosure :
    NSCollapseBoundaryQCommutatorEstimateStatus

data NSCollapseBoundaryQCommutatorEstimateStage : Set where
  qFunctionalOnMovingBoundaryRecorded :
    NSCollapseBoundaryQCommutatorEstimateStage
  movingBoundaryMeasureTermRecorded :
    NSCollapseBoundaryQCommutatorEstimateStage
  advectiveFluxTermRecorded :
    NSCollapseBoundaryQCommutatorEstimateStage
  vorticityStretchingNumeratorRecorded :
    NSCollapseBoundaryQCommutatorEstimateStage
  rellichKatoE2RotationRecorded :
    NSCollapseBoundaryQCommutatorEstimateStage
  g12DenominatorDerivativeRecorded :
    NSCollapseBoundaryQCommutatorEstimateStage
  pressureHessianTermsRecorded :
    NSCollapseBoundaryQCommutatorEstimateStage
  singularF123TermRecorded :
    NSCollapseBoundaryQCommutatorEstimateStage
  desiredEstimateRecorded :
    NSCollapseBoundaryQCommutatorEstimateStage
  blockerLedgerRecorded :
    NSCollapseBoundaryQCommutatorEstimateStage
  closureAndClayFalseRecorded :
    NSCollapseBoundaryQCommutatorEstimateStage

canonicalNSCollapseBoundaryQCommutatorEstimateStages :
  List NSCollapseBoundaryQCommutatorEstimateStage
canonicalNSCollapseBoundaryQCommutatorEstimateStages =
  qFunctionalOnMovingBoundaryRecorded
  ∷ movingBoundaryMeasureTermRecorded
  ∷ advectiveFluxTermRecorded
  ∷ vorticityStretchingNumeratorRecorded
  ∷ rellichKatoE2RotationRecorded
  ∷ g12DenominatorDerivativeRecorded
  ∷ pressureHessianTermsRecorded
  ∷ singularF123TermRecorded
  ∷ desiredEstimateRecorded
  ∷ blockerLedgerRecorded
  ∷ closureAndClayFalseRecorded
  ∷ []

data NSCollapseBoundaryQCommutatorEstimateTerm : Set where
  movingBoundaryMeasureTerm :
    NSCollapseBoundaryQCommutatorEstimateTerm
  advectiveFluxTerm :
    NSCollapseBoundaryQCommutatorEstimateTerm
  vorticityStretchingNumeratorTerm :
    NSCollapseBoundaryQCommutatorEstimateTerm
  rellichKatoE2RotationTerm :
    NSCollapseBoundaryQCommutatorEstimateTerm
  g12DenominatorDerivativeTerm :
    NSCollapseBoundaryQCommutatorEstimateTerm
  pressureHessianTerms :
    NSCollapseBoundaryQCommutatorEstimateTerm
  singularF123Term :
    NSCollapseBoundaryQCommutatorEstimateTerm
  desiredGronwallEstimate :
    NSCollapseBoundaryQCommutatorEstimateTerm

canonicalNSCollapseBoundaryQCommutatorEstimateTerms :
  List NSCollapseBoundaryQCommutatorEstimateTerm
canonicalNSCollapseBoundaryQCommutatorEstimateTerms =
  movingBoundaryMeasureTerm
  ∷ advectiveFluxTerm
  ∷ vorticityStretchingNumeratorTerm
  ∷ rellichKatoE2RotationTerm
  ∷ g12DenominatorDerivativeTerm
  ∷ pressureHessianTerms
  ∷ singularF123Term
  ∷ desiredGronwallEstimate
  ∷ []

data NSCollapseBoundaryQCommutatorEstimateBlocker : Set where
  movingBoundaryMeasureControlOpen :
    NSCollapseBoundaryQCommutatorEstimateBlocker
  advectiveFluxCancellationOpen :
    NSCollapseBoundaryQCommutatorEstimateBlocker
  vorticityStretchingAbsorptionOpen :
    NSCollapseBoundaryQCommutatorEstimateBlocker
  rellichKatoRotationBoundOpen :
    NSCollapseBoundaryQCommutatorEstimateBlocker
  g12LowerBoundPersistenceOpen :
    NSCollapseBoundaryQCommutatorEstimateBlocker
  pressureHessianSignControlOpen :
    NSCollapseBoundaryQCommutatorEstimateBlocker
  singularF123AbsorptionOpen :
    NSCollapseBoundaryQCommutatorEstimateBlocker
  gronwallConstantExtractionOpen :
    NSCollapseBoundaryQCommutatorEstimateBlocker
  closurePromotionUnavailable :
    NSCollapseBoundaryQCommutatorEstimateBlocker

canonicalNSCollapseBoundaryQCommutatorEstimateBlockers :
  List NSCollapseBoundaryQCommutatorEstimateBlocker
canonicalNSCollapseBoundaryQCommutatorEstimateBlockers =
  movingBoundaryMeasureControlOpen
  ∷ advectiveFluxCancellationOpen
  ∷ vorticityStretchingAbsorptionOpen
  ∷ rellichKatoRotationBoundOpen
  ∷ g12LowerBoundPersistenceOpen
  ∷ pressureHessianSignControlOpen
  ∷ singularF123AbsorptionOpen
  ∷ gronwallConstantExtractionOpen
  ∷ closurePromotionUnavailable
  ∷ []

data NSCollapseBoundaryQCommutatorEstimatePromotion : Set where

nsCollapseBoundaryQCommutatorEstimatePromotionImpossibleHere :
  NSCollapseBoundaryQCommutatorEstimatePromotion →
  ⊥
nsCollapseBoundaryQCommutatorEstimatePromotionImpossibleHere ()

qFunctionalText : String
qFunctionalText =
  "Q(t) = integral_{moving boundary} |<omega,e2>|^2 / g12^2 dH2"

movingBoundaryMeasureTermText : String
movingBoundaryMeasureTermText =
  "moving boundary measure term: d/dt(dH2) contributes the boundary Jacobian and normal-velocity correction"

advectiveFluxTermText : String
advectiveFluxTermText =
  "advective flux term: transport of |<omega,e2>|^2 / g12^2 by u . grad on the moving boundary"

vorticityStretchingNumeratorTermText : String
vorticityStretchingNumeratorTermText =
  "vorticity stretching numerator: 2 <omega,e2> <(omega . grad)u, e2> / g12^2 plus the projected stretching remainder"

rellichKatoE2RotationTermText : String
rellichKatoE2RotationTermText =
  "Rellich-Kato e2 rotation: <omega, d_t e2> / g12^2 with d_t e2 = sum_{k != 2} <e_k, A_t e2> / (lambda2 - lambdak) * e_k"

g12DenominatorDerivativeTermText : String
g12DenominatorDerivativeTermText =
  "g12 denominator derivative: d_t(g12^-2) = -2 g12_t / g12^3"

pressureHessianTermsText : String
pressureHessianTermsText =
  "pressure Hessian terms: the Hessian of p enters through the eigenframe evolution and the commutator route"

singularF123TermText : String
singularF123TermText =
  "singular F123 term: the boundary commutator contribution with 1/g12 structure that remains singular without extra cancellation"

assembledDerivativeText : String
assembledDerivativeText =
  "dQ/dt = moving boundary measure term + advective flux term + vorticity stretching numerator + Rellich-Kato e2 rotation + g12 denominator derivative + pressure Hessian terms + singular F123 term"

targetEstimateText : String
targetEstimateText =
  "desired estimate: dQ/dt <= C Q"

routeSummaryText : String
routeSummaryText =
  "The Q(t) commutator route records the moving-boundary differentiation of |<omega,e2>|^2 / g12^2, but the required boundary commutator, pressure-Hessian, and singular-term absorptions remain open, so the receipt keeps closure false and only records the target Gronwall form."

receiptBoundaryText : List String
receiptBoundaryText =
  "Q(t) is recorded on the moving boundary as integral |<omega,e2>|^2 / g12^2 dH2"
  ∷ "the moving boundary measure term is recorded explicitly"
  ∷ "the advective flux term is recorded explicitly"
  ∷ "the vorticity stretching numerator term is recorded explicitly"
  ∷ "the Rellich-Kato e2 rotation term is recorded explicitly"
  ∷ "the g12 denominator derivative term is recorded explicitly"
  ∷ "the pressure Hessian terms are recorded explicitly"
  ∷ "the singular F123 commutator term is recorded explicitly"
  ∷ "the desired estimate dQ/dt <= C Q is recorded as the target"
  ∷ "the blocker ledger remains open and closure stays false"
  ∷ "Clay stays false"
  ∷ []

record NSCollapseBoundaryQCommutatorEstimateReceipt : Setω where
  field
    status :
      NSCollapseBoundaryQCommutatorEstimateStatus

    statusIsCanonical :
      status ≡ qCommutatorRouteRecorded_noClosure

    stageLedger :
      List NSCollapseBoundaryQCommutatorEstimateStage

    stageLedgerIsCanonical :
      stageLedger ≡ canonicalNSCollapseBoundaryQCommutatorEstimateStages

    derivativeTerms :
      List NSCollapseBoundaryQCommutatorEstimateTerm

    derivativeTermsIsCanonical :
      derivativeTerms ≡ canonicalNSCollapseBoundaryQCommutatorEstimateTerms

    blockers :
      List NSCollapseBoundaryQCommutatorEstimateBlocker

    blockersIsCanonical :
      blockers ≡ canonicalNSCollapseBoundaryQCommutatorEstimateBlockers

    qFunctional :
      String

    qFunctionalIsCanonical :
      qFunctional ≡ qFunctionalText

    movingBoundaryMeasureTermDescription :
      String

    movingBoundaryMeasureTermDescriptionIsCanonical :
      movingBoundaryMeasureTermDescription ≡ movingBoundaryMeasureTermText

    advectiveFluxTermDescription :
      String

    advectiveFluxTermDescriptionIsCanonical :
      advectiveFluxTermDescription ≡ advectiveFluxTermText

    vorticityStretchingNumeratorDescription :
      String

    vorticityStretchingNumeratorDescriptionIsCanonical :
      vorticityStretchingNumeratorDescription
      ≡ vorticityStretchingNumeratorTermText

    rellichKatoE2RotationDescription :
      String

    rellichKatoE2RotationDescriptionIsCanonical :
      rellichKatoE2RotationDescription ≡ rellichKatoE2RotationTermText

    g12DenominatorDerivativeDescription :
      String

    g12DenominatorDerivativeDescriptionIsCanonical :
      g12DenominatorDerivativeDescription
      ≡ g12DenominatorDerivativeTermText

    pressureHessianTermsDescription :
      String

    pressureHessianTermsDescriptionIsCanonical :
      pressureHessianTermsDescription ≡ pressureHessianTermsText

    singularF123TermDescription :
      String

    singularF123TermDescriptionIsCanonical :
      singularF123TermDescription ≡ singularF123TermText

    assembledDerivativeDescription :
      String

    assembledDerivativeDescriptionIsCanonical :
      assembledDerivativeDescription ≡ assembledDerivativeText

    targetEstimate :
      String

    targetEstimateIsCanonical :
      targetEstimate ≡ targetEstimateText

    closurePromoted :
      Bool

    closurePromotedIsFalse :
      closurePromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    routeSummary :
      String

    routeSummaryIsCanonical :
      routeSummary ≡ routeSummaryText

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryText

open NSCollapseBoundaryQCommutatorEstimateReceipt public

canonicalNSCollapseBoundaryQCommutatorEstimateReceipt :
  NSCollapseBoundaryQCommutatorEstimateReceipt
canonicalNSCollapseBoundaryQCommutatorEstimateReceipt =
  record
    { status =
        qCommutatorRouteRecorded_noClosure
    ; statusIsCanonical =
        refl
    ; stageLedger =
        canonicalNSCollapseBoundaryQCommutatorEstimateStages
    ; stageLedgerIsCanonical =
        refl
    ; derivativeTerms =
        canonicalNSCollapseBoundaryQCommutatorEstimateTerms
    ; derivativeTermsIsCanonical =
        refl
    ; blockers =
        canonicalNSCollapseBoundaryQCommutatorEstimateBlockers
    ; blockersIsCanonical =
        refl
    ; qFunctional =
        qFunctionalText
    ; qFunctionalIsCanonical =
        refl
    ; movingBoundaryMeasureTermDescription =
        movingBoundaryMeasureTermText
    ; movingBoundaryMeasureTermDescriptionIsCanonical =
        refl
    ; advectiveFluxTermDescription =
        advectiveFluxTermText
    ; advectiveFluxTermDescriptionIsCanonical =
        refl
    ; vorticityStretchingNumeratorDescription =
        vorticityStretchingNumeratorTermText
    ; vorticityStretchingNumeratorDescriptionIsCanonical =
        refl
    ; rellichKatoE2RotationDescription =
        rellichKatoE2RotationTermText
    ; rellichKatoE2RotationDescriptionIsCanonical =
        refl
    ; g12DenominatorDerivativeDescription =
        g12DenominatorDerivativeTermText
    ; g12DenominatorDerivativeDescriptionIsCanonical =
        refl
    ; pressureHessianTermsDescription =
        pressureHessianTermsText
    ; pressureHessianTermsDescriptionIsCanonical =
        refl
    ; singularF123TermDescription =
        singularF123TermText
    ; singularF123TermDescriptionIsCanonical =
        refl
    ; assembledDerivativeDescription =
        assembledDerivativeText
    ; assembledDerivativeDescriptionIsCanonical =
        refl
    ; targetEstimate =
        targetEstimateText
    ; targetEstimateIsCanonical =
        refl
    ; closurePromoted =
        false
    ; closurePromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; routeSummary =
        routeSummaryText
    ; routeSummaryIsCanonical =
        refl
    ; receiptBoundary =
        receiptBoundaryText
    ; receiptBoundaryIsCanonical =
        refl
    }

canonicalNSCollapseBoundaryQCommutatorEstimateStatus :
  status canonicalNSCollapseBoundaryQCommutatorEstimateReceipt
  ≡ qCommutatorRouteRecorded_noClosure
canonicalNSCollapseBoundaryQCommutatorEstimateStatus =
  refl

canonicalNSCollapseBoundaryQCommutatorEstimateClosurePromotedIsFalse :
  closurePromoted canonicalNSCollapseBoundaryQCommutatorEstimateReceipt
  ≡ false
canonicalNSCollapseBoundaryQCommutatorEstimateClosurePromotedIsFalse =
  refl

canonicalNSCollapseBoundaryQCommutatorEstimateClayPromotedIsFalse :
  clayPromoted canonicalNSCollapseBoundaryQCommutatorEstimateReceipt
  ≡ false
canonicalNSCollapseBoundaryQCommutatorEstimateClayPromotedIsFalse =
  refl

