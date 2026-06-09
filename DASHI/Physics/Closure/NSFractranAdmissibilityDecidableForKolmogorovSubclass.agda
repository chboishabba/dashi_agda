module DASHI.Physics.Closure.NSFractranAdmissibilityDecidableForKolmogorovSubclass where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSFractranTailAdmissibilityReceipt as Tail
import DASHI.Physics.Closure.NSToEV5ProjectionFrontierReceipt as Projection

------------------------------------------------------------------------
-- NS/FRACTRAN admissibility: decidable Kolmogorov subclass only.
--
-- FRACTRAN is Turing-complete in general, so this receipt does not promote
-- general carrier admissibility or a Clay Navier-Stokes theorem.  It records
-- the narrow decidable subclass already suggested by the NS-facing EV5
-- receipts: Kolmogorov-calibrated modes whose projected tail state uses the
-- monotone v2/v7 termination surface, while v3 cascade flux remains
-- diagnostic-only.

data NSFractranKolmogorovSubclassStatus : Set where
  kolmogorovSubclassDecidable_generalFractranAdmissibilityOpen :
    NSFractranKolmogorovSubclassStatus

data NSFractranKolmogorovComponent : Set where
  fractranGeneralTuringCompleteBoundary :
    NSFractranKolmogorovComponent

  kolmogorovCalibratedSubclass :
    NSFractranKolmogorovComponent

  v2v7TerminationSurface :
    NSFractranKolmogorovComponent

  v3DiagnosticOnly :
    NSFractranKolmogorovComponent

  forwardSimulationStillOpen :
    NSFractranKolmogorovComponent

canonicalNSFractranKolmogorovComponents :
  List NSFractranKolmogorovComponent
canonicalNSFractranKolmogorovComponents =
  fractranGeneralTuringCompleteBoundary
  ∷ kolmogorovCalibratedSubclass
  ∷ v2v7TerminationSurface
  ∷ v3DiagnosticOnly
  ∷ forwardSimulationStillOpen
  ∷ []

data NSFractranKolmogorovPromotion : Set where

nsFractranKolmogorovPromotionImpossible :
  NSFractranKolmogorovPromotion →
  ⊥
nsFractranKolmogorovPromotionImpossible ()

generalFRACTRANBoundaryStatement :
  String
generalFRACTRANBoundaryStatement =
  "General FRACTRAN admissibility is not promoted as decidable here; unrestricted FRACTRAN is Turing-complete, so the general NS-to-FRACTRAN admissibility problem remains open."

kolmogorovSubclassStatement :
  String
kolmogorovSubclassStatement =
  "Kolmogorov-calibrated carrier states are recorded as the decidable subclass: the NS-facing termination/Lyapunov surface uses v2 and v7 only, and v3 cascade flux is diagnostic-only."

remainingNSObligationStatement :
  String
remainingNSObligationStatement =
  "Clay-level or unconditional NS regularity still requires NS-to-EV5 forward simulation, quotient correctness, Lyapunov preservation, and ultrametric preservation for actual NS flow."

record NSFractranAdmissibilityDecidableForKolmogorovSubclassReceipt : Set₁ where
  field
    status :
      NSFractranKolmogorovSubclassStatus

    statusIsKolmogorovSubclassOnly :
      status
      ≡
      kolmogorovSubclassDecidable_generalFractranAdmissibilityOpen

    tailReceipt :
      Tail.NSFractranTailAdmissibilityReceipt

    tailReceiptIsCanonical :
      tailReceipt ≡ Tail.canonicalNSFractranTailAdmissibilityReceipt

    projectionReceipt :
      Projection.NSToEV5ProjectionFrontierReceipt

    projectionReceiptIsCanonical :
      projectionReceipt ≡ Projection.canonicalNSToEV5ProjectionFrontierReceipt

    nsTerminationEnergyPrimeLanes :
      Tail.nsTerminationEnergyPrimeLanes tailReceipt ≡ (2 ∷ 7 ∷ [])

    projectionTerminationEnergyPrimeLanes :
      Projection.terminationEnergyActivePrimeLanes projectionReceipt
      ≡
      (2 ∷ 7 ∷ [])

    v3TailDiagnosticOnly :
      Tail.v3CascadeFluxDiagnosticOnly tailReceipt ≡ true

    v3ProjectionDiagnosticOnly :
      Projection.v3CascadeFluxDiagnosticOnly projectionReceipt ≡ true

    v3ExcludedFromTailTermination :
      Tail.v3ExcludedFromNSTerminationEnergy tailReceipt ≡ true

    v3ExcludedFromProjectionTermination :
      Projection.v3ExcludedFromTerminationEnergy projectionReceipt ≡ true

    v3PromotedToNSRegularityProofFalse :
      Tail.v3PromotedToNSRegularityProof tailReceipt ≡ false

    carrierProjectionFractranAdmissibleForSubclass :
      Tail.carrierProjectionFractranAdmissibleTerminating tailReceipt
      ≡
      true

    generalFractranAdmissibilityDecidableHere :
      Bool

    generalFractranAdmissibilityDecidableHereIsFalse :
      generalFractranAdmissibilityDecidableHere ≡ false

    kolmogorovSubclassDecidableHere :
      Bool

    kolmogorovSubclassDecidableHereIsTrue :
      kolmogorovSubclassDecidableHere ≡ true

    nsToEV5ForwardSimulationProvedHere :
      Bool

    nsToEV5ForwardSimulationProvedHereIsFalse :
      nsToEV5ForwardSimulationProvedHere ≡ false

    unconditionalNSRegularityPromoted :
      Bool

    unconditionalNSRegularityPromotedIsFalse :
      unconditionalNSRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    components :
      List NSFractranKolmogorovComponent

    componentsAreCanonical :
      components ≡ canonicalNSFractranKolmogorovComponents

    generalBoundary :
      String

    generalBoundaryIsCanonical :
      generalBoundary ≡ generalFRACTRANBoundaryStatement

    subclassStatement :
      String

    subclassStatementIsCanonical :
      subclassStatement ≡ kolmogorovSubclassStatement

    remainingNSObligation :
      String

    remainingNSObligationIsCanonical :
      remainingNSObligation ≡ remainingNSObligationStatement

    promotionFlags :
      List NSFractranKolmogorovPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open NSFractranAdmissibilityDecidableForKolmogorovSubclassReceipt public

canonicalNSFractranAdmissibilityDecidableForKolmogorovSubclassReceipt :
  NSFractranAdmissibilityDecidableForKolmogorovSubclassReceipt
canonicalNSFractranAdmissibilityDecidableForKolmogorovSubclassReceipt =
  record
    { status =
        kolmogorovSubclassDecidable_generalFractranAdmissibilityOpen
    ; statusIsKolmogorovSubclassOnly =
        refl
    ; tailReceipt =
        Tail.canonicalNSFractranTailAdmissibilityReceipt
    ; tailReceiptIsCanonical =
        refl
    ; projectionReceipt =
        Projection.canonicalNSToEV5ProjectionFrontierReceipt
    ; projectionReceiptIsCanonical =
        refl
    ; nsTerminationEnergyPrimeLanes =
        refl
    ; projectionTerminationEnergyPrimeLanes =
        refl
    ; v3TailDiagnosticOnly =
        refl
    ; v3ProjectionDiagnosticOnly =
        refl
    ; v3ExcludedFromTailTermination =
        refl
    ; v3ExcludedFromProjectionTermination =
        refl
    ; v3PromotedToNSRegularityProofFalse =
        refl
    ; carrierProjectionFractranAdmissibleForSubclass =
        refl
    ; generalFractranAdmissibilityDecidableHere =
        false
    ; generalFractranAdmissibilityDecidableHereIsFalse =
        refl
    ; kolmogorovSubclassDecidableHere =
        true
    ; kolmogorovSubclassDecidableHereIsTrue =
        refl
    ; nsToEV5ForwardSimulationProvedHere =
        false
    ; nsToEV5ForwardSimulationProvedHereIsFalse =
        refl
    ; unconditionalNSRegularityPromoted =
        false
    ; unconditionalNSRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; components =
        canonicalNSFractranKolmogorovComponents
    ; componentsAreCanonical =
        refl
    ; generalBoundary =
        generalFRACTRANBoundaryStatement
    ; generalBoundaryIsCanonical =
        refl
    ; subclassStatement =
        kolmogorovSubclassStatement
    ; subclassStatementIsCanonical =
        refl
    ; remainingNSObligation =
        remainingNSObligationStatement
    ; remainingNSObligationIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

nsFractranKolmogorovSubclassNoClayPromotion :
  clayNavierStokesPromoted
    canonicalNSFractranAdmissibilityDecidableForKolmogorovSubclassReceipt
  ≡
  false
nsFractranKolmogorovSubclassNoClayPromotion =
  refl
