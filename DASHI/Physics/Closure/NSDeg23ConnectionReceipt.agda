module DASHI.Physics.Closure.NSDeg23ConnectionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Deg23DirectIsogenyReceipt as Direct
import DASHI.Physics.Closure.Deg23FaltingsComputationReceipt as Faltings
import DASHI.Physics.Closure.Deg23PerturbativeReceipt as Perturbative
import DASHI.Physics.Closure.Deg23ResidualDiagnosticReceipt as Residual
import DASHI.Physics.Closure.Deg23RGRunningHypothesisReceipt as RG
import DASHI.Physics.Closure.ZetaK21ComputationReceipt as Zeta

------------------------------------------------------------------------
-- deg23 connection diagnostic for the Navier-Stokes lane.
--
-- ZetaK21ComputationReceipt records zeta_Q(sqrt(21))(-1)=1/3.  This receipt
-- audits that arithmetic diagnostic against the natural deg23 normalisations
-- without promoting CKM or Clay evidence.

data Deg23NormalisationTest : Set where
  pointCountSumEF5EF7 :
    Deg23NormalisationTest

  firstOrderAlpha1OverTwo :
    Deg23NormalisationTest

  geometricOneOverOneMinusAlpha1OverTwo :
    Deg23NormalisationTest

  qcdP5ToP7Running :
    Deg23NormalisationTest

  faltingsHeightCorrection :
    Deg23NormalisationTest

  zetaK21Computation :
    Deg23NormalisationTest

canonicalDeg23NormalisationTests :
  List Deg23NormalisationTest
canonicalDeg23NormalisationTests =
  pointCountSumEF5EF7
  ∷ firstOrderAlpha1OverTwo
  ∷ geometricOneOverOneMinusAlpha1OverTwo
  ∷ qcdP5ToP7Running
  ∷ faltingsHeightCorrection
  ∷ zetaK21Computation
  ∷ []

data Deg23DiagnosticStatus : Set where
  positiveDiagnostic :
    Deg23DiagnosticStatus

  negativeDiagnostic :
    Deg23DiagnosticStatus

  zetaK21NegativeDiagnostic :
    Deg23DiagnosticStatus

canonicalDeg23DiagnosticStatuses :
  List Deg23DiagnosticStatus
canonicalDeg23DiagnosticStatuses =
  negativeDiagnostic
  ∷ positiveDiagnostic
  ∷ positiveDiagnostic
  ∷ negativeDiagnostic
  ∷ negativeDiagnostic
  ∷ zetaK21NegativeDiagnostic
  ∷ []

data Deg23ConnectionBlocker : Set where
  zetaK21NaturalNormalisationsMiss :
    Deg23ConnectionBlocker

  pointCountDeg23LeavesResidual :
    Deg23ConnectionBlocker

  perturbativeAlphaDiagnosticNotPhysicalCKM :
    Deg23ConnectionBlocker

  rgRunningNaturalScaleOvershoots :
    Deg23ConnectionBlocker

  faltingsCorrectionOvershoots :
    Deg23ConnectionBlocker

  noNavierStokesMechanismFromDeg23 :
    Deg23ConnectionBlocker

canonicalDeg23ConnectionBlockers :
  List Deg23ConnectionBlocker
canonicalDeg23ConnectionBlockers =
  zetaK21NaturalNormalisationsMiss
  ∷ pointCountDeg23LeavesResidual
  ∷ perturbativeAlphaDiagnosticNotPhysicalCKM
  ∷ rgRunningNaturalScaleOvershoots
  ∷ faltingsCorrectionOvershoots
  ∷ noNavierStokesMechanismFromDeg23
  ∷ []

data Deg23ConnectionPromotion : Set where

deg23ConnectionPromotionImpossibleHere :
  Deg23ConnectionPromotion →
  ⊥
deg23ConnectionPromotionImpossibleHere ()

deg23ConnectionStatement : String
deg23ConnectionStatement =
  "Natural deg23 normalisations are audited against point-count, perturbative alpha, RG-running, Faltings-height, and zeta_Q(sqrt(21))(-1)=1/3.  Positive diagnostics remain diagnostics only; negative diagnostics stay blockers."

record NSDeg23ConnectionReceipt : Setω where
  field
    residualReceipt :
      Residual.Deg23ResidualDiagnosticReceipt

    residualReceiptIsCanonical :
      residualReceipt ≡ Residual.canonicalDeg23ResidualDiagnosticReceipt

    directReceipt :
      Direct.Deg23DirectIsogenyReceipt

    directDeg23StillUnderived :
      Direct.deg23FormulaUnderived directReceipt ≡ true

    perturbativeReceipt :
      Perturbative.Deg23PerturbativeReceipt

    perturbativeADiagnosticPositive :
      Perturbative.wolfensteinADiagnosticImproved perturbativeReceipt ≡ true

    perturbativeCKMPromotionFalse :
      Perturbative.physicalCKMPromoted perturbativeReceipt ≡ false

    rgReceipt :
      RG.Deg23RGRunningHypothesisReceipt

    rgNaturalScaleNegative :
      RG.naturalP5P7RunningResolvesResidual rgReceipt ≡ false

    faltingsReceipt :
      Faltings.Deg23FaltingsComputationReceipt

    faltingsCorrectionNegative :
      Faltings.faltingsCorrectionResolvesDeg23Residual faltingsReceipt
      ≡
      false

    zetaReceipt :
      Zeta.ZetaK21ComputationReceipt

    zetaArithmeticDiagnosticComplete :
      Zeta.arithmeticDiagnosticComplete zetaReceipt ≡ true

    zetaDoesNotDeriveDeg23 :
      Zeta.deg23DerivedFromZeta zetaReceipt ≡ false

    zetaK21ComputationReceiptAvailable :
      Bool

    zetaK21ComputationReceiptAvailableIsTrue :
      zetaK21ComputationReceiptAvailable ≡ true

    tests :
      List Deg23NormalisationTest

    testsAreCanonical :
      tests ≡ canonicalDeg23NormalisationTests

    diagnosticStatuses :
      List Deg23DiagnosticStatus

    diagnosticStatusesAreCanonical :
      diagnosticStatuses ≡ canonicalDeg23DiagnosticStatuses

    systematicNormalisationScanRecorded :
      Bool

    systematicNormalisationScanRecordedIsTrue :
      systematicNormalisationScanRecorded ≡ true

    positiveDiagnosticsRecorded :
      Bool

    positiveDiagnosticsRecordedIsTrue :
      positiveDiagnosticsRecorded ≡ true

    negativeDiagnosticsRecorded :
      Bool

    negativeDiagnosticsRecordedIsTrue :
      negativeDiagnosticsRecorded ≡ true

    deg23ConnectionToNavierStokesPromoted :
      Bool

    deg23ConnectionToNavierStokesPromotedIsFalse :
      deg23ConnectionToNavierStokesPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    blockers :
      List Deg23ConnectionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalDeg23ConnectionBlockers

    promotionFlags :
      List Deg23ConnectionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ deg23ConnectionStatement

    receiptBoundary :
      List String

open NSDeg23ConnectionReceipt public

canonicalNSDeg23ConnectionReceipt :
  NSDeg23ConnectionReceipt
canonicalNSDeg23ConnectionReceipt =
  record
    { residualReceipt =
        Residual.canonicalDeg23ResidualDiagnosticReceipt
    ; residualReceiptIsCanonical =
        refl
    ; directReceipt =
        Direct.canonicalDeg23DirectIsogenyReceipt
    ; directDeg23StillUnderived =
        refl
    ; perturbativeReceipt =
        Perturbative.canonicalDeg23PerturbativeReceipt
    ; perturbativeADiagnosticPositive =
        refl
    ; perturbativeCKMPromotionFalse =
        refl
    ; rgReceipt =
        RG.canonicalDeg23RGRunningHypothesisReceipt
    ; rgNaturalScaleNegative =
        refl
    ; faltingsReceipt =
        Faltings.canonicalDeg23FaltingsComputationReceipt
    ; faltingsCorrectionNegative =
        refl
    ; zetaReceipt =
        Zeta.canonicalZetaK21ComputationReceipt
    ; zetaArithmeticDiagnosticComplete =
        refl
    ; zetaDoesNotDeriveDeg23 =
        refl
    ; zetaK21ComputationReceiptAvailable =
        true
    ; zetaK21ComputationReceiptAvailableIsTrue =
        refl
    ; tests =
        canonicalDeg23NormalisationTests
    ; testsAreCanonical =
        refl
    ; diagnosticStatuses =
        canonicalDeg23DiagnosticStatuses
    ; diagnosticStatusesAreCanonical =
        refl
    ; systematicNormalisationScanRecorded =
        true
    ; systematicNormalisationScanRecordedIsTrue =
        refl
    ; positiveDiagnosticsRecorded =
        true
    ; positiveDiagnosticsRecordedIsTrue =
        refl
    ; negativeDiagnosticsRecorded =
        true
    ; negativeDiagnosticsRecordedIsTrue =
        refl
    ; deg23ConnectionToNavierStokesPromoted =
        false
    ; deg23ConnectionToNavierStokesPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; blockers =
        canonicalDeg23ConnectionBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        deg23ConnectionStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "ZetaK21ComputationReceipt records zeta_Q(sqrt(21))(-1)=1/3, but the tested natural normalisations do not close deg23"
        ∷ "The point-count deg23=14, natural RG-running, Faltings correction, and zeta route are negative diagnostics for closing the residual"
        ∷ "The first-order and geometric alpha tests are positive Wolfenstein-A diagnostics only"
        ∷ "No Navier-Stokes mechanism, CKM promotion, or Clay promotion is asserted"
        ∷ []
    }

nsDeg23ZetaK21Available :
  zetaK21ComputationReceiptAvailable canonicalNSDeg23ConnectionReceipt
  ≡
  true
nsDeg23ZetaK21Available =
  refl

nsDeg23DoesNotPromoteCKM :
  physicalCKMPromoted canonicalNSDeg23ConnectionReceipt ≡ false
nsDeg23DoesNotPromoteCKM =
  refl

nsDeg23DoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSDeg23ConnectionReceipt ≡ false
nsDeg23DoesNotPromoteClay =
  refl
