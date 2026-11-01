module DASHI.Physics.Closure.UnificationFourPointCancellationFromCrossTermNullityBoundary where

-- Boundary route:
--
--   UnificationCrossTermNullityTheoremBoundary
--   + UnificationGluingModuloNullLinearityCompositeBoundary
--   + GluingResidualForcesFourPointCancellationBoundary
--   -> four-point cancellation consumer.
--
-- This module records the proof spine and the exact consumer sockets:
--
--   additive test functional
--   quotient representative invariance
--   polarization / four-point residual
--   parallelogram consumer
--
-- It deliberately does not prove actual four-point cancellation, the
-- parallelogram law, quadratic emergence, or terminal unification promotion.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.UnificationCrossTermNullityTheoremBoundary
  as CrossTerm
import DASHI.Physics.Closure.UnificationGluingModuloNullLinearityCompositeBoundary
  as ModuloNull
import DASHI.Physics.Closure.GluingResidualForcesFourPointCancellationBoundary
  as Residual

------------------------------------------------------------------------
-- Local utilities.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Additive test functional socket.

record AdditiveTestFunctionalSurface : Setω where
  field
    Carrier :
      Set

    Value :
      Set

    zeroCarrier :
      Carrier

    _+c_ :
      Carrier → Carrier → Carrier

    -c_ :
      Carrier → Carrier

    zeroValue :
      Value

    _+v_ :
      Value → Value → Value

    -v_ :
      Value → Value

    T :
      Carrier → Value

open AdditiveTestFunctionalSurface public

additiveCrossTerm :
  (surface : AdditiveTestFunctionalSurface) →
  Carrier surface →
  Carrier surface →
  Value surface
additiveCrossTerm surface x y =
  _+v_ surface
    (_+v_ surface
      (T surface (_+c_ surface x y))
      (-v_ surface (T surface x)))
    (-v_ surface (T surface y))

record AdditiveTestFunctionalTarget
  (surface : AdditiveTestFunctionalSurface) : Setω where
  field
    additiveCrossTermNull :
      Value surface → Set

    additiveZeroTarget :
      T surface (zeroCarrier surface) ≡ zeroValue surface

    additiveTestFunctionalRoute :
      (x y : Carrier surface) →
      additiveCrossTermNull (additiveCrossTerm surface x y)

    targetText :
      String

    targetTextIsCanonical :
      targetText
      ≡ "forall x y, additiveCrossTermNull (T(x+y)-T(x)-T(y))"

open AdditiveTestFunctionalTarget public

------------------------------------------------------------------------
-- Quotient representative invariance socket.

record QuotientRepresentativeInvarianceSurface : Setω where
  field
    QuotientCarrier :
      Set

    Representative :
      Set

    represents :
      Representative → QuotientCarrier → Set

    representativeEquivalent :
      Representative → Representative → Set

    quotientEquivalent :
      QuotientCarrier → QuotientCarrier → Set

    residualClass :
      QuotientCarrier → Set

open QuotientRepresentativeInvarianceSurface public

record QuotientRepresentativeInvarianceTarget
  (surface : QuotientRepresentativeInvarianceSurface) : Setω where
  field
    quotientRepresentativeInvariance :
      (r s : Representative surface) →
      (x y : QuotientCarrier surface) →
      represents surface r x →
      represents surface s y →
      representativeEquivalent surface r s →
      quotientEquivalent surface x y

    residualRepresentativeInvariance :
      (x y : QuotientCarrier surface) →
      quotientEquivalent surface x y →
      residualClass surface x →
      residualClass surface y

    targetText :
      String

    targetTextIsCanonical :
      targetText
      ≡ "representative-equivalent residuals transport across quotient representatives"

open QuotientRepresentativeInvarianceTarget public

------------------------------------------------------------------------
-- Polarization and four-point residual socket.

record PolarizationFourPointResidualSurface : Setω where
  field
    Point :
      Set

    ResidualValue :
      Set

    zeroResidual :
      ResidualValue

    _+p_ :
      Point → Point → Point

    -p_ :
      Point → Point

    _+r_ :
      ResidualValue → ResidualValue → ResidualValue

    -r_ :
      ResidualValue → ResidualValue

    Q :
      Point → ResidualValue

open PolarizationFourPointResidualSurface public

pointDifference :
  (surface : PolarizationFourPointResidualSurface) →
  Point surface →
  Point surface →
  Point surface
pointDifference surface x y =
  _+p_ surface x (-p_ surface y)

twiceResidual :
  (surface : PolarizationFourPointResidualSurface) →
  ResidualValue surface →
  ResidualValue surface
twiceResidual surface value =
  _+r_ surface value value

fourPointResidual :
  (surface : PolarizationFourPointResidualSurface) →
  Point surface →
  Point surface →
  ResidualValue surface
fourPointResidual surface x y =
  _+r_ surface
    (_+r_ surface
      (Q surface (_+p_ surface x y))
      (Q surface (pointDifference surface x y)))
    (-r_ surface
      (_+r_ surface
        (twiceResidual surface (Q surface x))
        (twiceResidual surface (Q surface y))))

record PolarizationFourPointResidualTarget
  (surface : PolarizationFourPointResidualSurface) : Setω where
  field
    gluingResidualNull :
      ResidualValue surface → Set

    polarizationResidualRecorded :
      Bool

    polarizationResidualRecordedIsTrue :
      polarizationResidualRecorded ≡ true

    fourPointResidualTarget :
      (x y : Point surface) →
      gluingResidualNull (fourPointResidual surface x y)

    targetText :
      String

    targetTextIsCanonical :
      targetText
      ≡ "gluing/polarization residual forces Q(x+y)+Q(x-y)-2Q(x)-2Q(y)=0"

open PolarizationFourPointResidualTarget public

------------------------------------------------------------------------
-- Parallelogram consumer socket.

record ParallelogramConsumerSurface : Setω where
  field
    ParallelogramPoint :
      Set

    ParallelogramValue :
      Set

    _+pc_ :
      ParallelogramPoint →
      ParallelogramPoint →
      ParallelogramPoint

    -pc_ :
      ParallelogramPoint → ParallelogramPoint

    _+pv_ :
      ParallelogramValue →
      ParallelogramValue →
      ParallelogramValue

    defect :
      ParallelogramPoint → ParallelogramValue

open ParallelogramConsumerSurface public

parallelogramLeft :
  (surface : ParallelogramConsumerSurface) →
  ParallelogramPoint surface →
  ParallelogramPoint surface →
  ParallelogramValue surface
parallelogramLeft surface x y =
  _+pv_ surface
    (defect surface (_+pc_ surface x y))
    (defect surface (_+pc_ surface x (-pc_ surface y)))

parallelogramRight :
  (surface : ParallelogramConsumerSurface) →
  ParallelogramPoint surface →
  ParallelogramPoint surface →
  ParallelogramValue surface
parallelogramRight surface x y =
  _+pv_ surface
    (_+pv_ surface (defect surface x) (defect surface x))
    (_+pv_ surface (defect surface y) (defect surface y))

record ParallelogramConsumerTarget
  (surface : ParallelogramConsumerSurface) : Setω where
  field
    fourPointCancellationInput :
      (x y : ParallelogramPoint surface) →
      parallelogramLeft surface x y
      ≡
      parallelogramRight surface x y

    parallelogramConsumerText :
      String

    parallelogramConsumerTextIsCanonical :
      parallelogramConsumerText
      ≡ "four-point cancellation is the exact input consumed by the parallelogram law"

open ParallelogramConsumerTarget public

------------------------------------------------------------------------
-- Imported support from the three required boundaries.

record FourPointCancellationRouteImportedSupport : Setω where
  field
    crossTermNullityBoundary :
      CrossTerm.UnificationCrossTermNullityTheoremBoundary

    moduloNullLinearityBoundary :
      ModuloNull.UnificationGluingModuloNullLinearityCompositeBoundary

    gluingResidualFourPointBoundary :
      Residual.GluingResidualForcesFourPointCancellationBoundary

    crossTermTargetRecorded :
      CrossTerm.actualTheoremTargetRecorded crossTermNullityBoundary
      ≡ true

    crossTermRepresentativeInvarianceStillOpen :
      CrossTerm.representativeInvarianceProved crossTermNullityBoundary
      ≡ false

    crossTermTheoremStillOpen :
      CrossTerm.crossTermNullityTheoremProved crossTermNullityBoundary
      ≡ false

    crossTermFourPointConsumerStillOpen :
      CrossTerm.fourPointConsumerProved crossTermNullityBoundary
      ≡ false

    crossTermParallelogramStillOpen :
      CrossTerm.parallelogramProved crossTermNullityBoundary
      ≡ false

    crossTermQuadraticStillBlocked :
      CrossTerm.quadraticEmergenceProved crossTermNullityBoundary
      ≡ false

    crossTermTerminalPromotionFalse :
      CrossTerm.terminalPromotion crossTermNullityBoundary
      ≡ false

    moduloRepresentativeInvarianceStillOpen :
      ModuloNull.representativeInvarianceProved moduloNullLinearityBoundary
      ≡ false

    moduloCrossTermNullTransportStillOpen :
      ModuloNull.crossTermNullTransportProved moduloNullLinearityBoundary
      ≡ false

    moduloQuotientEqualityStillOpen :
      ModuloNull.quotientEqualityProved moduloNullLinearityBoundary
      ≡ false

    moduloFourPointRouteRecorded :
      ModuloNull.fourPointCancellationRouteRecorded
        moduloNullLinearityBoundary
      ≡ true

    moduloFourPointCancellationStillOpen :
      ModuloNull.actualFourPointCancellationProved
        moduloNullLinearityBoundary
      ≡ false

    moduloParallelogramStillOpen :
      ModuloNull.parallelogramProved moduloNullLinearityBoundary
      ≡ false

    moduloQuadraticStillBlocked :
      ModuloNull.quadraticEmergenceProved moduloNullLinearityBoundary
      ≡ false

    moduloTerminalPromotionFalse :
      ModuloNull.terminalUnificationPromotion moduloNullLinearityBoundary
      ≡ false

    residualPolarizationRequired :
      Residual.gluingPolarizationResidualRequired
        gluingResidualFourPointBoundary
      ≡ true

    residualTheoremStillOpen :
      Residual.gluingResidualForcesFourPointCancellationProved
        gluingResidualFourPointBoundary
      ≡ false

    residualFourPointStillOpen :
      Residual.fourPointDefectVanishes
        gluingResidualFourPointBoundary
      ≡ false

    residualParallelogramStillOpen :
      Residual.parallelogramLawProved
        gluingResidualFourPointBoundary
      ≡ false

    residualQuadraticStillBlocked :
      Residual.quadraticFormEmergenceApplied
        gluingResidualFourPointBoundary
      ≡ false

    residualTerminalPromotionFalse :
      Residual.terminalUnificationPromoted
        gluingResidualFourPointBoundary
      ≡ false

open FourPointCancellationRouteImportedSupport public

canonicalFourPointCancellationRouteImportedSupport :
  FourPointCancellationRouteImportedSupport
canonicalFourPointCancellationRouteImportedSupport =
  record
    { crossTermNullityBoundary =
        CrossTerm.canonicalUnificationCrossTermNullityTheoremBoundary
    ; moduloNullLinearityBoundary =
        ModuloNull.canonicalUnificationGluingModuloNullLinearityCompositeBoundary
    ; gluingResidualFourPointBoundary =
        Residual.canonicalGluingResidualForcesFourPointCancellationBoundary
    ; crossTermTargetRecorded =
        CrossTerm.canonicalCrossTermNullityActualTargetRecorded
    ; crossTermRepresentativeInvarianceStillOpen =
        CrossTerm.canonicalCrossTermNullityRepresentativeInvarianceStillOpen
    ; crossTermTheoremStillOpen =
        CrossTerm.canonicalCrossTermNullityTheoremStillOpen
    ; crossTermFourPointConsumerStillOpen =
        CrossTerm.canonicalCrossTermNullityFourPointConsumerStillOpen
    ; crossTermParallelogramStillOpen =
        CrossTerm.canonicalCrossTermNullityParallelogramStillOpen
    ; crossTermQuadraticStillBlocked =
        CrossTerm.canonicalCrossTermNullityQuadraticStillBlocked
    ; crossTermTerminalPromotionFalse =
        CrossTerm.canonicalCrossTermNullityTerminalPromotionFalse
    ; moduloRepresentativeInvarianceStillOpen =
        ModuloNull.canonicalModuloNullRepresentativeInvarianceStillOpen
    ; moduloCrossTermNullTransportStillOpen =
        ModuloNull.canonicalModuloNullCrossTermNullTransportStillOpen
    ; moduloQuotientEqualityStillOpen =
        ModuloNull.canonicalModuloNullQuotientEqualityStillOpen
    ; moduloFourPointRouteRecorded =
        ModuloNull.canonicalModuloNullFourPointRouteRecorded
    ; moduloFourPointCancellationStillOpen =
        ModuloNull.canonicalModuloNullActualFourPointCancellationStillOpen
    ; moduloParallelogramStillOpen =
        ModuloNull.canonicalModuloNullParallelogramStillOpen
    ; moduloQuadraticStillBlocked =
        ModuloNull.canonicalModuloNullQuadraticStillBlocked
    ; moduloTerminalPromotionFalse =
        ModuloNull.canonicalModuloNullTerminalPromotionFalse
    ; residualPolarizationRequired =
        Residual.canonicalGluingPolarizationResidualRequired
    ; residualTheoremStillOpen =
        Residual.canonicalGluingResidualForcesFourPointCancellationStillOpen
    ; residualFourPointStillOpen =
        Residual.canonicalFourPointDefectStillOpen
    ; residualParallelogramStillOpen =
        Residual.canonicalParallelogramLawStillOpen
    ; residualQuadraticStillBlocked =
        Residual.canonicalQuadraticFormEmergenceStillBlocked
    ; residualTerminalPromotionFalse =
        Residual.canonicalTerminalUnificationPromotionFalse
    }

------------------------------------------------------------------------
-- Route rows.

data FourPointCancellationRouteStage : Set where
  crossTermNullityImported :
    FourPointCancellationRouteStage

  additiveTestFunctionalStage :
    FourPointCancellationRouteStage

  quotientRepresentativeInvarianceStage :
    FourPointCancellationRouteStage

  moduloNullLinearityRouteStage :
    FourPointCancellationRouteStage

  polarizationResidualStage :
    FourPointCancellationRouteStage

  gluingResidualForcesFourPointStage :
    FourPointCancellationRouteStage

  actualFourPointCancellationStage :
    FourPointCancellationRouteStage

  parallelogramConsumerStage :
    FourPointCancellationRouteStage

  quadraticEmergenceConsumerStage :
    FourPointCancellationRouteStage

  terminalPromotionGate :
    FourPointCancellationRouteStage

data FourPointCancellationRouteStatus : Set where
  importedBoundary :
    FourPointCancellationRouteStatus

  targetRecorded :
    FourPointCancellationRouteStatus

  prerequisiteOpen :
    FourPointCancellationRouteStatus

  routeRecorded :
    FourPointCancellationRouteStatus

  theoremOpen :
    FourPointCancellationRouteStatus

  downstreamBlocked :
    FourPointCancellationRouteStatus

  promotionHeld :
    FourPointCancellationRouteStatus

canonicalFourPointCancellationRouteStatus :
  FourPointCancellationRouteStage →
  FourPointCancellationRouteStatus
canonicalFourPointCancellationRouteStatus crossTermNullityImported =
  importedBoundary
canonicalFourPointCancellationRouteStatus additiveTestFunctionalStage =
  targetRecorded
canonicalFourPointCancellationRouteStatus quotientRepresentativeInvarianceStage =
  prerequisiteOpen
canonicalFourPointCancellationRouteStatus moduloNullLinearityRouteStage =
  routeRecorded
canonicalFourPointCancellationRouteStatus polarizationResidualStage =
  targetRecorded
canonicalFourPointCancellationRouteStatus gluingResidualForcesFourPointStage =
  theoremOpen
canonicalFourPointCancellationRouteStatus actualFourPointCancellationStage =
  theoremOpen
canonicalFourPointCancellationRouteStatus parallelogramConsumerStage =
  downstreamBlocked
canonicalFourPointCancellationRouteStatus quadraticEmergenceConsumerStage =
  downstreamBlocked
canonicalFourPointCancellationRouteStatus terminalPromotionGate =
  promotionHeld

data FourPointCancellationRouteBlocker : Set where
  noBlockerForImportedBoundary :
    FourPointCancellationRouteBlocker

  noBlockerForRecordedTarget :
    FourPointCancellationRouteBlocker

  missingQuotientRepresentativeInvariance :
    FourPointCancellationRouteBlocker

  missingModuloNullQuotientEquality :
    FourPointCancellationRouteBlocker

  missingGluingPolarizationResidualTheorem :
    FourPointCancellationRouteBlocker

  missingActualFourPointCancellation :
    FourPointCancellationRouteBlocker

  missingParallelogramConsumer :
    FourPointCancellationRouteBlocker

  missingQuadraticConsumer :
    FourPointCancellationRouteBlocker

  noTerminalPromotionAuthority :
    FourPointCancellationRouteBlocker

canonicalFourPointCancellationRouteBlocker :
  FourPointCancellationRouteStage →
  FourPointCancellationRouteBlocker
canonicalFourPointCancellationRouteBlocker crossTermNullityImported =
  noBlockerForImportedBoundary
canonicalFourPointCancellationRouteBlocker additiveTestFunctionalStage =
  noBlockerForRecordedTarget
canonicalFourPointCancellationRouteBlocker quotientRepresentativeInvarianceStage =
  missingQuotientRepresentativeInvariance
canonicalFourPointCancellationRouteBlocker moduloNullLinearityRouteStage =
  missingModuloNullQuotientEquality
canonicalFourPointCancellationRouteBlocker polarizationResidualStage =
  noBlockerForRecordedTarget
canonicalFourPointCancellationRouteBlocker gluingResidualForcesFourPointStage =
  missingGluingPolarizationResidualTheorem
canonicalFourPointCancellationRouteBlocker actualFourPointCancellationStage =
  missingActualFourPointCancellation
canonicalFourPointCancellationRouteBlocker parallelogramConsumerStage =
  missingParallelogramConsumer
canonicalFourPointCancellationRouteBlocker quadraticEmergenceConsumerStage =
  missingQuadraticConsumer
canonicalFourPointCancellationRouteBlocker terminalPromotionGate =
  noTerminalPromotionAuthority

record FourPointCancellationRouteRow : Set where
  field
    stage :
      FourPointCancellationRouteStage

    status :
      FourPointCancellationRouteStatus

    statusIsCanonical :
      status ≡ canonicalFourPointCancellationRouteStatus stage

    blocker :
      FourPointCancellationRouteBlocker

    blockerIsCanonical :
      blocker ≡ canonicalFourPointCancellationRouteBlocker stage

    routeContract :
      String

    importedSurface :
      String

    provedOrPromotedHere :
      Bool

    provedOrPromotedHereIsFalse :
      provedOrPromotedHere ≡ false

open FourPointCancellationRouteRow public

mkFourPointCancellationRouteRow :
  FourPointCancellationRouteStage →
  String →
  String →
  FourPointCancellationRouteRow
mkFourPointCancellationRouteRow stage routeContract importedSurface =
  record
    { stage =
        stage
    ; status =
        canonicalFourPointCancellationRouteStatus stage
    ; statusIsCanonical =
        refl
    ; blocker =
        canonicalFourPointCancellationRouteBlocker stage
    ; blockerIsCanonical =
        refl
    ; routeContract =
        routeContract
    ; importedSurface =
        importedSurface
    ; provedOrPromotedHere =
        false
    ; provedOrPromotedHereIsFalse =
        refl
    }

canonicalFourPointCancellationRouteRows :
  List FourPointCancellationRouteRow
canonicalFourPointCancellationRouteRows =
  mkFourPointCancellationRouteRow
    crossTermNullityImported
    "consume the recorded U-1a cross-term nullity theorem target"
    "UnificationCrossTermNullityTheoremBoundary"
  ∷ mkFourPointCancellationRouteRow
    additiveTestFunctionalStage
    "record additive test functional T and target T(x+y)-T(x)-T(y) in the null class"
    "AdditiveTestFunctionalTarget"
  ∷ mkFourPointCancellationRouteRow
    quotientRepresentativeInvarianceStage
    "require representative-invariant transport of residual nullity on the quotient"
    "CrossTerm and ModuloNull representative-invariance guards"
  ∷ mkFourPointCancellationRouteRow
    moduloNullLinearityRouteStage
    "route cross-term nullity through modulo-null gluing linearity and quotient equality"
    "UnificationGluingModuloNullLinearityCompositeBoundary"
  ∷ mkFourPointCancellationRouteRow
    polarizationResidualStage
    "record polarization residual Q(x+y)+Q(x-y)-2Q(x)-2Q(y)"
    "PolarizationFourPointResidualTarget"
  ∷ mkFourPointCancellationRouteRow
    gluingResidualForcesFourPointStage
    "consume the stronger gluing residual forces four-point cancellation theorem target"
    "GluingResidualForcesFourPointCancellationBoundary"
  ∷ mkFourPointCancellationRouteRow
    actualFourPointCancellationStage
    "actual four-point cancellation remains the unproved theorem output of the route"
    "Residual four-point target"
  ∷ mkFourPointCancellationRouteRow
    parallelogramConsumerStage
    "parallelogram consumer waits for actual four-point cancellation"
    "ParallelogramConsumerTarget"
  ∷ mkFourPointCancellationRouteRow
    quadraticEmergenceConsumerStage
    "quadratic emergence waits for parallelogram"
    "Defect four-point/parallelogram boundary"
  ∷ mkFourPointCancellationRouteRow
    terminalPromotionGate
    "terminal unification promotion remains held"
    "all imported promotion gates"
  ∷ []

canonicalFourPointCancellationRouteRowCount : Nat
canonicalFourPointCancellationRouteRowCount =
  listLength canonicalFourPointCancellationRouteRows

canonicalFourPointCancellationRouteRowCountIs10 :
  canonicalFourPointCancellationRouteRowCount ≡ 10
canonicalFourPointCancellationRouteRowCountIs10 =
  refl

------------------------------------------------------------------------
-- Boundary.

data FourPointCancellationTerminalPromotionAuthority : Set where

fourPointCancellationTerminalPromotionAuthorityImpossible :
  FourPointCancellationTerminalPromotionAuthority →
  ⊥
fourPointCancellationTerminalPromotionAuthorityImpossible ()

record UnificationFourPointCancellationFromCrossTermNullityBoundary :
  Setω where
  field
    importedSupport :
      FourPointCancellationRouteImportedSupport

    routeRows :
      List FourPointCancellationRouteRow

    routeRowCount :
      Nat

    routeRowCountIs10 :
      routeRowCount ≡ 10

    routeRowCountMatchesRows :
      routeRowCount ≡ listLength routeRows

    additiveTestFunctionalRecorded :
      Bool

    additiveTestFunctionalRecordedIsTrue :
      additiveTestFunctionalRecorded ≡ true

    quotientRepresentativeInvarianceRecorded :
      Bool

    quotientRepresentativeInvarianceRecordedIsTrue :
      quotientRepresentativeInvarianceRecorded ≡ true

    polarizationFourPointResidualRecorded :
      Bool

    polarizationFourPointResidualRecordedIsTrue :
      polarizationFourPointResidualRecorded ≡ true

    moduloNullLinearityRouteRecorded :
      Bool

    moduloNullLinearityRouteRecordedIsTrue :
      moduloNullLinearityRouteRecorded ≡ true

    parallelogramConsumerRecorded :
      Bool

    parallelogramConsumerRecordedIsTrue :
      parallelogramConsumerRecorded ≡ true

    additiveTestFunctionalProved :
      Bool

    additiveTestFunctionalProvedIsFalse :
      additiveTestFunctionalProved ≡ false

    quotientRepresentativeInvarianceProved :
      Bool

    quotientRepresentativeInvarianceProvedIsFalse :
      quotientRepresentativeInvarianceProved ≡ false

    moduloNullLinearityProved :
      Bool

    moduloNullLinearityProvedIsFalse :
      moduloNullLinearityProved ≡ false

    gluingResidualForcesFourPointCancellationProved :
      Bool

    gluingResidualForcesFourPointCancellationProvedIsFalse :
      gluingResidualForcesFourPointCancellationProved ≡ false

    fourPointCancellationProved :
      Bool

    fourPointCancellationProvedIsFalse :
      fourPointCancellationProved ≡ false

    parallelogramProved :
      Bool

    parallelogramProvedIsFalse :
      parallelogramProved ≡ false

    quadraticEmergenceProved :
      Bool

    quadraticEmergenceProvedIsFalse :
      quadraticEmergenceProved ≡ false

    terminalUnificationPromotion :
      Bool

    terminalUnificationPromotionIsFalse :
      terminalUnificationPromotion ≡ false

    fourPointParallelogramQuadraticTerminalPromotionFalse :
      Bool

    fourPointParallelogramQuadraticTerminalPromotionFalseIsTrue :
      fourPointParallelogramQuadraticTerminalPromotionFalse ≡ true

    promotionAuthorityImpossible :
      FourPointCancellationTerminalPromotionAuthority →
      ⊥

    notes :
      List String

open UnificationFourPointCancellationFromCrossTermNullityBoundary public

canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary :
  UnificationFourPointCancellationFromCrossTermNullityBoundary
canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary =
  record
    { importedSupport =
        canonicalFourPointCancellationRouteImportedSupport
    ; routeRows =
        canonicalFourPointCancellationRouteRows
    ; routeRowCount =
        10
    ; routeRowCountIs10 =
        refl
    ; routeRowCountMatchesRows =
        refl
    ; additiveTestFunctionalRecorded =
        true
    ; additiveTestFunctionalRecordedIsTrue =
        refl
    ; quotientRepresentativeInvarianceRecorded =
        true
    ; quotientRepresentativeInvarianceRecordedIsTrue =
        refl
    ; polarizationFourPointResidualRecorded =
        true
    ; polarizationFourPointResidualRecordedIsTrue =
        refl
    ; moduloNullLinearityRouteRecorded =
        true
    ; moduloNullLinearityRouteRecordedIsTrue =
        ModuloNull.canonicalModuloNullFourPointRouteRecorded
    ; parallelogramConsumerRecorded =
        true
    ; parallelogramConsumerRecordedIsTrue =
        refl
    ; additiveTestFunctionalProved =
        false
    ; additiveTestFunctionalProvedIsFalse =
        refl
    ; quotientRepresentativeInvarianceProved =
        false
    ; quotientRepresentativeInvarianceProvedIsFalse =
        ModuloNull.canonicalModuloNullRepresentativeInvarianceStillOpen
    ; moduloNullLinearityProved =
        false
    ; moduloNullLinearityProvedIsFalse =
        ModuloNull.canonicalModuloNullGluingLinearityStillOpen
    ; gluingResidualForcesFourPointCancellationProved =
        false
    ; gluingResidualForcesFourPointCancellationProvedIsFalse =
        Residual.canonicalGluingResidualForcesFourPointCancellationStillOpen
    ; fourPointCancellationProved =
        false
    ; fourPointCancellationProvedIsFalse =
        Residual.canonicalFourPointDefectStillOpen
    ; parallelogramProved =
        false
    ; parallelogramProvedIsFalse =
        Residual.canonicalParallelogramLawStillOpen
    ; quadraticEmergenceProved =
        false
    ; quadraticEmergenceProvedIsFalse =
        Residual.canonicalQuadraticFormEmergenceStillBlocked
    ; terminalUnificationPromotion =
        false
    ; terminalUnificationPromotionIsFalse =
        Residual.canonicalTerminalUnificationPromotionFalse
    ; fourPointParallelogramQuadraticTerminalPromotionFalse =
        true
    ; fourPointParallelogramQuadraticTerminalPromotionFalseIsTrue =
        refl
    ; promotionAuthorityImpossible =
        fourPointCancellationTerminalPromotionAuthorityImpossible
    ; notes =
        "The route consumes U-1a cross-term nullity, modulo-null gluing linearity, and gluing residual four-point boundaries."
      ∷ "The additive test functional and quotient representative invariance sockets are recorded as prerequisites only."
      ∷ "The polarization residual socket records Q(x+y)+Q(x-y)-2Q(x)-2Q(y) as the four-point residual consumed by the route."
      ∷ "The parallelogram consumer is present but waits for actual four-point cancellation."
      ∷ "Four-point cancellation, parallelogram, quadratic emergence, and terminal promotion remain false."
      ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas for downstream consumers.

canonicalFourPointCancellationRouteRowsCountIs10 :
  routeRowCount
    canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
  ≡ 10
canonicalFourPointCancellationRouteRowsCountIs10 =
  refl

canonicalAdditiveTestFunctionalRecorded :
  additiveTestFunctionalRecorded
    canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
  ≡ true
canonicalAdditiveTestFunctionalRecorded =
  refl

canonicalQuotientRepresentativeInvarianceRecorded :
  quotientRepresentativeInvarianceRecorded
    canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
  ≡ true
canonicalQuotientRepresentativeInvarianceRecorded =
  refl

canonicalPolarizationFourPointResidualRecorded :
  polarizationFourPointResidualRecorded
    canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
  ≡ true
canonicalPolarizationFourPointResidualRecorded =
  refl

canonicalModuloNullLinearityRouteRecorded :
  moduloNullLinearityRouteRecorded
    canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
  ≡ true
canonicalModuloNullLinearityRouteRecorded =
  ModuloNull.canonicalModuloNullFourPointRouteRecorded

canonicalParallelogramConsumerRecorded :
  parallelogramConsumerRecorded
    canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
  ≡ true
canonicalParallelogramConsumerRecorded =
  refl

canonicalAdditiveTestFunctionalStillOpen :
  additiveTestFunctionalProved
    canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
  ≡ false
canonicalAdditiveTestFunctionalStillOpen =
  refl

canonicalQuotientRepresentativeInvarianceStillOpen :
  quotientRepresentativeInvarianceProved
    canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
  ≡ false
canonicalQuotientRepresentativeInvarianceStillOpen =
  ModuloNull.canonicalModuloNullRepresentativeInvarianceStillOpen

canonicalRouteModuloNullLinearityStillOpen :
  moduloNullLinearityProved
    canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
  ≡ false
canonicalRouteModuloNullLinearityStillOpen =
  ModuloNull.canonicalModuloNullGluingLinearityStillOpen

canonicalGluingResidualRouteStillOpen :
  gluingResidualForcesFourPointCancellationProved
    canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
  ≡ false
canonicalGluingResidualRouteStillOpen =
  Residual.canonicalGluingResidualForcesFourPointCancellationStillOpen

canonicalRouteFourPointCancellationStillOpen :
  fourPointCancellationProved
    canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
  ≡ false
canonicalRouteFourPointCancellationStillOpen =
  Residual.canonicalFourPointDefectStillOpen

canonicalRouteParallelogramStillOpen :
  parallelogramProved
    canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
  ≡ false
canonicalRouteParallelogramStillOpen =
  Residual.canonicalParallelogramLawStillOpen

canonicalRouteQuadraticStillBlocked :
  quadraticEmergenceProved
    canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
  ≡ false
canonicalRouteQuadraticStillBlocked =
  Residual.canonicalQuadraticFormEmergenceStillBlocked

canonicalRouteTerminalPromotionFalse :
  terminalUnificationPromotion
    canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
  ≡ false
canonicalRouteTerminalPromotionFalse =
  Residual.canonicalTerminalUnificationPromotionFalse

canonicalRouteFourPointParallelogramQuadraticTerminalPromotionFalse :
  fourPointParallelogramQuadraticTerminalPromotionFalse
    canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
  ≡ true
canonicalRouteFourPointParallelogramQuadraticTerminalPromotionFalse =
  refl

canonicalRouteTerminalPromotionImpossible :
  terminalUnificationPromotion
    canonicalUnificationFourPointCancellationFromCrossTermNullityBoundary
  ≡ true →
  ⊥
canonicalRouteTerminalPromotionImpossible ()
