module DASHI.Physics.Closure.Deg23SummaryAndFutureDirectionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Deg23RawVsCMEigenvalueReceipt as RawCM
import DASHI.Physics.Closure.Deg23FromEminus3CountAt13Receipt as Count

data Deg23RouteStatus : Set where
  naivePointCountPatternUnderived :
    Deg23RouteStatus

  hilbertVolumeRouteNegative :
    Deg23RouteStatus

  t13RawDegreeExplainsBaseFourteen :
    Deg23RouteStatus

  cmEigenvalueCorrectionZero :
    Deg23RouteStatus

  residualStillOpen :
    Deg23RouteStatus

canonicalDeg23RouteStatuses : List Deg23RouteStatus
canonicalDeg23RouteStatuses =
  naivePointCountPatternUnderived
  ∷ hilbertVolumeRouteNegative
  ∷ t13RawDegreeExplainsBaseFourteen
  ∷ cmEigenvalueCorrectionZero
  ∷ residualStillOpen
  ∷ []

futureDirectionLabel : String
futureDirectionLabel =
  "future route: full Eichler-Selberg/full trace at the CM locus; raw T13 degree explains 14 but not the residual."

record Deg23SummaryAndFutureDirectionReceipt : Setω where
  field
    rawVsCMReceipt :
      RawCM.Deg23RawVsCMEigenvalueReceipt

    residualNotFromCMEigenvalue :
      RawCM.deg23ResidualFromCMEigenvalue rawVsCMReceipt ≡ false

    countReceipt :
      Count.Deg23FromEminus3CountAt13Receipt

    countA13IsTwo :
      Count.traceA13 countReceipt ≡ 2

    deg23BaseExplained :
      Bool

    deg23BaseExplainedIsTrue :
      deg23BaseExplained ≡ true

    deg23ResidualExplained :
      Bool

    deg23ResidualExplainedIsFalse :
      deg23ResidualExplained ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    terminalPromoted :
      Bool

    terminalPromotedIsFalse :
      terminalPromoted ≡ false

    statuses :
      List Deg23RouteStatus

    statusesAreCanonical :
      statuses ≡ canonicalDeg23RouteStatuses

    futureDirection :
      String

    futureDirectionIsCanonical :
      futureDirection ≡ futureDirectionLabel

    receiptBoundary :
      List String

open Deg23SummaryAndFutureDirectionReceipt public

canonicalDeg23SummaryAndFutureDirectionReceipt :
  Deg23SummaryAndFutureDirectionReceipt
canonicalDeg23SummaryAndFutureDirectionReceipt =
  record
    { rawVsCMReceipt =
        RawCM.canonicalDeg23RawVsCMEigenvalueReceipt
    ; residualNotFromCMEigenvalue =
        refl
    ; countReceipt =
        Count.canonicalDeg23FromEminus3CountAt13Receipt
    ; countA13IsTwo =
        refl
    ; deg23BaseExplained =
        true
    ; deg23BaseExplainedIsTrue =
        refl
    ; deg23ResidualExplained =
        false
    ; deg23ResidualExplainedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; terminalPromoted =
        false
    ; terminalPromotedIsFalse =
        refl
    ; statuses =
        canonicalDeg23RouteStatuses
    ; statusesAreCanonical =
        refl
    ; futureDirection =
        futureDirectionLabel
    ; futureDirectionIsCanonical =
        refl
    ; receiptBoundary =
        "13 split in Q(sqrt(-3)) and inert in Q(sqrt(-7)) are recorded upstream."
        ∷ "E_j=0(F13) point count is 12, a13=2, and E_-7 has a13=0."
        ∷ "The local Hecke eigenvalue product is 0."
        ∷ "Raw degree 14 and CM eigenvalue measure different invariants; residual not explained."
        ∷ "Physical CKM promotion remains false."
        ∷ "Future route is full Eichler-Selberg/full trace at the CM locus."
        ∷ []
    }

deg23SummaryPhysicalCKMFalse :
  physicalCKMPromoted canonicalDeg23SummaryAndFutureDirectionReceipt ≡ false
deg23SummaryPhysicalCKMFalse =
  refl

deg23SummaryResidualUnsolved :
  deg23ResidualExplained canonicalDeg23SummaryAndFutureDirectionReceipt ≡ false
deg23SummaryResidualUnsolved =
  refl
