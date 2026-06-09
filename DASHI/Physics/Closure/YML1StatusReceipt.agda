module DASHI.Physics.Closure.YML1StatusReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayYMProofRoadmapReceipt as Roadmap
import DASHI.Physics.Closure.LatticeMassGapFromTransferMatrixReceipt as Gap

data YML1NextOpenTarget : Set where
  uniformPlaquetteCorrelatorBounds :
    YML1NextOpenTarget

  measureTightnessAsDepthGrows :
    YML1NextOpenTarget

  continuumGaugeMeasureLimit :
    YML1NextOpenTarget

canonicalYML1NextOpenTargets : List YML1NextOpenTarget
canonicalYML1NextOpenTargets =
  uniformPlaquetteCorrelatorBounds
  ∷ measureTightnessAsDepthGrows
  ∷ continuumGaugeMeasureLimit
  ∷ []

ymL1StatusStatement : String
ymL1StatusStatement =
  "YM L1 is inhabited only at finite carrier-lattice Wilson-action scope; L2 uniform bounds, tightness, continuum construction, and Clay mass gap remain open."

record YML1StatusReceipt : Setω where
  field
    roadmapReceipt :
      Roadmap.ClayYMProofRoadmapReceipt

    roadmapKeepsClayFalse :
      Roadmap.clayYangMillsPromoted roadmapReceipt ≡ false

    latticeGapReceipt :
      Gap.LatticeMassGapFromTransferMatrixReceipt

    finiteLatticeGapPositive :
      Gap.finiteLatticeGapPositive latticeGapReceipt ≡ true

    finiteLatticeYMMeasureInhabited :
      Bool

    finiteLatticeYMMeasureInhabitedIsTrue :
      finiteLatticeYMMeasureInhabited ≡ true

    ymL1CarrierLatticeInhabited :
      Bool

    ymL1CarrierLatticeInhabitedIsTrue :
      ymL1CarrierLatticeInhabited ≡ true

    ymL2UniformBoundsOpen :
      Bool

    ymL2UniformBoundsOpenIsTrue :
      ymL2UniformBoundsOpen ≡ true

    ymL3TightnessOpen :
      Bool

    ymL3TightnessOpenIsTrue :
      ymL3TightnessOpen ≡ true

    ymL4ContinuumLimitOpen :
      Bool

    ymL4ContinuumLimitOpenIsTrue :
      ymL4ContinuumLimitOpen ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    nextTargets :
      List YML1NextOpenTarget

    nextTargetsAreCanonical :
      nextTargets ≡ canonicalYML1NextOpenTargets

    statement :
      String

    statementIsCanonical :
      statement ≡ ymL1StatusStatement

open YML1StatusReceipt public

canonicalYML1StatusReceipt :
  YML1StatusReceipt
canonicalYML1StatusReceipt =
  record
    { roadmapReceipt =
        Roadmap.canonicalClayYMProofRoadmapReceipt
    ; roadmapKeepsClayFalse =
        refl
    ; latticeGapReceipt =
        Gap.canonicalLatticeMassGapFromTransferMatrixReceipt
    ; finiteLatticeGapPositive =
        refl
    ; finiteLatticeYMMeasureInhabited =
        true
    ; finiteLatticeYMMeasureInhabitedIsTrue =
        refl
    ; ymL1CarrierLatticeInhabited =
        true
    ; ymL1CarrierLatticeInhabitedIsTrue =
        refl
    ; ymL2UniformBoundsOpen =
        true
    ; ymL2UniformBoundsOpenIsTrue =
        refl
    ; ymL3TightnessOpen =
        true
    ; ymL3TightnessOpenIsTrue =
        refl
    ; ymL4ContinuumLimitOpen =
        true
    ; ymL4ContinuumLimitOpenIsTrue =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; nextTargets =
        canonicalYML1NextOpenTargets
    ; nextTargetsAreCanonical =
        refl
    ; statement =
        ymL1StatusStatement
    ; statementIsCanonical =
        refl
    }

yml1StatusKeepsClayFalse :
  clayYangMillsPromoted canonicalYML1StatusReceipt ≡ false
yml1StatusKeepsClayFalse =
  refl

yml1StatusKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYML1StatusReceipt ≡ false
yml1StatusKeepsTerminalFalse =
  refl
