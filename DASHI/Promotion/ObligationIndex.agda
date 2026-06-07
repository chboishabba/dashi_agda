module DASHI.Promotion.ObligationIndex where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Interop.CategoricalInterlinkLayer as Interlink
import DASHI.Promotion.NumericAndAuthorityObligations as Numeric
import DASHI.Promotion.ClassicalFieldObligations as Classical
import DASHI.Promotion.QuantumQFTObligations as Quantum
import DASHI.Promotion.ChemistryBiologyObligations as ChemBio
import DASHI.Promotion.Gate3ClayObligations as GateClay
import DASHI.Promotion.StandardModelTerminalObligations as SMT

------------------------------------------------------------------------
-- Unified promotion obligation index.
--
-- This is the sprint-facing queue for promotion work.  It joins the six
-- disjoint implementation lanes into one receipt surface and deliberately
-- keeps the promoted-claim bit false.  Rows here are obligations to satisfy,
-- not theorem claims.

data PromotionImplementationLane : Set where
  numericAndAuthorityLane : PromotionImplementationLane
  classicalFieldLane : PromotionImplementationLane
  quantumQFTLane : PromotionImplementationLane
  chemistryBiologyLane : PromotionImplementationLane
  gate3ClayLane : PromotionImplementationLane
  standardModelTerminalLane : PromotionImplementationLane

record PromotionLaneSummary : Set where
  field
    lane :
      PromotionImplementationLane

    ownerModule :
      String

    canonicalReceipt :
      String

    scope :
      String

    openObligationCount :
      Nat

    positiveBoundary :
      String

    falsePromotionGuards :
      String

    validationCommand :
      String

    promotesClaim :
      Bool

    promotesClaimIsFalse :
      promotesClaim ≡ false

open PromotionLaneSummary public

mkLaneSummary :
  PromotionImplementationLane →
  String →
  String →
  String →
  Nat →
  String →
  String →
  String →
  PromotionLaneSummary
mkLaneSummary lane owner receipt scope count positive falseGuards command =
  record
    { lane = lane
    ; ownerModule = owner
    ; canonicalReceipt = receipt
    ; scope = scope
    ; openObligationCount = count
    ; positiveBoundary = positive
    ; falsePromotionGuards = falseGuards
    ; validationCommand = command
    ; promotesClaim = false
    ; promotesClaimIsFalse = refl
    }

canonicalPromotionLaneSummaries : List PromotionLaneSummary
canonicalPromotionLaneSummaries =
  mkLaneSummary
    numericAndAuthorityLane
    "DASHI.Promotion.NumericAndAuthorityObligations"
    "canonicalNumericAndAuthorityObligationIndex"
    "numeric measured values; provider authority; comparison law; covariance; holdout; runtime replay; semantic adequacy"
    9
    "authority and runtime metadata obligations are indexed"
    "numericValuePromoted/providerAuthority/comparison/covariance/holdout/replay/semantic adequacy remain false"
    "agda -i . DASHI/Promotion/NumericAndAuthorityObligations.agda"
  ∷ mkLaneSummary
    classicalFieldLane
    "DASHI.Promotion.ClassicalFieldObligations"
    "canonicalClassicalFieldPromotionObligationIndex"
    "physical laws; Maxwell field equations; GR field equations"
    3
    "classical field promotion stages are indexed"
    "physical laws, Maxwell, and GR promotion remain false"
    "agda -i . DASHI/Promotion/ClassicalFieldObligations.agda"
  ∷ mkLaneSummary
    quantumQFTLane
    "DASHI.Promotion.QuantumQFTObligations"
    "canonicalQuantumQFTPromotionObligationReceipt"
    "Schrodinger dynamics; Born semantics; QFT"
    14
    "quantum/QFT receipt targets are indexed against registry inputs"
    "Schrodinger dynamics, Born semantics, QFT, and quantum empirical adequacy remain false"
    "agda -i . DASHI/Promotion/QuantumQFTObligations.agda"
  ∷ mkLaneSummary
    chemistryBiologyLane
    "DASHI.Promotion.ChemistryBiologyObligations"
    "canonicalChemistryBiologyPromotionObligationIndex"
    "physical chemistry; spectroscopy; bonding; wet-lab chemistry; biology causation/intervention/clinical/brain-state recovery"
    11
    "chemistry and biology promotion obligations are indexed beyond local population receipts"
    "physical chemistry, spectroscopy, bonding, wet-lab, causation, intervention, clinical validity, and brain-state recovery remain false"
    "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
  ∷ mkLaneSummary
    gate3ClayLane
    "DASHI.Promotion.Gate3ClayObligations"
    "canonicalGate3ClayPromotionObligationReceipt"
    "Gate 3 closure; Mosco; no spectral pollution; mass shell; NS Clay; YM Clay"
    22
    "Gate 3 density evidence is recorded as non-promoting input"
    "Gate 3 closure, Mosco, no-pollution, transfer, mass-shell, NS Clay, YM Clay, and terminal Clay promotion remain false"
    "agda -i . DASHI/Promotion/Gate3ClayObligations.agda"
  ∷ mkLaneSummary
    standardModelTerminalLane
    "DASHI.Promotion.StandardModelTerminalObligations"
    "canonicalStandardModelTerminalPromotionObligationReceipt"
    "Standard Model; terminal/full unification"
    14
    "Standard Model and terminal claim-audit obligations are indexed"
    "Standard Model and terminal/full unification promotion remain false"
    "agda -i . DASHI/Promotion/StandardModelTerminalObligations.agda"
  ∷ []

record UnifiedPromotionObligationIndex : Setω where
  field
    sourceKnownInputsPopulation :
      Registry.KnownInputsPopulationReceipt

    sourceCategoricalInterlink :
      Interlink.CategoricalInterlinkReceipt

    numericAndAuthority :
      Numeric.NumericAndAuthorityObligationIndex

    classicalField :
      Classical.ClassicalFieldPromotionObligationIndex

    quantumQFT :
      Quantum.QuantumQFTPromotionObligationReceipt

    chemistryBiology :
      ChemBio.ChemistryBiologyPromotionObligationIndex

    gate3Clay :
      GateClay.Gate3ClayPromotionObligationReceipt

    standardModelTerminal :
      SMT.StandardModelTerminalPromotionObligationReceipt

    laneSummaries :
      List PromotionLaneSummary

    laneSummaryCount :
      Nat

    laneSummaryCountIs6 :
      laneSummaryCount ≡ 6

    aggregateOpenObligationCount :
      Nat

    aggregateOpenObligationCountIs73 :
      aggregateOpenObligationCount ≡ 73

    validationTarget :
      String

    validationCommand :
      String

    allPromotionGuardsStillFalse :
      Bool

    allPromotionGuardsStillFalseIsTrue :
      allPromotionGuardsStillFalse ≡ true

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

open UnifiedPromotionObligationIndex public

canonicalUnifiedPromotionObligationIndex :
  UnifiedPromotionObligationIndex
canonicalUnifiedPromotionObligationIndex =
  record
    { sourceKnownInputsPopulation =
        Registry.canonicalKnownInputsPopulationReceipt
    ; sourceCategoricalInterlink =
        Interlink.canonicalCategoricalInterlinkReceipt
    ; numericAndAuthority =
        Numeric.canonicalNumericAndAuthorityObligationIndex
    ; classicalField =
        Classical.canonicalClassicalFieldPromotionObligationIndex
    ; quantumQFT =
        Quantum.canonicalQuantumQFTPromotionObligationReceipt
    ; chemistryBiology =
        ChemBio.canonicalChemistryBiologyPromotionObligationIndex
    ; gate3Clay =
        GateClay.canonicalGate3ClayPromotionObligationReceipt
    ; standardModelTerminal =
        SMT.canonicalStandardModelTerminalPromotionObligationReceipt
    ; laneSummaries =
        canonicalPromotionLaneSummaries
    ; laneSummaryCount =
        6
    ; laneSummaryCountIs6 =
        refl
    ; aggregateOpenObligationCount =
        73
    ; aggregateOpenObligationCountIs73 =
        refl
    ; validationTarget =
        "DASHI/Promotion/ObligationIndex.agda"
    ; validationCommand =
        "agda -i . DASHI/Promotion/ObligationIndex.agda"
    ; allPromotionGuardsStillFalse =
        true
    ; allPromotionGuardsStillFalseIsTrue =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    }

canonicalUnifiedPromotionLaneCountIs6 :
  UnifiedPromotionObligationIndex.laneSummaryCount
    canonicalUnifiedPromotionObligationIndex
  ≡ 6
canonicalUnifiedPromotionLaneCountIs6 = refl

canonicalUnifiedPromotionOpenObligationCountIs73 :
  UnifiedPromotionObligationIndex.aggregateOpenObligationCount
    canonicalUnifiedPromotionObligationIndex
  ≡ 73
canonicalUnifiedPromotionOpenObligationCountIs73 = refl

canonicalUnifiedPromotionTerminalPromotionIsFalse :
  UnifiedPromotionObligationIndex.terminalPromotion
    canonicalUnifiedPromotionObligationIndex
  ≡ false
canonicalUnifiedPromotionTerminalPromotionIsFalse = refl

