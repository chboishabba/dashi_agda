module DASHI.Biology.Molecular.BH4ExecutedPanelReactionReceiptExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- EXECUTED 16-PROTEIN RHEA / ChEBI PANEL RECEIPT
--
-- Local live acquisition 2026-10-17 consumed the byte-pinned 16-member
-- UniProt panel, extracted catalytic-activity Rhea links, resolved generic
-- Rhea IDs to directional reactions for RDF participant inspection, and then
-- built the finite stoichiometric workload.
--
-- Result:
--   24 protein->Rhea links
--   12 finite formula/charge reaction columns
--   3 acquired but non-finite protein/R-group reaction residuals
--   29 finite species in the resulting matrix
--
-- Acquisition success is kept separate from finite-molecular representability:
-- the MTOR protein-kinase reactions are acquired reactions but are deliberately
-- not represented by fake zero columns.
------------------------------------------------------------------------

record ExecutedPanelReactionReceipt : Set where
  constructor executed-panel-reaction-receipt
  field
    sourcePanelReference : String
    proteinCount : Nat
    proteinReactionLinkCount : Nat
    finiteReactionCount : Nat
    residualReactionCount : Nat
    finiteSpeciesCount : Nat
    finiteReactionIds : List String
    residualReactionIds : List String
    acquisitionExecuted : Bool
    matrixBuilt : Bool
    parameterTemplateBuilt : Bool
    jointFeasibilityExecuted : Bool

open ExecutedPanelReactionReceipt public

finitePanelReactionIds : List String
finitePanelReactionIds =
  "RHEA:17473"  -- GCH1
  ∷ "RHEA:22048"  -- PTS
  ∷ "RHEA:32627"  -- SPR
  ∷ "RHEA:18953"  -- SPR
  ∷ "RHEA:11920"  -- PCBD1
  ∷ "RHEA:17869"  -- QDPR / NAD+
  ∷ "RHEA:17865"  -- QDPR / NADP+
  ∷ "RHEA:20273"  -- PAH
  ∷ "RHEA:18201"  -- TH
  ∷ "RHEA:16709"  -- TPH1 / TPH2
  ∷ "RHEA:19897"  -- NOS1 / NOS2 / NOS3
  ∷ "RHEA:36255"  -- AGMO
  ∷ []

residualPanelReactionIds : List String
residualPanelReactionIds =
  "RHEA:10596"  -- MTOR tyrosyl-[protein] kinase reaction
  ∷ "RHEA:17989"  -- MTOR seryl-[protein] kinase reaction
  ∷ "RHEA:46608"  -- MTOR threonyl-[protein] kinase reaction
  ∷ []

canonicalExecutedPanelReactionReceipt : ExecutedPanelReactionReceipt
canonicalExecutedPanelReactionReceipt =
  executed-panel-reaction-receipt
    "artifacts/biology/uniprot-kitzerow-bh4-panel-certificate.json -> artifacts/biology/rhea-kitzerow-bh4-reactions.json"
    16 24 12 3 29
    finitePanelReactionIds
    residualPanelReactionIds
    true true true true

record ExecutedPanelReactionBoundary : Set where
  constructor executed-panel-reaction-boundary
  field
    acquiredReactionImpliesFiniteFormulaRepresentation : Bool
    acquiredReactionImpliesFiniteFormulaRepresentationIsFalse :
      acquiredReactionImpliesFiniteFormulaRepresentation ≡ false
    residualReactionMayBeInsertedAsZeroColumn : Bool
    residualReactionMayBeInsertedAsZeroColumnIsFalse :
      residualReactionMayBeInsertedAsZeroColumn ≡ false
    completeReactionIdentityCreatesKinetics : Bool
    completeReactionIdentityCreatesKineticsIsFalse :
      completeReactionIdentityCreatesKinetics ≡ false
    finiteStoichiometricMatrixCreatesMeasuredFlux : Bool
    finiteStoichiometricMatrixCreatesMeasuredFluxIsFalse :
      finiteStoichiometricMatrixCreatesMeasuredFlux ≡ false
    underdeterminedFluxReceiptCreatesMechanismTruth : Bool
    underdeterminedFluxReceiptCreatesMechanismTruthIsFalse :
      underdeterminedFluxReceiptCreatesMechanismTruth ≡ false

open ExecutedPanelReactionBoundary public

canonicalExecutedPanelReactionBoundary : ExecutedPanelReactionBoundary
canonicalExecutedPanelReactionBoundary =
  executed-panel-reaction-boundary
    false refl false refl false refl false refl false refl

canonicalExecutedPanelReactionGenericReceipt : Receipt.GenericReceipt
canonicalExecutedPanelReactionGenericReceipt =
  Receipt.mkNonPromotingReceipt
    "executed BH4 panel Rhea/ChEBI reaction receipt"
    "DASHI.Biology.Molecular.BH4ExecutedPanelReactionReceiptExact"
    "16 exact UniProt proteins -> 24 catalytic Rhea links -> 12 finite reactions + 3 explicit MTOR protein/R-group residuals -> 29-species finite matrix"
    "promotes the actual live panel execution counts and reaction IDs into the proof graph and closes the generic execute/acquire-panel residual"
    "acquired reaction identity is not finite formula representation; residual reactions are not zero columns; finite stoichiometry does not create kinetics, measured flux or mechanism truth"
    "python3 scripts/check_kitzerow_bh4_priority_all.py"
