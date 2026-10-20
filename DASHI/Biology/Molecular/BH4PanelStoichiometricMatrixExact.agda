module DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt
import DASHI.Biology.Molecular.BH4ExecutedPanelReactionReceiptExact as Executed

------------------------------------------------------------------------
-- Canonical panel stoichiometric matrix surface.
--
-- The executable owner builds the concrete finite matrix from the acquired
-- Rhea/ChEBI panel certificate. This Agda owner records the exact contract:
-- deterministic species/reaction indices, signed coefficients, and an explicit
-- residual set for reactions whose finite formula/charge representation is not
-- paid. Missing chemistry is never represented by a fake zero column.
--
-- The live panel was executed on 2026-10-17.  Its finite matrix has 29 species
-- and 12 reactions; three acquired MTOR protein/R-group reactions remain
-- explicit residuals.
------------------------------------------------------------------------

data CoefficientSign : Set where
  consumed : CoefficientSign
  produced : CoefficientSign

record StoichiometricMatrixEntry : Set where
  constructor stoichiometric-matrix-entry
  field
    speciesIndex : Nat
    reactionIndex : Nat
    signedCoefficientSign : CoefficientSign
    signedCoefficientMagnitude : Nat

open StoichiometricMatrixEntry public

data MatrixResidual : Set where
  formulaIncomplete : String → MatrixResidual
  polymerOrRGroup : String → MatrixResidual
  coefficientUnresolved : String → MatrixResidual
  speciesIdentityUnresolved : String → MatrixResidual

record BH4PanelStoichiometricMatrix : Set where
  constructor bh4-panel-stoichiometric-matrix
  field
    sourceCertificateReference : String
    speciesCount : Nat
    reactionCount : Nat
    entries : List StoichiometricMatrixEntry
    residuals : List MatrixResidual
    deterministicSpeciesIndex : Bool
    deterministicReactionIndex : Bool
    internalReactionsOnly : Bool

open BH4PanelStoichiometricMatrix public

-- The QDPR slice provides the first fully paid finite column. It contains
-- three consumed and two produced molecular species; the exact atom/charge
-- conservation proof remains owned by BH4MolecularStoichiometryExact.
qdprFiniteColumn : BH4PanelStoichiometricMatrix
qdprFiniteColumn =
  bh4-panel-stoichiometric-matrix
    "RHEA:32253 / dashi.rhea-chebi-bh4-panel.v2"
    5
    1
    ( stoichiometric-matrix-entry 0 0 consumed 1
    ∷ stoichiometric-matrix-entry 1 0 consumed 1
    ∷ stoichiometric-matrix-entry 2 0 consumed 1
    ∷ stoichiometric-matrix-entry 3 0 produced 1
    ∷ stoichiometric-matrix-entry 4 0 produced 1
    ∷ [] )
    []
    true true true

-- Executed-panel dimensions and identities.  The full sparse entry list remains
-- an executable JSON/CSV receipt because the user-run artifact is intentionally
-- not retyped by hand here.  The formal owner pins the exact dimensions,
-- reaction index and non-finite residual IDs that were actually produced.
executedPanelSpeciesCount : Nat
executedPanelSpeciesCount = 29

executedPanelReactionCount : Nat
executedPanelReactionCount = 12

executedPanelFiniteReactionIds : List String
executedPanelFiniteReactionIds = Executed.finitePanelReactionIds

executedPanelResidualReactionIds : List String
executedPanelResidualReactionIds = Executed.residualPanelReactionIds

executedPanelMatrixReference : String
executedPanelMatrixReference =
  "artifacts/biology/bh4-stoichiometric-matrix.json; executed 2026-10-17 from dashi.rhea-chebi-bh4-panel.v2"

executedPanelHasTwentyNineSpecies : executedPanelSpeciesCount ≡ 29
executedPanelHasTwentyNineSpecies = refl

executedPanelHasTwelveFiniteReactions : executedPanelReactionCount ≡ 12
executedPanelHasTwelveFiniteReactions = refl

record BH4PanelMatrixBoundary : Set where
  constructor bh4-panel-matrix-boundary
  field
    formulaIncompleteReactionBecomesZeroColumn : Bool
    formulaIncompleteReactionBecomesZeroColumnIsFalse :
      formulaIncompleteReactionBecomesZeroColumn ≡ false
    matrixCreatesKineticLaw : Bool
    matrixCreatesKineticLawIsFalse : matrixCreatesKineticLaw ≡ false
    matrixIncludesExternalExchangeAsInternalReaction : Bool
    matrixIncludesExternalExchangeAsInternalReactionIsFalse :
      matrixIncludesExternalExchangeAsInternalReaction ≡ false
    matrixCreatesMeasuredCompartmentState : Bool
    matrixCreatesMeasuredCompartmentStateIsFalse :
      matrixCreatesMeasuredCompartmentState ≡ false
    matrixCreatesDiseaseMechanism : Bool
    matrixCreatesDiseaseMechanismIsFalse : matrixCreatesDiseaseMechanism ≡ false
    executedDimensionsImplyAllChemistryFinite : Bool
    executedDimensionsImplyAllChemistryFiniteIsFalse :
      executedDimensionsImplyAllChemistryFinite ≡ false

open BH4PanelMatrixBoundary public

canonicalBH4PanelMatrixBoundary : BH4PanelMatrixBoundary
canonicalBH4PanelMatrixBoundary =
  bh4-panel-matrix-boundary
    false refl false refl false refl false refl false refl false refl

canonicalBH4PanelStoichiometricMatrixReceipt : Receipt.GenericReceipt
canonicalBH4PanelStoichiometricMatrixReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 panel stoichiometric matrix"
    "DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact"
    "executed 29-species x 12-finite-reaction matrix from 24 panel Rhea links; three MTOR protein/R-group reactions retained as explicit residuals"
    "pins the executed species/reaction dimensions, exact finite reaction index, residual reaction IDs and deterministic/internal-only matrix contract while leaving the sparse executable entries in the generated JSON/CSV receipt"
    "missing chemistry is not a zero column; S does not create kinetics, compartment measurements, external exchange, allocator causality or disease mechanism"
    "python3 scripts/build_bh4_stoichiometric_matrix.py artifacts/biology/rhea-kitzerow-bh4-reactions.json --output-prefix artifacts/biology/bh4-stoichiometric-matrix"
