module DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Canonical panel stoichiometric matrix surface.
--
-- The executable owner builds the concrete finite matrix from the acquired
-- Rhea/ChEBI panel certificate. This Agda owner records the exact contract:
-- deterministic species/reaction indices, signed coefficients, and an explicit
-- residual set for reactions whose finite formula/charge representation is not
-- paid. Missing chemistry is never represented by a fake zero column.
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

-- The QDPR slice provides the first fully paid finite column.  It contains
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

open BH4PanelMatrixBoundary public

canonicalBH4PanelMatrixBoundary : BH4PanelMatrixBoundary
canonicalBH4PanelMatrixBoundary =
  bh4-panel-matrix-boundary false refl false refl false refl false refl false refl

canonicalBH4PanelStoichiometricMatrixReceipt : Receipt.GenericReceipt
canonicalBH4PanelStoichiometricMatrixReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 panel stoichiometric matrix"
    "DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact"
    "Rhea/ChEBI finite reaction rows -> deterministic species index x reaction index -> signed coefficient entries"
    "the executable builder constructs S only for formula/charge-ready internal reactions and retains incomplete/polymeric/R-group chemistry as residuals"
    "missing chemistry is not a zero column; S does not create kinetics, compartment measurements, external exchange, allocator causality or disease mechanism"
    "python3 scripts/build_bh4_stoichiometric_matrix.py artifacts/biology/rhea-chebi-kitzerow-bh4-panel.json"
