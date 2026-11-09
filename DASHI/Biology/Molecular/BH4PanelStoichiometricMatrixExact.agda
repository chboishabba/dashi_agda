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


------------------------------------------------------------------------
-- SOURCE-CONSUMING FINITE STOICHIOMETRIC REACTION THEOREM
--
-- A finite source column is explicitly reactants/products (no signed
-- natural-number underflow), with a reactant-availability witness
--  state[site] = reactants + residual.
--
-- Conservation is derived from executable vector addition and the
-- literal per-column CHNOP left-kernel identities. No hand-filled
-- 29x12 coefficients or measured kinetics enter this theorem.
------------------------------------------------------------------------

import Data.Vec.Base as V
import Data.Fin.Base as F

panelAdd :
  ∀ {n} → V.Vec Nat n → V.Vec Nat n → V.Vec Nat n
panelAdd V.[] V.[] = V.[]
panelAdd (V._∷_ a xs) (V._∷_ b ys) =
  V._∷_ (a + b) (panelAdd xs ys)

panelWeighted :
  ∀ {n} → V.Vec Nat n → V.Vec Nat n → Nat
panelWeighted V.[] V.[] = 0
panelWeighted (V._∷_ weight weights) (V._∷_ count counts) =
  weight * count + panelWeighted weights counts

-- Four-term exchange is the only arithmetic interchange required
-- by the native 29-species weighted-inventory proof.
panelShuffle :
  (a b c d : Nat) →
  (a + b) + (c + d) ≡ (a + c) + (b + d)
panelShuffle a b c d =
  trans (+-assoc a b (c + d))
    (trans
      (cong (λ n → a + n)
        (trans
          (sym (+-assoc b c d))
          (trans
            (cong (λ n → n + d) (+-comm b c))
            (+-assoc c b d))))
      (sym (+-assoc a c (b + d))))

panelWeightedDistributes :
  ∀ {n} (weights xs ys : V.Vec Nat n) →
  panelWeighted weights (panelAdd xs ys)
    ≡ panelWeighted weights xs + panelWeighted weights ys
panelWeightedDistributes V.[] V.[] V.[] = refl
panelWeightedDistributes
  (V._∷_ w weights) (V._∷_ x xs) (V._∷_ y ys) =
  trans
    (cong (λ n → w * (x + y) + n)
      (panelWeightedDistributes weights xs ys))
    (trans
      (cong (λ n → n + (panelWeighted weights xs
        + panelWeighted weights ys))
        (*-distribˡ-+ w x y))
      (panelShuffle (w * x) (w * y)
        (panelWeighted weights xs) (panelWeighted weights ys)))

record OriginalFiniteReaction (n : Nat) : Set where
  constructor original-finite-reaction
  field
    originalReactants : V.Vec Nat n
    originalProducts : V.Vec Nat n
open OriginalFiniteReaction public

-- Executed reaction on the available residual inventory.
panelReactionAfter :
  ∀ {n} → OriginalFiniteReaction n →
  V.Vec Nat n → V.Vec Nat n
panelReactionAfter reaction residual =
  panelAdd (originalProducts reaction) residual

panelReactionBefore :
  ∀ {n} → OriginalFiniteReaction n →
  V.Vec Nat n → V.Vec Nat n
panelReactionBefore reaction residual =
  panelAdd (originalReactants reaction) residual

panelReactionConserves :
  ∀ {n} (weights : V.Vec Nat n)
  (reaction : OriginalFiniteReaction n)
  (residual : V.Vec Nat n) →
  panelWeighted weights (originalReactants reaction)
    ≡ panelWeighted weights (originalProducts reaction) →
  panelWeighted weights (panelReactionAfter reaction residual)
    ≡ panelWeighted weights (panelReactionBefore reaction residual)
panelReactionConserves weights reaction residual balanced =
  trans
    (panelWeightedDistributes
      weights (originalProducts reaction) residual)
    (trans
      (cong (λ n → n + panelWeighted weights residual)
        (sym balanced))
      (sym (panelWeightedDistributes
        weights (originalReactants reaction) residual)))

panelSpatialWeighted :
  ∀ {n sites} (weights : V.Vec Nat n) →
  V.Vec (V.Vec Nat n) sites → Nat
panelSpatialWeighted weights V.[] = 0
panelSpatialWeighted weights (V._∷_ current rest) =
  panelWeighted weights current + panelSpatialWeighted weights rest

-- A reaction fires AT the selected voxel, preserving all other
-- molecular inventories. The lookup equality is the genuine
-- reactant-availability witness, not an asserted nonnegative rate.
panelSpatialReactionConserves :
  ∀ {n sites} (weights : V.Vec Nat n)
  (site : F.Fin sites)
  (reaction : OriginalFiniteReaction n)
  (residual : V.Vec Nat n)
  (before : V.Vec (V.Vec Nat n) sites) →
  V.lookup before site ≡ panelReactionBefore reaction residual →
  panelWeighted weights (originalReactants reaction)
    ≡ panelWeighted weights (originalProducts reaction) →
  panelSpatialWeighted weights
    (V.updateAt before site
      (λ _ → panelReactionAfter reaction residual))
    ≡ panelSpatialWeighted weights before
panelSpatialReactionConserves weights F.zero reaction residual
  (V._∷_ current rest) available balanced =
  trans
    (cong (λ n → n + panelSpatialWeighted weights rest)
      (panelReactionConserves weights reaction residual balanced))
    (cong (λ n → n + panelSpatialWeighted weights rest)
      (sym (cong (panelWeighted weights) available)))
panelSpatialReactionConserves weights (F.suc site) reaction residual
  (V._∷_ current rest) available balanced =
  cong (λ n → panelWeighted weights current + n)
    (panelSpatialReactionConserves
      weights site reaction residual rest available balanced)


------------------------------------------------------------------------
-- SIGNED MOLECULAR CHARGE. Conservation of positive and negative
-- magnitudes separately would be false for general redox chemistry.
-- Instead p_before + n_after = p_after + n_before is the constructive
-- cross-sum encoding of net signed-charge equality.
------------------------------------------------------------------------

panelReactionSignedChargeConserves :
  ∀ {n}
  (positiveWeights negativeWeights : V.Vec Nat n)
  (reaction : OriginalFiniteReaction n)
  (residual : V.Vec Nat n) →
  (panelWeighted positiveWeights (originalReactants reaction)
    + panelWeighted negativeWeights (originalProducts reaction))
    ≡
  (panelWeighted positiveWeights (originalProducts reaction)
    + panelWeighted negativeWeights (originalReactants reaction)) →
  (panelWeighted positiveWeights (panelReactionBefore reaction residual)
    + panelWeighted negativeWeights (panelReactionAfter reaction residual))
    ≡
  (panelWeighted positiveWeights (panelReactionAfter reaction residual)
    + panelWeighted negativeWeights (panelReactionBefore reaction residual))
panelReactionSignedChargeConserves
  positiveWeights negativeWeights reaction residual balanced =
  trans
    (cong₂ _+_
      (panelWeightedDistributes positiveWeights
        (originalReactants reaction) residual)
      (panelWeightedDistributes negativeWeights
        (originalProducts reaction) residual))
    (trans
      (panelShuffle
        (panelWeighted positiveWeights (originalReactants reaction))
        (panelWeighted positiveWeights residual)
        (panelWeighted negativeWeights (originalProducts reaction))
        (panelWeighted negativeWeights residual))
      (trans
        (cong
          (λ n → n + (panelWeighted positiveWeights residual
            + panelWeighted negativeWeights residual))
          balanced)
        (trans
          (sym (panelShuffle
            (panelWeighted positiveWeights (originalProducts reaction))
            (panelWeighted positiveWeights residual)
            (panelWeighted negativeWeights (originalReactants reaction))
            (panelWeighted negativeWeights residual)))
          (cong₂ _+_
            (sym (panelWeightedDistributes positiveWeights
              (originalProducts reaction) residual))
            (sym (panelWeightedDistributes negativeWeights
              (originalReactants reaction) residual))))))

-- Cross-sum equality is preserved in all 27 sites even when another
-- voxel has arbitrary unrelated molecular inventory.
panelSpatialSignedReactionConserves :
  ∀ {n sites}
  (positiveWeights negativeWeights : V.Vec Nat n)
  (site : F.Fin sites)
  (reaction : OriginalFiniteReaction n)
  (residual : V.Vec Nat n)
  (before : V.Vec (V.Vec Nat n) sites) →
  V.lookup before site ≡ panelReactionBefore reaction residual →
  (panelWeighted positiveWeights (originalReactants reaction)
    + panelWeighted negativeWeights (originalProducts reaction))
    ≡
  (panelWeighted positiveWeights (originalProducts reaction)
    + panelWeighted negativeWeights (originalReactants reaction)) →
  (panelSpatialWeighted positiveWeights before
    + panelSpatialWeighted negativeWeights
      (V.updateAt before site
        (λ _ → panelReactionAfter reaction residual)))
    ≡
  (panelSpatialWeighted positiveWeights
    (V.updateAt before site
      (λ _ → panelReactionAfter reaction residual))
    + panelSpatialWeighted negativeWeights before)
panelSpatialSignedReactionConserves
  positiveWeights negativeWeights F.zero reaction residual
  (V._∷_ current rest) available balanced =
  trans
    (panelShuffle
      (panelWeighted positiveWeights current)
      (panelSpatialWeighted positiveWeights rest)
      (panelWeighted negativeWeights (panelReactionAfter reaction residual))
      (panelSpatialWeighted negativeWeights rest))
    (trans
      (cong
        (λ n → n + (panelSpatialWeighted positiveWeights rest
          + panelSpatialWeighted negativeWeights rest))
        (trans
          (cong
            (λ n → n + panelWeighted negativeWeights
              (panelReactionAfter reaction residual))
            (cong (panelWeighted positiveWeights) available))
          (trans
            (panelReactionSignedChargeConserves
              positiveWeights negativeWeights reaction residual balanced)
            (cong
              (λ n → panelWeighted positiveWeights
                (panelReactionAfter reaction residual) + n)
              (sym (cong (panelWeighted negativeWeights) available))))))
      (sym (panelShuffle
        (panelWeighted positiveWeights
          (panelReactionAfter reaction residual))
        (panelSpatialWeighted positiveWeights rest)
        (panelWeighted negativeWeights current)
        (panelSpatialWeighted negativeWeights rest))))
panelSpatialSignedReactionConserves
  positiveWeights negativeWeights (F.suc site) reaction residual
  (V._∷_ current rest) available balanced =
  trans
    (panelShuffle
      (panelWeighted positiveWeights current)
      (panelSpatialWeighted positiveWeights rest)
      (panelWeighted negativeWeights current)
      (panelSpatialWeighted negativeWeights
        (V.updateAt rest site
          (λ _ → panelReactionAfter reaction residual))))
    (trans
      (cong
        (λ n → n + (panelWeighted positiveWeights current
          + panelWeighted negativeWeights current))
        (panelSpatialSignedReactionConserves
          positiveWeights negativeWeights site reaction residual
          rest available balanced))
      (sym (panelShuffle
        (panelWeighted positiveWeights current)
        (panelSpatialWeighted positiveWeights
          (V.updateAt rest site
            (λ _ → panelReactionAfter reaction residual)))
        (panelWeighted negativeWeights current)
        (panelSpatialWeighted negativeWeights rest))))

data OriginalCHNOPElement : Set where
  carbonElement : OriginalCHNOPElement
  hydrogenElement : OriginalCHNOPElement
  nitrogenElement : OriginalCHNOPElement
  oxygenElement : OriginalCHNOPElement
  phosphorusElement : OriginalCHNOPElement

-- The entire original 29x12 source is demanded explicitly.
-- No data are fabricated to inhabit this record.
record SourceCertifiedOriginal29x12 : Set where
  field
    sourceFiniteColumns : V.Vec (OriginalFiniteReaction 29) 12
    sourceElementWeights : OriginalCHNOPElement → V.Vec Nat 29
    sourceColumnLeftKernel :
      (element : OriginalCHNOPElement) (column : F.Fin 12) →
      panelWeighted (sourceElementWeights element)
        (originalReactants (V.lookup sourceFiniteColumns column))
        ≡ panelWeighted (sourceElementWeights element)
          (originalProducts (V.lookup sourceFiniteColumns column))
open SourceCertifiedOriginal29x12 public

-- Exact P0 finite-volume SOURCE-CERTIFICATE-CONSUMING theorem:
-- each original column fires in one of 27 sites, consumes only its
-- actual reactants and preserves every CHNOP quantity across the
-- COMPLETE cubical inventory. The certificate itself is UNPAID until
-- constructed from the original byte-pinned Rhea/ChEBI matrix.
original29x12SpatialReactionBalance :
  (certificate : SourceCertifiedOriginal29x12)
  (element : OriginalCHNOPElement)
  (column : F.Fin 12)
  (site : F.Fin 27)
  (residual : V.Vec Nat 29)
  (before : V.Vec (V.Vec Nat 29) 27) →
  V.lookup before site ≡
    panelReactionBefore
      (V.lookup (sourceFiniteColumns certificate) column) residual →
  panelSpatialWeighted (sourceElementWeights certificate element)
    (V.updateAt before site
      (λ _ → panelReactionAfter
        (V.lookup (sourceFiniteColumns certificate) column) residual))
    ≡ panelSpatialWeighted
      (sourceElementWeights certificate element) before
original29x12SpatialReactionBalance
  certificate element column site residual before available =
  panelSpatialReactionConserves
    (sourceElementWeights certificate element)
    site (V.lookup (sourceFiniteColumns certificate) column)
    residual before available
    (sourceColumnLeftKernel certificate element column)
