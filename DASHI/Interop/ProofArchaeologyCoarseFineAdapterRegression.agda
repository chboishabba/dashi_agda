module DASHI.Interop.ProofArchaeologyCoarseFineAdapterRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Interop.CrossLaneProofArchaeologyLedgerExact as Ledger
import DASHI.Interop.ProofArchaeologyCoarseFineAdapterExact as Adapter

------------------------------------------------------------------------
-- RED/GREEN contract: a proof-archeology anchor must decompose into a compact
-- current proof surface plus retained chronology/provenance residual and reopen
-- definitionally through the existing coarse/fine kernel.
------------------------------------------------------------------------

proofAnchorReopeningSurface :
  Fibre.CoarseFineReopening Ledger.DatedAnchor
proofAnchorReopeningSurface = Adapter.proofAnchorReopening

proofAnchorObserverSeparatingSurface =
  Adapter.proofAnchorObserverSeparating

currentSurfaceIsWholeProofHistory : Bool
currentSurfaceIsWholeProofHistory =
  Adapter.ProofArchaeologyCoarseFineBoundary.currentSurfaceIsWholeProofHistory
    Adapter.canonicalProofArchaeologyCoarseFineBoundary

currentSurfaceIsWholeProofHistoryIsFalse :
  currentSurfaceIsWholeProofHistory ≡ false
currentSurfaceIsWholeProofHistoryIsFalse = refl

chronologyResidualCanBeDroppedWithoutInformationLoss : Bool
chronologyResidualCanBeDroppedWithoutInformationLoss =
  Adapter.ProofArchaeologyCoarseFineBoundary.chronologyResidualCanBeDroppedWithoutInformationLoss
    Adapter.canonicalProofArchaeologyCoarseFineBoundary

chronologyResidualCanBeDroppedWithoutInformationLossIsFalse :
  chronologyResidualCanBeDroppedWithoutInformationLoss ≡ false
chronologyResidualCanBeDroppedWithoutInformationLossIsFalse = refl
