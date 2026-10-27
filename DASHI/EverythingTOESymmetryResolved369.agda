module DASHI.EverythingTOESymmetryResolved369 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (false)

------------------------------------------------------------------------
-- Focused TOE aggregate: generic symmetry-resolved fibre calculus plus the
-- existing SSP/369 representation-reduction and physics instances.
------------------------------------------------------------------------

import DASHI.Core.SymmetryResolvedFibreExact
import DASHI.EverythingSSPRepresentationReductionRound9
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact

-- Reuse the existing exact finite GR/quantum proof-term regression.
-- It contains a terminal physical non-promotion theorem.
-- Do not replace this import with DASHI.Unifier placeholder axioms.
import DASHI.Unified.GRQuantumProofTermRegression

-- Reuse the strict Balaban RG normalization and its fail-closed continuum boundary.
import DASHI.Unified.BalabanRGTOERegression as BalabanRGTOE

toeBalabanRGBlockSpinTransferStillOpen :
  BalabanRGTOE.RGFrontier.balabanBlockSpinTransferProved
    BalabanRGTOE.RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt
  ≡ false
toeBalabanRGBlockSpinTransferStillOpen =
  BalabanRGTOE.balabanRGBlockSpinTransferStillOpen

toeBalabanRGContinuumConstructionStillOpen :
  BalabanRGTOE.RGFrontier.continuumYangMillsConstructedHere
    BalabanRGTOE.RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt
  ≡ false
toeBalabanRGContinuumConstructionStillOpen =
  BalabanRGTOE.balabanRGContinuumConstructionStillOpen

toeBalabanRGClayPromotionStillFalse :
  BalabanRGTOE.RGFrontier.clayYangMillsPromoted
    BalabanRGTOE.RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt
  ≡ false
toeBalabanRGClayPromotionStillFalse =
  BalabanRGTOE.balabanRGClayPromotionStillFalse

toeBalabanRGZKPFrame : BalabanRGTOE.BalabanTOEZKPFrame
toeBalabanRGZKPFrame =
  BalabanRGTOE.canonicalBalabanTOEZKPFrame
