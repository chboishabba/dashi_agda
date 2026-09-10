module DASHI.Physics.Closure.NSTriadKNSpectatorNestedOuterSwapGluingBoundaryExact where

------------------------------------------------------------------------
-- OUTER SWAP / GLUING BOUNDARY AFTER THE LOCAL LH <-> HL QUOTIENT
--
-- The graph-colouring cross-pollination says that a local recolouring may be
-- quotiented only after the actual downstream consumer descends through it.
-- The inner R584 consumer has now paid LH <-> HL.  This file records why that
-- does NOT automatically quotient the outer R573 spectator cells.
--
-- Swapping one outer physical incidence preserves k but exchanges p and q.
-- R573's nestedSlotFold is indexed by the INNER physical output fibre over p,
-- and its outer slot also uses q as the velocity slot.  Consequently the raw
-- outer vector consumer after swap is not definitionally the same consumer:
--
--   fibre(p_tau) / velocity(q_tau)
--     -> fibre(q_tau) / velocity(p_tau).
--
-- A new same-object theorem would therefore be needed before promoting the
-- local orbit quotient to an outer vector quotient.  We do not invent it.
--
-- At the COMPLETE SCALAR square, however, R566/R567 already provide the valid
-- global transpose quotient: the amplitude half is the transpose of the
-- forcing half and the complete factored square becomes four times one forcing
-- square.  Thus the correct global quotient exists at the scalar consumer, not
-- automatically at the selected outer-vector consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNFactoredFullTransposeSymmetryRound566Exact as R566
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567

------------------------------------------------------------------------
-- Exact outer-index coordinate transport already owned by the physical swap.
------------------------------------------------------------------------

outerSwapPreservesOutput :
  (tau : Physical.PhysicalTriadIncidence) →
  Physical.k (Symmetry.swapTriad tau) ≡ Physical.k tau
outerSwapPreservesOutput = Symmetry.swapTriadK

outerSwapMovesInnerOutputFromPToQ :
  (tau : Physical.PhysicalTriadIncidence) →
  Physical.p (Symmetry.swapTriad tau) ≡ Physical.q tau
outerSwapMovesInnerOutputFromPToQ = Symmetry.swapTriadP

outerSwapMovesVelocitySlotFromQToP :
  (tau : Physical.PhysicalTriadIncidence) →
  Physical.q (Symmetry.swapTriad tau) ≡ Physical.p tau
outerSwapMovesVelocitySlotFromQToP = Symmetry.swapTriadQ

------------------------------------------------------------------------
-- Typed residual: what would actually be required to quotient the selected
-- outer vector carrier under p/q swap.
------------------------------------------------------------------------

data OuterSwapGluingResidual : Set where
  proveInnerOutputFibreTransportPToQ : OuterSwapGluingResidual
  proveNestedSlotConsumerTransportUnderOuterSwap : OuterSwapGluingResidual
  proveSelectedOuterCellConsumerInvariant : OuterSwapGluingResidual
  selectedOuterSwapQuotientClosed : OuterSwapGluingResidual

firstOuterSwapGluingResidual : OuterSwapGluingResidual
firstOuterSwapGluingResidual = proveInnerOutputFibreTransportPToQ

------------------------------------------------------------------------
-- Boundary / proof-search result.
------------------------------------------------------------------------

record OuterSwapGluingBoundary : Set where
  constructor outer-swap-gluing-boundary
  field
    outerSwapPreservesK : Bool
    outerSwapExchangesPAndQ : Bool
    innerLHHLQuotientImpliesOuterVectorSwapInvariant : Bool
    selectedOuterVectorSwapInvariantProved : Bool
    completeScalarTransposeQuotientAlreadyClosed : Bool
    independentAmplitudeFullSquareStillRequired : Bool
    selectedOuterSignedGramStillLive : Bool

canonicalOuterSwapGluingBoundary : OuterSwapGluingBoundary
canonicalOuterSwapGluingBoundary =
  outer-swap-gluing-boundary
    true
    true
    false
    false
    R566.round566FullAmplitudeAndForcingHalvesEqual
    R567.round567IndependentAmplitudeSpacetimeEstimateRequired
    true

localOrbitQuotientDoesNotPromoteOuterVectorQuotient : Bool
localOrbitQuotientDoesNotPromoteOuterVectorQuotient = true

scalarTransposeIsCorrectGlobalQuotient : Bool
scalarTransposeIsCorrectGlobalQuotient = true

selectedOuterGramStillLeastPrivilegeResidual : Bool
selectedOuterGramStillLeastPrivilegeResidual = true

clayPromotion : Bool
clayPromotion = false

localOrbitQuotientDoesNotPromoteOuterVectorQuotientIsTrue :
  localOrbitQuotientDoesNotPromoteOuterVectorQuotient ≡ true
localOrbitQuotientDoesNotPromoteOuterVectorQuotientIsTrue = refl

selectedOuterGramStillLeastPrivilegeResidualIsTrue :
  selectedOuterGramStillLeastPrivilegeResidual ≡ true
selectedOuterGramStillLeastPrivilegeResidualIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
