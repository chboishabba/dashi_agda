module DASHI.Moonshine.P11MarkedFrobeniusResidualReceiptExact where

------------------------------------------------------------------------
-- MARKED FROBENIUS MUST MOVE THE REOPENING RESIDUAL
--
-- This is the arithmetic specialization of
-- ProvenanceFibreDynamicsReceiptExact.  The p=11 marked Frobenius swaps a0/a1
-- while the coarse supersingular j-class is unchanged.  Because the existing
-- P11Fine5 provenance quotient reopens the marked point exactly from
--
--   coarse j-class + Fine5Residual,
--
-- the hidden Frobenius move necessarily changes that residual coordinate.
--
-- Source context inherited from P11MarkedX2FrobeniusFrickeExact:
-- Adel Betina and Emmanuel Lecouturier,
-- "Congruence formulae for Legendre modular polynomials",
-- Journal of Number Theory 188 (2018), 71--87.
-- DOI: 10.1016/j.jnt.2018.01.006.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.FibrePreservingDynamicsExact as Dynamics
import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Sectioned
import DASHI.Core.ProvenanceFibreDynamicsReceiptExact as ReceiptDynamics
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11Fine5PNFProvenanceQuotientBridgeExact as PNFQuotient
import DASHI.Moonshine.P11MarkedX2FrobeniusFrickeExact as Marked

fine5PNFCore =
  Sectioned.sectionedProjectionCore PNFQuotient.fine5SectionedProjection

markedFrobeniusPreservesPNFSurface :
  Dynamics.SurfaceInvariant fine5PNFCore Marked.markedFrobenius
markedFrobeniusPreservesPNFSurface = Marked.markedFrobeniusPreservesJClass

markedFrobeniusEndomorphism : Dynamics.FibreEndomorphism fine5PNFCore
markedFrobeniusEndomorphism =
  Dynamics.fibreEndomorphism
    Marked.markedFrobenius
    markedFrobeniusPreservesPNFSurface

markedFrobeniusMovesA0 : Marked.markedFrobenius Fine.a0 ≡ Fine.a0 → ⊥
markedFrobeniusMovesA0 ()

markedFrobeniusA0HiddenTransition :
  Dynamics.HiddenTransition fine5PNFCore Marked.markedFrobenius Fine.a0
markedFrobeniusA0HiddenTransition =
  Dynamics.fibreEndomorphismHiddenWhenNontrivial
    markedFrobeniusEndomorphism
    Fine.a0
    markedFrobeniusMovesA0

markedFrobeniusMustChangeFine5Residual :
  PNFQuotient.fine5Residual (Marked.markedFrobenius Fine.a0)
    ≡ PNFQuotient.fine5Residual Fine.a0 → ⊥
markedFrobeniusMustChangeFine5Residual =
  ReceiptDynamics.hiddenTransitionChangesReceipt
    PNFQuotient.fine5PNFProvenanceQuotient
    markedFrobeniusA0HiddenTransition

markedFrobeniusResidualChangeComputes :
  PNFQuotient.r1 ≡ PNFQuotient.r0 → ⊥
markedFrobeniusResidualChangeComputes ()

record P11MarkedFrobeniusResidualBoundary : Set where
  constructor p11MarkedFrobeniusResidualBoundary
  field
    coarseJClassFixed : Bool
    coarseJClassFixedIsTrue : coarseJClassFixed ≡ true
    markedStateMoves : Bool
    markedStateMovesIsTrue : markedStateMoves ≡ true
    exactReopeningResidualMustMove : Bool
    exactReopeningResidualMustMoveIsTrue :
      exactReopeningResidualMustMove ≡ true
    hiddenMotionEqualsSemanticErasure : Bool
    hiddenMotionEqualsSemanticErasureIsFalse :
      hiddenMotionEqualsSemanticErasure ≡ false

canonicalP11MarkedFrobeniusResidualBoundary :
  P11MarkedFrobeniusResidualBoundary
canonicalP11MarkedFrobeniusResidualBoundary =
  p11MarkedFrobeniusResidualBoundary
    true refl
    true refl
    true refl
    false refl
