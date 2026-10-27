module DASHI.EverythingTOESymmetryResolved369 where

open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- Focused TOE aggregate: generic symmetry-resolved fibre calculus plus the
-- existing SSP/369 representation-reduction and physics instances.
------------------------------------------------------------------------

import DASHI.Core.SymmetryResolvedFibreExact
import DASHI.EverythingSSPRepresentationReductionRound9
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact

------------------------------------------------------------------------
-- Literal Collatz/Syracuse max-cut normalization.
--
-- Reuse the theorem owners.  Keep the terminal all-start producer open.
------------------------------------------------------------------------

import DASHI.Unified.CollatzSyracuseTOEMaxCutExact as CollatzTOE
import DASHI.Analysis.CollatzSyracuseSameObjectMaxCutExact as CollatzMaxCut
import DASHI.Analysis.CollatzSyracuseTerminalParityMaxCutExact as CollatzTerminal

toeCollatzSyracuseMaxCutReceipt :
  CollatzTOE.CollatzSyracuseTOEMaxCutReceipt
toeCollatzSyracuseMaxCutReceipt =
  CollatzTOE.canonicalCollatzSyracuseTOEMaxCutReceipt

toeCollatzCylinderForwardPaid :
  CollatzMaxCut.cutStatus CollatzMaxCut.C3-residueCylinderForward
  ≡ CollatzMaxCut.proved
toeCollatzCylinderForwardPaid =
  CollatzTOE.collatzCylinderForwardPaid

toeCollatzAffineIteratePaid :
  CollatzMaxCut.cutStatus CollatzMaxCut.C6-affineIterate
  ≡ CollatzMaxCut.proved
toeCollatzAffineIteratePaid =
  CollatzTOE.collatzAffineIteratePaid

toeCollatzDirectBernoulliLawPaid :
  CollatzMaxCut.cutStatus CollatzMaxCut.C12a-directParityBernoulliLaw
  ≡ CollatzMaxCut.proved
toeCollatzDirectBernoulliLawPaid =
  CollatzTOE.collatzDirectBernoulliLawPaid

toeCollatzStrictDescentTerminalWallOpen :
  CollatzMaxCut.cutStatus CollatzMaxCut.C13d-allStartsStrictDescentProducer
  ≡ CollatzMaxCut.sourceSpecificOpen
toeCollatzStrictDescentTerminalWallOpen =
  CollatzTOE.collatzStrictDescentTerminalWallOpen

toeCollatzAllStartsFiniteBarrierProducerStillOpen :
  CollatzTerminal.TerminalParityMaxCutBoundary.allStartsFiniteBarrierProducerPaid
    CollatzTerminal.canonicalTerminalParityMaxCutBoundary
  ≡ 0
toeCollatzAllStartsFiniteBarrierProducerStillOpen =
  CollatzTOE.collatzAllStartsFiniteBarrierProducerStillOpen

toeCollatzFiniteSearchDoesNotPromoteUniversalStopping :
  CollatzTerminal.TerminalParityMaxCutBoundary.finiteSearchPromotesUniversalStopping
    CollatzTerminal.canonicalTerminalParityMaxCutBoundary
  ≡ 0
toeCollatzFiniteSearchDoesNotPromoteUniversalStopping =
  CollatzTOE.collatzFiniteSearchDoesNotPromoteUniversalStopping
