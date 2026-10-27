module DASHI.Unified.CollatzSyracuseTOEMaxCutExact where

------------------------------------------------------------------------
-- COLLATZ / SYRACUSE TOE MAX-CUT NORMALIZATION
--
-- O. Objective.
-- Reconcile the literal Syracuse derivations with the DASHI TOE roots.
--
-- R. Reuse.
-- Reuse the existing same-object max-cut, terminal parity max-cut, and
-- 2026 source-attribution owners.  Do not restate their proofs.
--
-- C. Construction.
-- Expose one normalized receipt and exact theorem aliases.
--
-- S. Safety.
-- Finite computation does not prove universal stopping.
-- Density decay does not prove universal stopping.
-- The old 3z/(3z-1) relation matrix is not the literal Syracuse map.
-- A source atlas does not import external theorem authority.
--
-- L. Lane.
-- One Collatz/Syracuse TOE normalization lane.
-- No ESD or digital_esd surface is edited.
--
-- P. Preconditions and invariants.
-- The imported owners exist on this branch.
-- C1-C6 and the finite parity-counting chain retain their source owners.
-- The all-start finite-barrier producer remains explicit when it is open.
-- Attribution remains with the cited mathematical authors and source repos.
--
-- G. Governance.
-- ITIL, ISO 9000/42001/27001/27701/23894/9241, NIST AI RMF,
-- Six Sigma and C4/PlantUML are process lenses only.
--
-- F. Postconditions and verification.
-- Both TOE roots can reach the same exact Collatz owners.
-- The open terminal leaf remains visible.
-- Preflight, trust scan, ESD diff scan, and Agda typecheck remain required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.CollatzSyracuseSameObjectMaxCutExact as MaxCut
import DASHI.Analysis.CollatzSyracuseTerminalParityMaxCutExact as Terminal
import DASHI.Analysis.CollatzSyracuseSOTA2026Exact as SOTA

------------------------------------------------------------------------
-- Exact reused owners.
------------------------------------------------------------------------

collatzSameObjectMaxCutBoundary : MaxCut.MaxCutBoundary
collatzSameObjectMaxCutBoundary =
  MaxCut.canonicalMaxCutBoundary

collatzTerminalParityMaxCutBoundary : Terminal.TerminalParityMaxCutBoundary
collatzTerminalParityMaxCutBoundary =
  Terminal.canonicalTerminalParityMaxCutBoundary

collatzSOTA2026Boundary : SOTA.CollatzSOTA2026Boundary
collatzSOTA2026Boundary =
  SOTA.canonicalCollatzSOTA2026Boundary

------------------------------------------------------------------------
-- Paid exact chain.
------------------------------------------------------------------------

collatzCylinderForwardPaid :
  MaxCut.cutStatus MaxCut.C3-residueCylinderForward ≡ MaxCut.proved
collatzCylinderForwardPaid =
  MaxCut.cylinderForwardPaid

collatzCylinderReversePaid :
  MaxCut.cutStatus MaxCut.C5-residueCylinderReverse ≡ MaxCut.proved
collatzCylinderReversePaid =
  MaxCut.cylinderReversePaid

collatzAffineIteratePaid :
  MaxCut.cutStatus MaxCut.C6-affineIterate ≡ MaxCut.proved
collatzAffineIteratePaid = refl

collatzCompleteBlockUniformityPaid :
  MaxCut.cutStatus MaxCut.C11b-completeBlockUniformPushforward ≡ MaxCut.proved
collatzCompleteBlockUniformityPaid =
  MaxCut.completeBlockUniformityPaid

collatzDirectBernoulliLawPaid :
  MaxCut.cutStatus MaxCut.C12a-directParityBernoulliLaw ≡ MaxCut.proved
collatzDirectBernoulliLawPaid =
  MaxCut.directBernoulliLawPaid

collatzParametricRationalTailPaid :
  MaxCut.cutStatus MaxCut.C12c2-parametricRationalTail ≡ MaxCut.proved
collatzParametricRationalTailPaid =
  MaxCut.parametricRationalTailPaid

collatzFiniteSurvivorBarrierExtractionPaid :
  MaxCut.cutStatus MaxCut.C13f-finiteSurvivorBarrierExtraction ≡ MaxCut.proved
collatzFiniteSurvivorBarrierExtractionPaid =
  MaxCut.finiteSurvivorBarrierExtractionPaid

------------------------------------------------------------------------
-- Exact terminal wall.
------------------------------------------------------------------------

collatzStrictDescentTerminalWallOpen :
  MaxCut.cutStatus MaxCut.C13d-allStartsStrictDescentProducer
  ≡ MaxCut.sourceSpecificOpen
collatzStrictDescentTerminalWallOpen =
  MaxCut.strictDescentTerminalWallVisible

collatzAllStartsFiniteBarrierProducerStillOpen :
  Terminal.TerminalParityMaxCutBoundary.allStartsFiniteBarrierProducerPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 0
collatzAllStartsFiniteBarrierProducerStillOpen =
  Terminal.finiteBarrierProducerStillOpen

collatzUnboundedResidualProducerStillOpen :
  Terminal.TerminalParityMaxCutBoundary.unboundedResidualProducerPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 0
collatzUnboundedResidualProducerStillOpen =
  Terminal.residualStillOpen

collatzOnlyCriticalOpenLeafIsLiteralResidualElimination :
  Terminal.TerminalParityMaxCutBoundary.onlyCriticalOpenLeafIsLiteralResidualElimination
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 1
collatzOnlyCriticalOpenLeafIsLiteralResidualElimination = refl

------------------------------------------------------------------------
-- Non-promotion aliases.
------------------------------------------------------------------------

collatzFiniteSearchDoesNotPromoteUniversalStopping :
  Terminal.TerminalParityMaxCutBoundary.finiteSearchPromotesUniversalStopping
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 0
collatzFiniteSearchDoesNotPromoteUniversalStopping = refl

collatzDensityDoesNotPromoteUniversalStopping :
  Terminal.TerminalParityMaxCutBoundary.densityPromotesUniversalStopping
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 0
collatzDensityDoesNotPromoteUniversalStopping = refl

collatzOldSpectralRelationDoesNotPromoteUniversalStopping :
  Terminal.TerminalParityMaxCutBoundary.oldSpectralRelationPromotesUniversalStopping
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 0
collatzOldSpectralRelationDoesNotPromoteUniversalStopping = refl

collatzNatSearchMarkovNotUnconditionallyOwned :
  Terminal.TerminalParityMaxCutBoundary.natSearchMarkovUnconditionallyPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 0
collatzNatSearchMarkovNotUnconditionallyOwned =
  Terminal.markovNotSilentlyOwned

collatzExternalSourcesDoNotImportProof :
  SOTA.CollatzSOTA2026Boundary.externalSourcesImportCollatzProof
    SOTA.canonicalCollatzSOTA2026Boundary
  ≡ 0
collatzExternalSourcesDoNotImportProof =
  SOTA.sourcesDoNotImportProof

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F normalization receipt.
------------------------------------------------------------------------

record CollatzSyracuseTOEZKPFrame : Set where
  constructor collatz-syracuse-toe-zkp-frame
  field
    objective : String
    reuse : String
    construction : String
    safetyInvariant : String
    lane : String
    preconditions : String
    governance : String
    postconditions : String
    verification : String
    esdMutationAllowed : Bool
    createsUniversalStoppingProof : Bool

canonicalCollatzSyracuseTOEZKPFrame : CollatzSyracuseTOEZKPFrame
canonicalCollatzSyracuseTOEZKPFrame =
  collatz-syracuse-toe-zkp-frame
    "connect the existing literal Syracuse max-cut and terminal frontier to the DASHI TOE"
    "reuse the same-object max-cut, terminal parity max-cut, and 2026 attribution atlas without duplicating theorem ownership"
    "expose exact aliases and one normalized receipt only"
    "finite checks, density, spectral relations, source citations, and compiler interfaces cannot promote the open all-start strict-descent producer"
    "one disjoint Collatz/Syracuse TOE normalization lane"
    "canonical owners exist; C1-C6 remain paid; the all-start finite-barrier producer remains explicit; ESD surfaces are read-only"
    "ITIL, ISO 9000/42001/27001/27701/23894/9241, NIST AI RMF, Six Sigma and C4/PlantUML are process lenses only"
    "EverythingTOESymmetryResolved369 and Unifier reach the same exact owners while the literal residual-elimination leaf remains open"
    "dashi-agda-preflight discovery and lineage, zero-trust escape scan, ESD diff scan, and Agda kernel typecheck"
    false
    false

record CollatzSyracuseTOEMaxCutReceipt : Set where
  field
    sameObjectBoundary : MaxCut.MaxCutBoundary
    terminalBoundary : Terminal.TerminalParityMaxCutBoundary
    sotaBoundary : SOTA.CollatzSOTA2026Boundary
    terminalStrictDescentOpen :
      MaxCut.cutStatus MaxCut.C13d-allStartsStrictDescentProducer
      ≡ MaxCut.sourceSpecificOpen
    allStartsFiniteBarrierOpen :
      Terminal.TerminalParityMaxCutBoundary.allStartsFiniteBarrierProducerPaid
        terminalBoundary
      ≡ 0
    finiteSearchNoPromotion :
      Terminal.TerminalParityMaxCutBoundary.finiteSearchPromotesUniversalStopping
        terminalBoundary
      ≡ 0
    densityNoPromotion :
      Terminal.TerminalParityMaxCutBoundary.densityPromotesUniversalStopping
        terminalBoundary
      ≡ 0
    oldSpectralNoPromotion :
      Terminal.TerminalParityMaxCutBoundary.oldSpectralRelationPromotesUniversalStopping
        terminalBoundary
      ≡ 0
    zkpFrame : CollatzSyracuseTOEZKPFrame

canonicalCollatzSyracuseTOEMaxCutReceipt : CollatzSyracuseTOEMaxCutReceipt
canonicalCollatzSyracuseTOEMaxCutReceipt = record
  { sameObjectBoundary = collatzSameObjectMaxCutBoundary
  ; terminalBoundary = collatzTerminalParityMaxCutBoundary
  ; sotaBoundary = collatzSOTA2026Boundary
  ; terminalStrictDescentOpen = collatzStrictDescentTerminalWallOpen
  ; allStartsFiniteBarrierOpen = collatzAllStartsFiniteBarrierProducerStillOpen
  ; finiteSearchNoPromotion = collatzFiniteSearchDoesNotPromoteUniversalStopping
  ; densityNoPromotion = collatzDensityDoesNotPromoteUniversalStopping
  ; oldSpectralNoPromotion = collatzOldSpectralRelationDoesNotPromoteUniversalStopping
  ; zkpFrame = canonicalCollatzSyracuseTOEZKPFrame
  }
