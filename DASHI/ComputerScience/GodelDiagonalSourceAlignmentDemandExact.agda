module DASHI.ComputerScience.GodelDiagonalSourceAlignmentDemandExact where

open import DASHI.Core.Prelude

import DASHI.Core.ProofDebtRouterExact as Debt

------------------------------------------------------------------------
-- EXACT SOURCE-ALIGNMENT DEMANDS FOR THE REMAINING SOURCE-NATIVE DIAGONAL
-- COORDINATES.  This is provenance/alignment data only: no theorem inhabitant
-- is manufactured from it.
------------------------------------------------------------------------

primitiveRecursiveRepresentabilitySource : Debt.SourceIdentity
primitiveRecursiveRepresentabilitySource =
  Debt.source-identity
    "Kurt Gödel"
    "Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I"
    "10.1007/BF01700692"
    "Theorem V / preceding primitive-recursive coding construction"
    "1931"

primitiveRecursiveRepresentabilityAlignment : Debt.StatementAlignmentReceipt
primitiveRecursiveRepresentabilityAlignment =
  Debt.statement-alignment-receipt
    "Every primitive-recursive number-theoretic relation is numeralwise expressible in system P; the preceding coding construction includes substitution on Gödel codes among the primitive-recursive relations/functions."
    "For the SAME chosen arithmetic formal system and SAME primitive-recursive authority, every admitted primitive-recursive unary function has the graph-representation strength consumed by GodelPrimitiveRecursiveRepresentabilityBridgeExact."
    false
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- We deliberately do not construct `FullyAligned` here.  The local contract
-- currently packages strong graph representation of unary functions, whereas
-- the primary source statement is phrased for primitive-recursive relations
-- and Gödel's own system P/coding.  That domain/strength/code weld is the live
-- transcription residual.
------------------------------------------------------------------------

data CitationMeansFullyAlignedRepresentability : Set where

data GodelSystemPMeansArbitraryLocalFormalSystem : Set where

data RelationRepresentabilityMeansFunctionGraphRepresentationForFree : Set where

citationDoesNotCloseAlignment :
  CitationMeansFullyAlignedRepresentability → ⊥
citationDoesNotCloseAlignment ()

systemPDoesNotSilentlyGeneralise :
  GodelSystemPMeansArbitraryLocalFormalSystem → ⊥
systemPDoesNotSilentlyGeneralise ()

relationTheoremNeedsGraphAdapter :
  RelationRepresentabilityMeansFunctionGraphRepresentationForFree → ⊥
relationTheoremNeedsGraphAdapter ()

record GodelDiagonalSourceAlignmentBoundary : Set where
  constructor godelDiagonalSourceAlignmentBoundary
  field
    exactSourceIdentityPinned : Bool
    theoremVFamilyPinned : Bool
    sourceToLocalGraphStrengthAligned : Bool
    sourceCodingToLocalCodingAligned : Bool
    fullyAlignedDeferredTheoremConstructed : Bool

canonicalGodelDiagonalSourceAlignmentBoundary :
  GodelDiagonalSourceAlignmentBoundary
canonicalGodelDiagonalSourceAlignmentBoundary =
  godelDiagonalSourceAlignmentBoundary true true false false false
