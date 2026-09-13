module DASHI.ComputerScience.RSA260GraphColouringF2PairProjectionCrossPollinationExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BlockWiedemannProjectionSequence256Exact as Projection

------------------------------------------------------------------------
-- GRAPH-COLOURING / RSA-260 F2^2 CROSS-POLLINATION
--
-- The sibling graph-colouring tranche (PR #880, branch
-- agent/recolour-pants-graph-theory-snowball) uses four labels 00,01,10,11 and
-- retains three nonzero transition classes.  On the RSA side those four labels
-- may be read as the four vectors of F2^2, where the three nonzero differences
-- are exactly 01,10,11.
--
-- This owner imports only the structural algebraic lesson; it does not import
-- PR #880 as a dependency and does not identify graph colouring with Block
-- Wiedemann.  The valid RSA symmetry is a linear basis change A in GL(2,2)
-- paired covariantly with A^{-T} on the dual carrier, preserving the GF(2)
-- bilinear pairing.  Arbitrary colour permutations/Kempe moves are not promoted
-- to linear-algebra symmetries.
------------------------------------------------------------------------

record GraphColouringSourceCoordinate : Set where
  constructor graph-colouring-source-coordinate
  field
    repository : String
    pullRequest : Nat
    branch : String
    ownerPath : String
    fourStateLabels : Nat
    nonzeroDifferenceClasses : Nat
    proofImportedIntoRSA : Bool
open GraphColouringSourceCoordinate public

graphColouringCoordinate : GraphColouringSourceCoordinate
graphColouringCoordinate = graph-colouring-source-coordinate
  "chboishabba/dashi_agda"
  880
  "agent/recolour-pants-graph-theory-snowball"
  "DASHI/Combinatorics/GraphColouringRecolourPantsSnowballExact.agda"
  4 3 false

record F2PairCovarianceReceipt : Set where
  constructor f2-pair-covariance-receipt
  field
    field : String
    pairDimension : Nat
    stateCount : Nat
    nonzeroStateCount : Nat
    invertibleBasisChanges : Nat
    ambientRSAWidth : Nat
    pairedSymbols : Nat
    primalTransform : String
    dualTransform : String
    preservedObserver : String
    localExhaustiveChecks : Nat
    broadWidth256Checks : Nat
    runtimeExecutionPassed : Bool
    arbitraryColourPermutationIsLinearBasisChange : Bool
    kempeMoveIsBlockWiedemannSymmetry : Bool
open F2PairCovarianceReceipt public

f2PairCovarianceReceipt : F2PairCovarianceReceipt
f2PairCovarianceReceipt = f2-pair-covariance-receipt
  "GF(2)"
  2
  4
  3
  6
  256
  128
  "right/primal pair x -> A x"
  "left/dual pair y -> A^{-T} y"
  "GF(2) bilinear dot pairing"
  96
  1572864
  true
  false false

priorProjectionBoundary : Projection.RSA260ProjectionSequenceRoadmapBoundary
priorProjectionBoundary = Projection.currentRSA260ProjectionSequenceRoadmapBoundary

record GraphColouringRSAProjectionBoundary : Set where
  constructor graph-colouring-rsa-projection-boundary
  field
    fourStateF2PairBridgeLocated : Bool
    threeNonzeroDifferencesRetained : Bool
    gl2OrderSixRetained : Bool
    basisCovariantPairingExecutionPaid : Bool
    projectionSequenceAlreadyExecutable : Bool
    graphColouringProofReproduced : Bool
    graphColouringSemanticsImportedIntoGF2 : Bool
    arbitraryRecolouringPreservesProjection : Bool
    basisCovarianceProvesProductionRunIdentity : Bool
    basisCovarianceUsefulAsMetamorphicTest : Bool
open GraphColouringRSAProjectionBoundary public

currentGraphColouringRSAProjectionBoundary : GraphColouringRSAProjectionBoundary
currentGraphColouringRSAProjectionBoundary = graph-colouring-rsa-projection-boundary
  true true true true true
  false false false false
  true

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data FourColourTheoremImpliesBlockWiedemann : Set where
data SameFourStateCarrierImpliesSameSemantics : Set where
data ArbitraryColourPermutationImpliesGL2 : Set where
data LocalRecolouringImpliesProjectionInvariance : Set where
data PairingInvarianceImpliesExactProductionRun : Set where

fourColourDoesNotSolveBlockWiedemann : FourColourTheoremImpliesBlockWiedemann → ⊥
fourColourDoesNotSolveBlockWiedemann ()

sameCarrierDoesNotIdentifySemantics : SameFourStateCarrierImpliesSameSemantics → ⊥
sameCarrierDoesNotIdentifySemantics ()

arbitraryPermutationDoesNotBecomeLinear : ArbitraryColourPermutationImpliesGL2 → ⊥
arbitraryPermutationDoesNotBecomeLinear ()

localRecolourDoesNotCreateProjectionInvariant : LocalRecolouringImpliesProjectionInvariance → ⊥
localRecolourDoesNotCreateProjectionInvariant ()

invarianceDoesNotIdentifyRun : PairingInvarianceImpliesExactProductionRun → ⊥
invarianceDoesNotIdentifyRun ()
