module DASHI.Moonshine.OggSSPMarkedArithmeticResidualCoverPatternExact where

------------------------------------------------------------------------
-- MARKED ARITHMETIC RESIDUAL COVER PATTERN
--
-- Cross-pollinated from the source-native p=11 marked Frobenius construction.
--
-- Generic shape:
--
--   fine marked arithmetic state
--        -> coarse arithmetic surface
--        + exact reopening residual
--
-- together with a nontrivial fibre automorphism preserving the coarse surface.
--
-- Exact reopening then forces that hidden symmetry to move the residual.
--
-- This is an ACQUISITION PATTERN.  It does not construct the missing p=2/p=3
-- exponent-residual arithmetic sources, and it does not identify the coarse
-- surface with supersingular j unless an application supplies that theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Sectioned
import DASHI.Core.FibrePreservingDynamicsExact as Dynamics
import DASHI.Core.ProvenanceBearingQuotient as Quotient
import DASHI.Core.ProvenanceFibreDynamicsReceiptExact as ReceiptDynamics
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source

record MarkedArithmeticResidualCover : Set₁ where
  constructor marked-arithmetic-residual-cover
  field
    Fine : Set
    Coarse : Set

    projection :
      Sectioned.SectionedProjection Fine Coarse

    reopening :
      Sectioned.ResidualReopening projection

    hiddenSymmetry :
      Dynamics.NontrivialFibreAutomorphism
        (Sectioned.sectionedProjectionCore projection)

    arithmeticProvenance : String
    constructionReference : String

open MarkedArithmeticResidualCover public

coverCore :
  MarkedArithmeticResidualCover ->
  DASHI.Core.FibreRestrictionCore.FibreRestrictionCore
coverCore cover =
  Sectioned.sectionedProjectionCore (projection cover)

coverQuotient :
  (cover : MarkedArithmeticResidualCover) ->
  Quotient.ProvenanceBearingQuotient (coverCore cover)
coverQuotient cover =
  Sectioned.residualReopeningGivesProvenanceBearingQuotient
    (reopening cover)

markedSymmetryChangesResidual :
  (cover : MarkedArithmeticResidualCover) ->
  Quotient.receipt (coverQuotient cover)
      (Dynamics.forward
        (Dynamics.automorphism (hiddenSymmetry cover))
        (Dynamics.movedPoint (hiddenSymmetry cover)))
  ≡
  Quotient.receipt (coverQuotient cover)
      (Dynamics.movedPoint (hiddenSymmetry cover))
  ->
  ⊥
markedSymmetryChangesResidual cover =
  ReceiptDynamics.nontrivialFibreAutomorphismChangesReceipt
    (coverQuotient cover)
    (hiddenSymmetry cover)

markedCoverProjectionIsNotInjective :
  (cover : MarkedArithmeticResidualCover) ->
  ((a b : Fine cover) ->
    Sectioned.project (projection cover) a
    ≡ Sectioned.project (projection cover) b ->
    a ≡ b)
  ->
  ⊥
markedCoverProjectionIsNotInjective cover =
  Dynamics.nontrivialFibreAutomorphismBlocksProjectionInjectivity
    (hiddenSymmetry cover)

------------------------------------------------------------------------
-- p=11 proves this pattern is not merely hypothetical in the repo.
--
-- We keep the witness as a receipt-level bridge because the source-native
-- p=11 owner already contains the actual fine carrier and Frobenius action.
------------------------------------------------------------------------

record ExistingMarkedArithmeticPatternReceipt : Set where
  constructor existing-marked-arithmetic-pattern-receipt
  field
    sourceOwner : String
    coarseArithmeticClassFixed : Bool
    markedStateMoves : Bool
    exactReopeningResidualMoves : Bool
    patternPromotedToP2P3Source : Bool

p11PatternReceipt : ExistingMarkedArithmeticPatternReceipt
p11PatternReceipt =
  existing-marked-arithmetic-pattern-receipt
    "DASHI.Moonshine.P11MarkedFrobeniusResidualReceiptExact"
    true
    true
    true
    false

------------------------------------------------------------------------
-- Small-characteristic acquisition socket.
------------------------------------------------------------------------

data ExceptionalResidualPrime : Set where
  residualP2 residualP3 : ExceptionalResidualPrime

record MarkedResidualSourceCandidate
    (prime : ExceptionalResidualPrime) : Set₁ where
  constructor marked-residual-source-candidate
  field
    cover : MarkedArithmeticResidualCover
    coarseSurfaceHasArithmeticMeaning : Bool
    coarseSurfaceArithmeticReference : String
    hiddenSymmetryHasArithmeticMeaning : Bool
    hiddenSymmetryArithmeticReference : String

open MarkedResidualSourceCandidate public

data P11PatternAutomaticallySuppliesP2P3Source : Set where

p11PatternDoesNotAutomaticallySupplyP2P3Source :
  P11PatternAutomaticallySuppliesP2P3Source -> ⊥
p11PatternDoesNotAutomaticallySupplyP2P3Source ()

patternOrigin : Source.ClaimOrigin
patternOrigin = Source.repositoryCrossModuleInference

record MarkedArithmeticResidualCoverBoundary : Set where
  constructor marked-arithmetic-residual-cover-boundary
  field
    genericMarkedCoverPatternOwned : Bool
    exactReopeningRequired : Bool
    nontrivialFibreSymmetryRequired : Bool
    hiddenSymmetryForcesResidualMotion : Bool
    coarseProjectionProvablyLossyUnderHiddenMotion : Bool
    p11PatternRecordedAsExistingInstance : Bool
    p11PatternPromotedToP2P3ArithmeticSource : Bool
    p2CandidateInhabitedHere : Bool
    p3CandidateInhabitedHere : Bool

canonicalMarkedArithmeticResidualCoverBoundary :
  MarkedArithmeticResidualCoverBoundary
canonicalMarkedArithmeticResidualCoverBoundary =
  marked-arithmetic-residual-cover-boundary
    true true true true true true
    false false false
