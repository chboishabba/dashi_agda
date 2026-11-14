module DASHI.Reasoning.TrialecticC3EdgeResidualRepairExact where

------------------------------------------------------------------------
-- EXACT RESIDUAL REPAIR FOR C3 EDGE ROTATION
--
-- TrialecticC3GlobalNaturalityNoGoExact proves that participant A alone cannot
-- determine participant B, so a vertex-local A->B naturality promotion fails
-- on arbitrary T^18 boundaries.
--
-- ConsumerFibreRepairExact says every sufficient repair must separate the
-- witnessed same-A/different-B states.  Here we also construct an exact repair
-- for the stronger consumer "the whole rotated AB edge": retain beside A the
-- two missing T^3 cells
--
--                  residual = (B , S_AB).
--
-- Then
--
--        (A , residual) -> rotate(A,B,S_AB) = (B,S_AB,A)
--
-- exactly.  Thus the old full T^9 edge need not be retained as a separate
-- coordinate for this consumer: the coarse A stalk plus a T^6 residual already
-- reconstructs the rotated T^9 edge.  No minimality or uniqueness of that
-- residual is claimed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; proj₁; proj₂)
open import DASHI.Core.Prelude using (⊥; cong)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as FibreRepair
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Reasoning.TrialecticC3GlobalNaturalityNoGoExact as NoGo
import DASHI.Reasoning.TrialecticGrothendieckTransportCoherenceExact as Transport
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell

record C3ABResidual : Set where
  constructor c3-ab-residual
  field
    participantB : Cell.TrialecticBasis3Cell
    synthesisAB : Cell.TrialecticBasis3Cell

open C3ABResidual public

c3ABResidualObserver :
  Cell.CompatibleThreeCellTrialecticBoundary →
  C3ABResidual
c3ABResidualObserver boundary =
  c3-ab-residual
    (Cell.rightCell (Cell.edgeAB boundary))
    (Cell.synthesisCell (Cell.edgeAB boundary))

rotatedABConsumer :
  Cell.CompatibleThreeCellTrialecticBoundary →
  Cell.CellDialectic
rotatedABConsumer boundary =
  Transport.rotateCell (Cell.edgeAB boundary)

reconstructRotatedAB :
  Cell.TrialecticBasis3Cell →
  C3ABResidual →
  Cell.CellDialectic
reconstructRotatedAB participantA residual =
  Cell.cell-dialectic
    (participantB residual)
    (synthesisAB residual)
    participantA

participantAWithResidual :
  Cell.CompatibleThreeCellTrialecticBoundary →
  Cell.TrialecticBasis3Cell × C3ABResidual
participantAWithResidual =
  Observer.pairObserver
    NoGo.participantAObserver
    c3ABResidualObserver

rotatedABFactorsThroughAWithResidual :
  Descent.FactorsThrough
    participantAWithResidual
    rotatedABConsumer
rotatedABFactorsThroughAWithResidual =
  Factorized.factorizedRefinement
    (λ pair → reconstructRotatedAB (proj₁ pair) (proj₂ pair))
    (λ boundary → refl)

anyRepairForBMustSeparateWitness :
  {Residual : Set} →
  (refine : Cell.CompatibleThreeCellTrialecticBoundary → Residual) →
  FibreRepair.RefinementRepairs
    NoGo.participantAObserver
    refine
    NoGo.participantBConsumer →
  refine NoGo.sameAFirstBoundary
    ≡ refine NoGo.sameASecondBoundary →
  ⊥
anyRepairForBMustSeparateWitness refine repaired sameResidual =
  FibreRepair.refinementRepairSeparatesWitness
    NoGo.participantANonDescentWitnessForB
    repaired
    sameResidual

selectedResidualSeparatesWitness :
  c3ABResidualObserver NoGo.sameAFirstBoundary
  ≡ c3ABResidualObserver NoGo.sameASecondBoundary →
  ⊥
selectedResidualSeparatesWitness equality =
  NoGo.differentParticipantB (cong participantB equality)

participantBResidualObserver :
  Cell.CompatibleThreeCellTrialecticBoundary →
  Cell.TrialecticBasis3Cell
participantBResidualObserver = NoGo.participantBConsumer

participantBRepairsParticipantBConsumer :
  FibreRepair.RefinementRepairs
    NoGo.participantAObserver
    participantBResidualObserver
    NoGo.participantBConsumer
participantBRepairsParticipantBConsumer
  left right samePair =
  cong proj₂ samePair

data SelectedC3ResidualIsMinimalUnique : Set where
data SelectedC3ResidualIsEmpiricalPsychologicalState : Set where

selectedResidualNotClaimedMinimalUnique :
  SelectedC3ResidualIsMinimalUnique → ⊥
selectedResidualNotClaimedMinimalUnique ()

selectedResidualNotPromotedToEmpiricalPsychology :
  SelectedC3ResidualIsEmpiricalPsychologicalState → ⊥
selectedResidualNotPromotedToEmpiricalPsychology ()

record TrialecticC3EdgeResidualRepairBoundary : Set where
  constructor trialectic-c3-edge-residual-repair-boundary
  field
    sameAWitnessBlocksAOnlyRepair : Bool
    everySufficientResidualMustSeparateWitness : Bool
    participantBAloneRepairsBConsumer : Bool
    selectedResidualCarriesBAndSynthesisAB : Bool
    selectedResidualReconstructsWholeRotatedEdge : Bool
    oldFullT9EdgeRequiredForRotatedEdgeConsumer : Bool
    selectedResidualClaimedMinimalUnique : Bool
    residualPromotedToEmpiricalPsychology : Bool

open TrialecticC3EdgeResidualRepairBoundary public

canonicalTrialecticC3EdgeResidualRepairBoundary :
  TrialecticC3EdgeResidualRepairBoundary
canonicalTrialecticC3EdgeResidualRepairBoundary =
  trialectic-c3-edge-residual-repair-boundary
    true true true true true false false false
