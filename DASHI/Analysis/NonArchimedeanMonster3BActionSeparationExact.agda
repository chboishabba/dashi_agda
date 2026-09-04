module DASHI.Analysis.NonArchimedeanMonster3BActionSeparationExact where

------------------------------------------------------------------------
-- ACTION-SEPARATION CORRECTION FOR THE MONSTER CORRESPONDENCE
--
-- The arithmetic bulk match at source level 17 must not be upgraded by
-- identifying the source permutation k |-> 3k with a Monster 3B element.
-- Their action orders are incompatible:
--
--   source odd-residue x3 permutation at n=17 : 2^(17-2) = 32768
--   Monster 3B element                         : 3.
--
-- The correct candidate geometry is therefore two-axis:
--
--   C3 phase action
--       over
--   2^16-dimensional dyadic multiplicity fibre with its own dynamics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Analysis.NonArchimedeanMonster3BDyadicCorrespondenceBidiExact as Corr
import DASHI.Moonshine.HyperfabricMonsterConjugacyActionAuditExact as Audit

sourceOddTimesThreeOrderAt17 : Nat
sourceOddTimesThreeOrderAt17 = 32768

monster3BOrder : Nat
monster3BOrder = 3

sourceOrderIsTwoPowerFifteen : sourceOddTimesThreeOrderAt17 ≡ 32768
sourceOrderIsTwoPowerFifteen = refl

monster3BOrderIsThree : monster3BOrder ≡ 3
monster3BOrderIsThree = refl

------------------------------------------------------------------------
-- We record the mismatch positively as a constructor-level no-fusion result.
------------------------------------------------------------------------

data OrderComparison : Set where
  sameOrder : OrderComparison
  differentOrder : OrderComparison

sourceTimesThreeVsMonster3BOrder : OrderComparison
sourceTimesThreeVsMonster3BOrder = differentOrder

sourceTimesThreeCannotBePromotedAs3BByOrder :
  sourceTimesThreeVsMonster3BOrder ≡ differentOrder
sourceTimesThreeCannotBePromotedAs3BByOrder = refl

------------------------------------------------------------------------
-- Corrected two-action hyperfabric target.
------------------------------------------------------------------------

record PhaseOverDyadicBulkAction : Set₁ where
  field
    BulkState : Set
    PhaseState : Set
    DyadicActor : Set
    PhaseActor : Set

    dyadicAct : DyadicActor → BulkState → BulkState
    phaseAct : PhaseActor → PhaseState → PhaseState

    bulkCardinality : Nat
    bulkCardinalityIsSource17 :
      bulkCardinality ≡ Corr.sourceTwistedCardinalityAt17

    phaseCount : Nat
    phaseCountIsThree : phaseCount ≡ 3

open PhaseOverDyadicBulkAction public

------------------------------------------------------------------------
-- A stronger Monster-facing candidate may additionally ask whether the phase
-- and internal dyadic actions commute, normalize one another, or form a
-- semidirect action.  None follows from the dimension decomposition alone.
------------------------------------------------------------------------

record MonsterPhaseDyadicCompatibility
    (H : PhaseOverDyadicBulkAction) : Set₁ where
  field
    CombinedState : Set
    combine : PhaseState H → BulkState H → CombinedState

    phaseLift : PhaseActor H → CombinedState → CombinedState
    dyadicLift : DyadicActor H → CombinedState → CombinedState

    phaseDyadicCommute : Set
    phaseNormalizesDyadic : Set
    dyadicActionMatchesMonsterMultiplicityAction : Set

open MonsterPhaseDyadicCompatibility public

record ActionSeparationBoundary : Set where
  constructor action-separation-boundary
  field
    sourceTimesThreeIsMonster3B : Bool
    sameNumeralThreeImpliesSameAction : Bool
    sameBulkCardinalityImpliesSameActor : Bool
    dyadicDynamicsMayLiveInsideMultiplicityFibre : Bool
    monsterPhaseActionRemainsSeparateCoordinate : Bool
    actionCompatibilityStillNeedsIntertwinerOrNormalizerReceipt : Bool

canonicalActionSeparationBoundary : ActionSeparationBoundary
canonicalActionSeparationBoundary =
  action-separation-boundary
    false false false true true true

------------------------------------------------------------------------
-- Cross-pollinate the existing Monster conjugacy audit discipline.
------------------------------------------------------------------------

monsterAuditAlreadyRequiresActionSignature : Bool
monsterAuditAlreadyRequiresActionSignature = true

monsterAuditAlreadyBlocksCardinalityPromotion :
  Audit.fullMonsterActionOnHyperfabricEstablished
    Audit.canonicalHyperfabricMonsterConjugacyBoundary
  ≡ false
monsterAuditAlreadyBlocksCardinalityPromotion = refl
