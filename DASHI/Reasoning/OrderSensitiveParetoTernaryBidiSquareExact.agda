module DASHI.Reasoning.OrderSensitiveParetoTernaryBidiSquareExact where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.IntellectualReceptionSituatedInformationParetoPreorderExact as Pareto
import DASHI.Reasoning.Spacy369ForwardBackwardRevisionSquareExact as Square
import DASHI.Computation.SSSPThreeFrontierBinaryTernaryFactorExact as SSSP
import DASHI.Governance.SexedHistoricalProductiveDialecticalFibreJoinExact as Dialectic
import DASHI.Reasoning.Spacy369CoverageHyperfabricMonsterBoundaryExact as MonsterBoundary

------------------------------------------------------------------------
-- ORDER-SENSITIVE PARETO / TERNARY BIDI CROSS-POLLINATION.
--
-- Canonical repo state now contains all donor owners directly on master.
-- This module therefore composes their actual proof-bearing surfaces instead
-- of copying draft-local analogues.
--
-- The central correction is simple but important:
--
--   a Pareto preorder has four relevant pair-relations
--     left strict / right strict / incomparable / equivalent,
--
-- while a three-valued consumer can expose only three coarse outcomes unless
-- one of those cases is excluded by a premise.  We retain the lost distinction
-- as a binary residual, exactly in the consumer-quotient spirit of the merged
-- SSSP ternary-minimum / binary-tail factorisation.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Proof-relevant four-way Pareto relation on the canonical six-axis profile.
------------------------------------------------------------------------

data ParetoKind4 : Set where
  leftStrictKind rightStrictKind incomparableKind equivalentKind : ParetoKind4

data ParetoFourWay
    (left right : Pareto.SituatedInformationProfile) : Set where
  leftStrict :
    Pareto.ParetoNoWorse right left →
    (Pareto.ParetoNoWorse left right → ⊥) →
    ParetoFourWay left right
  rightStrict :
    Pareto.ParetoNoWorse left right →
    (Pareto.ParetoNoWorse right left → ⊥) →
    ParetoFourWay left right
  incomparable :
    (Pareto.ParetoNoWorse left right → ⊥) →
    (Pareto.ParetoNoWorse right left → ⊥) →
    ParetoFourWay left right
  equivalent :
    Pareto.ParetoNoWorse left right →
    Pareto.ParetoNoWorse right left →
    ParetoFourWay left right

kindOf :
  ∀ {left right} →
  ParetoFourWay left right → ParetoKind4
kindOf (leftStrict _ _) = leftStrictKind
kindOf (rightStrict _ _) = rightStrictKind
kindOf (incomparable _ _) = incomparableKind
kindOf (equivalent _ _) = equivalentKind

canonicalIncomparable :
  ParetoFourWay Pareto.discriminatorProfile Pareto.governedProfile
canonicalIncomparable =
  incomparable
    (Pareto.leftNotBelowRight
      Pareto.canonicalSituatedInformationIncomparability)
    (Pareto.rightNotBelowLeft
      Pareto.canonicalSituatedInformationIncomparability)

canonicalEquivalent :
  ParetoFourWay Pareto.governedProfile Pareto.governedProfile
canonicalEquivalent =
  equivalent
    (Pareto.paretoRefl Pareto.governedProfile)
    (Pareto.paretoRefl Pareto.governedProfile)

incomparableAndEquivalentAreDifferentKinds :
  incomparableKind ≡ equivalentKind → ⊥
incomparableAndEquivalentAreDifferentKinds ()

------------------------------------------------------------------------
-- 2. Three-valued consumer quotient.
--
-- Strict left/right remain oriented.  Both non-strict cases project to mid.
-- Thus mid is consumer-relative: here it means "no strict orientation exposed",
-- not one unique hidden relation.
------------------------------------------------------------------------

paretoTritKind : ParetoKind4 → Base.TriTruth
paretoTritKind leftStrictKind = Base.tri-high
paretoTritKind rightStrictKind = Base.tri-low
paretoTritKind incomparableKind = Base.tri-mid
paretoTritKind equivalentKind = Base.tri-mid

canonicalIncomparabilityChartsMid :
  paretoTritKind (kindOf canonicalIncomparable) ≡ Base.tri-mid
canonicalIncomparabilityChartsMid = refl

canonicalEquivalenceChartsMid :
  paretoTritKind (kindOf canonicalEquivalent) ≡ Base.tri-mid
canonicalEquivalenceChartsMid = refl

midConflatesIncomparabilityAndEquivalence :
  paretoTritKind incomparableKind ≡ paretoTritKind equivalentKind
midConflatesIncomparabilityAndEquivalence = refl

fullKindObserver : ParetoKind4 → ParetoKind4
fullKindObserver kind = kind

ternaryParetoProjectionCannotRecoverFullFourWayKind :
  INF.FactorsThrough paretoTritKind fullKindObserver → ⊥
ternaryParetoProjectionCannotRecoverFullFourWayKind =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      incomparableKind
      equivalentKind
      refl
      incomparableAndEquivalentAreDifferentKinds)

------------------------------------------------------------------------
-- 3. Binary residual repairs the exact collision used above.
--
-- This is an ambient Trit × Bit-style refinement shape.  It is not asserted to
-- be a six-state Pareto ontology: only four semantic codes are occupied here.
------------------------------------------------------------------------

data ParetoResidualBit : Set where
  nonEquivalentResidual equivalentResidual : ParetoResidualBit

record ParetoTritResidualCode : Set where
  constructor paretoTritResidualCode
  field
    coarseTrit : Base.TriTruth
    residualBit : ParetoResidualBit

open ParetoTritResidualCode public

fineParetoCode : ParetoKind4 → ParetoTritResidualCode
fineParetoCode leftStrictKind =
  paretoTritResidualCode Base.tri-high nonEquivalentResidual
fineParetoCode rightStrictKind =
  paretoTritResidualCode Base.tri-low nonEquivalentResidual
fineParetoCode incomparableKind =
  paretoTritResidualCode Base.tri-mid nonEquivalentResidual
fineParetoCode equivalentKind =
  paretoTritResidualCode Base.tri-mid equivalentResidual

forgetParetoResidual : ParetoTritResidualCode → Base.TriTruth
forgetParetoResidual = coarseTrit

forgetFineCodeAgreesWithTernary :
  (kind : ParetoKind4) →
  forgetParetoResidual (fineParetoCode kind) ≡ paretoTritKind kind
forgetFineCodeAgreesWithTernary leftStrictKind = refl
forgetFineCodeAgreesWithTernary rightStrictKind = refl
forgetFineCodeAgreesWithTernary incomparableKind = refl
forgetFineCodeAgreesWithTernary equivalentKind = refl

midResidualsSeparateTheCollision :
  residualBit (fineParetoCode incomparableKind)
  ≡ residualBit (fineParetoCode equivalentKind) → ⊥
midResidualsSeparateTheCollision ()

ssspThreeByTwoResidualPrecedent : SSSP.BinaryTernaryFactorBoundary
ssspThreeByTwoResidualPrecedent = SSSP.canonicalBinaryTernaryFactorBoundary

------------------------------------------------------------------------
-- 4. Revision order can change the intermediate situated profile while both
--    routes reconverge on the same final profile.
------------------------------------------------------------------------

data RoutedRevision : Set where
  forwardFirst backwardFirst : RoutedRevision

revisionHistory : RoutedRevision → Square.RevisionHistory
revisionHistory forwardFirst = Square.historyForwardThenBackward
revisionHistory backwardFirst = Square.historyBackwardThenForward

intermediateProfile :
  RoutedRevision → Pareto.SituatedInformationProfile
intermediateProfile forwardFirst = Pareto.discriminatorProfile
intermediateProfile backwardFirst = Pareto.governedProfile

intermediateRoutesAreParetoIncomparable :
  Pareto.ParetoIncomparable
    (intermediateProfile forwardFirst)
    (intermediateProfile backwardFirst)
intermediateRoutesAreParetoIncomparable =
  Pareto.canonicalSituatedInformationIncomparability

fullyStrengthenedProfile : Pareto.SituatedInformationProfile
fullyStrengthenedProfile =
  Pareto.situated-information-profile
    Pareto.strong Pareto.strong Pareto.strong
    Pareto.strong Pareto.strong Pareto.strong

terminalProfile : RoutedRevision → Pareto.SituatedInformationProfile
terminalProfile forwardFirst = fullyStrengthenedProfile
terminalProfile backwardFirst = fullyStrengthenedProfile

sameTerminalProfile :
  terminalProfile forwardFirst ≡ terminalProfile backwardFirst
sameTerminalProfile = refl

routeOrderResidue : RoutedRevision → Square.RevisionOrderResidue
routeOrderResidue route = Square.orderResidue (revisionHistory route)

routeOrderResiduesDiffer :
  routeOrderResidue forwardFirst ≡ routeOrderResidue backwardFirst → ⊥
routeOrderResiduesDiffer ()

terminalProfileCannotRecoverRevisionOrder :
  INF.FactorsThrough terminalProfile routeOrderResidue → ⊥
terminalProfileCannotRecoverRevisionOrder =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      forwardFirst
      backwardFirst
      sameTerminalProfile
      routeOrderResiduesDiffer)

terminalProfileIsParetoEquivalentToItself :
  ParetoFourWay fullyStrengthenedProfile fullyStrengthenedProfile
terminalProfileIsParetoEquivalentToItself =
  equivalent
    (Pareto.paretoRefl fullyStrengthenedProfile)
    (Pareto.paretoRefl fullyStrengthenedProfile)

terminalParetoEquivalenceChartsMid :
  paretoTritKind (kindOf terminalProfileIsParetoEquivalentToItself)
  ≡ Base.tri-mid
terminalParetoEquivalenceChartsMid = refl

------------------------------------------------------------------------
-- 5. Cross-domain boundaries are consumed, not redefined.
------------------------------------------------------------------------

dialecticalJoinBoundary : Dialectic.ProductiveDialecticalFibreJoinBoundary
dialecticalJoinBoundary =
  Dialectic.canonicalProductiveDialecticalFibreJoinBoundary

monsterRepresentationBoundary :
  MonsterBoundary.Spacy369CoverageHyperfabricMonsterBoundary
monsterRepresentationBoundary =
  MonsterBoundary.canonicalSpacy369CoverageHyperfabricMonsterBoundary

data ParetoIncomparabilityAutomaticallyCreatesProductiveDialecticalJoin : Set where

data ParetoResidualProductIsCyclicBase369C6 : Set where

data ParetoTernaryChartCreatesMonsterRepresentation : Set where

paretoIncomparabilityDoesNotAutomaticallyCreateSynthesis :
  ParetoIncomparabilityAutomaticallyCreatesProductiveDialecticalJoin → ⊥
paretoIncomparabilityDoesNotAutomaticallyCreateSynthesis ()

paretoResidualProductIsNotAutomaticallyCyclicC6 :
  ParetoResidualProductIsCyclicBase369C6 → ⊥
paretoResidualProductIsNotAutomaticallyCyclicC6 ()

paretoTernaryChartDoesNotCreateMonsterRepresentation :
  ParetoTernaryChartCreatesMonsterRepresentation → ⊥
paretoTernaryChartDoesNotCreateMonsterRepresentation ()

------------------------------------------------------------------------
-- 6. Capstone boundary.
------------------------------------------------------------------------

record OrderSensitiveParetoTernaryBidiBoundary : Set where
  constructor order-sensitive-pareto-ternary-bidi-boundary
  field
    paretoRelationHasExplicitEquivalentCaseHere : Bool
    ternaryMidCanHideIncomparableOrEquivalent : Bool
    ternaryProjectionRecoversFullParetoKind : Bool
    binaryResidualSeparatesDeclaredMidCollision : Bool
    threeByTwoIsResidualRefinementShapeOnly : Bool
    sameFinalProfileDeterminesRevisionOrder : Bool
    routeOrderCanMatterBeforeFinalReconvergence : Bool
    paretoIncomparabilityGuaranteesDialecticalSynthesis : Bool
    residualProductIsCyclicC6ByCardinality : Bool
    ternaryCoverageCreatesMonsterRepresentation : Bool

canonicalOrderSensitiveParetoTernaryBidiBoundary :
  OrderSensitiveParetoTernaryBidiBoundary
canonicalOrderSensitiveParetoTernaryBidiBoundary =
  order-sensitive-pareto-ternary-bidi-boundary
    true
    true
    false
    true
    true
    false
    true
    false
    false
    false
