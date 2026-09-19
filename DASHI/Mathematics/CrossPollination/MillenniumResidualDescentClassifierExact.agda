module DASHI.Mathematics.CrossPollination.MillenniumResidualDescentClassifierExact where

------------------------------------------------------------------------
-- MILLENNIUM RESIDUAL CLASSIFIER
--
-- The RH observer/descent work exposed four materially different residuals:
--
--   representation/descent
--   missing-information/repair
--   domain theorem
--   coverage
--
-- This owner instantiates that distinction for BSD, Hodge and P-vs-NP.
-- It does not manufacture any Millennium theorem.  Its positive results are:
--
--   * Hodge's conjecture-at-codimension is exactly a cycle-class reopening;
--   * BSD rank equality is exactly a weld between two observations of one curve;
--   * a family of consumer-relevant fibre collisions uniformly blocks every
--     proposed observer in that family, and the obstruction survives arbitrary
--     downstream postcomposition.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge
import DASHI.Mathematics.Arithmetic.BirchSwinnertonDyerBoundary as BSD
import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic

------------------------------------------------------------------------
-- Generic residual classification.
------------------------------------------------------------------------

data ResidualKind : Set where
  representationDescentWall : ResidualKind
  missingInformationRepairWall : ResidualKind
  domainTheoremWall : ResidualKind
  coverageWall : ResidualKind

record FourWayResidualCut : Set where
  constructor four-way-residual-cut
  field
    first second third fourth : ResidualKind

open FourWayResidualCut public

bsdResidualCut : FourWayResidualCut
bsdResidualCut =
  four-way-residual-cut
    representationDescentWall
    domainTheoremWall
    domainTheoremWall
    coverageWall

hodgeResidualCut : FourWayResidualCut
hodgeResidualCut =
  four-way-residual-cut
    representationDescentWall
    missingInformationRepairWall
    representationDescentWall
    coverageWall

pvsnpResidualCut : FourWayResidualCut
pvsnpResidualCut =
  four-way-residual-cut
    representationDescentWall
    missingInformationRepairWall
    domainTheoremWall
    coverageWall

------------------------------------------------------------------------
-- HODGE: cycle class as observer, conjecture as reopening.
------------------------------------------------------------------------

record HodgeCycleClassReopening
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (cycleMap : Hodge.CycleClassMap variety comparison hodge)
    (codimension : Nat) : Set₁ where
  constructor hodge-cycle-class-reopening
  field
    reopen :
      Hodge.RationalHodgeClass hodge codimension →
      Hodge.Cycle cycleMap codimension
    reopeningCorrect :
      (hodgeClass : Hodge.RationalHodgeClass hodge codimension) →
      Hodge.cycleClass cycleMap codimension (reopen hodgeClass)
      ≡ Hodge.hodgeClassValue hodgeClass

open HodgeCycleClassReopening public

hodgeConjectureToCycleClassReopening :
  ∀ {variety comparison hodge cycleMap codimension} →
  Hodge.HodgeConjectureAtCodimension
    {variety = variety}
    {comparison = comparison}
    {hodge = hodge}
    cycleMap codimension →
  HodgeCycleClassReopening cycleMap codimension
hodgeConjectureToCycleClassReopening conjecture =
  hodge-cycle-class-reopening
    (Hodge.everyRationalHodgeClassHasCycle conjecture)
    (Hodge.cycleRepresentsClass conjecture)

cycleClassReopeningToHodgeConjecture :
  ∀ {variety comparison hodge cycleMap codimension} →
  HodgeCycleClassReopening
    {variety = variety}
    {comparison = comparison}
    {hodge = hodge}
    cycleMap codimension →
  Hodge.HodgeConjectureAtCodimension cycleMap codimension
cycleClassReopeningToHodgeConjecture reopening = record
  { everyRationalHodgeClassHasCycle = reopen reopening
  ; cycleRepresentsClass = reopeningCorrect reopening
  }

record HodgeReopeningEquivalence
    {variety : Hodge.SmoothProjectiveComplexVariety}
    {comparison : Hodge.SingularDeRhamComparison variety}
    {hodge : Hodge.HodgeDecomposition variety comparison}
    (cycleMap : Hodge.CycleClassMap variety comparison hodge)
    (codimension : Nat) : Set₁ where
  constructor hodge-reopening-equivalence
  field
    forward :
      Hodge.HodgeConjectureAtCodimension cycleMap codimension →
      HodgeCycleClassReopening cycleMap codimension
    backward :
      HodgeCycleClassReopening cycleMap codimension →
      Hodge.HodgeConjectureAtCodimension cycleMap codimension

hodgeConjectureIsExactlyCycleClassReopening :
  ∀ {variety comparison hodge}
    (cycleMap : Hodge.CycleClassMap variety comparison hodge)
    (codimension : Nat) →
  HodgeReopeningEquivalence cycleMap codimension
hodgeConjectureIsExactlyCycleClassReopening cycleMap codimension =
  hodge-reopening-equivalence
    hodgeConjectureToCycleClassReopening
    cycleClassReopeningToHodgeConjecture

------------------------------------------------------------------------
-- BSD: two observations of the same elliptic curve.
------------------------------------------------------------------------

record BSDRankTwoObserverWeld
    (curve : Elliptic.ShortWeierstrassCurve)
    (mordellWeil : BSD.MordellWeilData curve)
    (lFunction : BSD.EllipticLFunctionData curve) : Set where
  constructor bsd-rank-two-observer-weld
  field
    analyticObservation : Nat
    algebraicObservation : Nat
    analyticObservationIsRank :
      analyticObservation ≡ BSD.analyticRank lFunction
    algebraicObservationIsRank :
      algebraicObservation ≡ BSD.freeRank mordellWeil
    observationsAgree :
      analyticObservation ≡ algebraicObservation

open BSDRankTwoObserverWeld public

bsdRankConjectureToTwoObserverWeld :
  ∀ {curve mordellWeil lFunction} →
  BSD.BSDRankConjecture curve mordellWeil lFunction →
  BSDRankTwoObserverWeld curve mordellWeil lFunction
bsdRankConjectureToTwoObserverWeld conjecture =
  bsd-rank-two-observer-weld
    (BSD.analyticRank _)
    (BSD.freeRank _)
    refl
    refl
    (BSD.analyticRankEqualsAlgebraicRank conjecture)

twoObserverWeldToBSDRankConjecture :
  ∀ {curve mordellWeil lFunction} →
  BSDRankTwoObserverWeld curve mordellWeil lFunction →
  BSD.BSDRankConjecture curve mordellWeil lFunction
twoObserverWeldToBSDRankConjecture weld = record
  { analyticRankEqualsAlgebraicRank =
      trans
        (sym (analyticObservationIsRank weld))
        (trans
          (observationsAgree weld)
          (algebraicObservationIsRank weld))
  }

------------------------------------------------------------------------
-- P-VS-NP: generic uniform non-descent obstruction grammar.
------------------------------------------------------------------------

record UniformObserverNonDescent
    {State Surface Outcome Candidate : Set}
    (observe : Candidate → State → Surface)
    (consumer : State → Outcome) : Set₁ where
  constructor uniform-observer-non-descent
  field
    collisionFor :
      (candidate : Candidate) →
      Descent.ConsumerNonDescentWitness
        (observe candidate)
        consumer

open UniformObserverNonDescent public

uniformNonDescentBlocksEveryCandidate :
  ∀ {State Surface Outcome Candidate}
    {observe : Candidate → State → Surface}
    {consumer : State → Outcome} →
  UniformObserverNonDescent observe consumer →
  (candidate : Candidate) →
  Descent.FactorsThrough (observe candidate) consumer →
  ⊥
uniformNonDescentBlocksEveryCandidate obstruction candidate =
  Descent.nonDescentWitnessBlocksFactorization
    (collisionFor obstruction candidate)

postcomposeNonDescentWitness :
  ∀ {State Surface Recharted Outcome}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  Descent.ConsumerNonDescentWitness observe consumer →
  (rechart : Surface → Recharted) →
  Descent.ConsumerNonDescentWitness
    (λ state → rechart (observe state))
    consumer
postcomposeNonDescentWitness witness rechart =
  Descent.consumerNonDescentWitness
    (Descent.left witness)
    (Descent.right witness)
    (cong rechart (Descent.sameSurface witness))
    (Descent.differentOutcome witness)

postcompositionCannotRepairNonDescent :
  ∀ {State Surface Recharted Outcome}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  Descent.ConsumerNonDescentWitness observe consumer →
  (rechart : Surface → Recharted) →
  Descent.FactorsThrough
    (λ state → rechart (observe state))
    consumer →
  ⊥
postcompositionCannotRepairNonDescent witness rechart =
  Descent.nonDescentWitnessBlocksFactorization
    (postcomposeNonDescentWitness witness rechart)

record PvsNPUniformNonDescentResearchBoundary : Set where
  constructor pvsnp-uniform-non-descent-research-boundary
  field
    consumerRelativeCollisionGrammarAvailable : Bool
    obstructionSurvivesPostcomposition : Bool
    candidateFamilyCoverageOfAllPolynomialAlgorithmsPaid : Bool
    npCompleteUniformObstructionPaid : Bool
    pNotEqualsNPDerived : Bool

open PvsNPUniformNonDescentResearchBoundary public

canonicalPvsNPUniformNonDescentResearchBoundary :
  PvsNPUniformNonDescentResearchBoundary
canonicalPvsNPUniformNonDescentResearchBoundary =
  pvsnp-uniform-non-descent-research-boundary
    true true false false false

------------------------------------------------------------------------
-- Shared anti-promotion boundary.
------------------------------------------------------------------------

record MillenniumResidualClassifierBoundary : Set where
  constructor millennium-residual-classifier-boundary
  field
    hodgeConjectureRecognizedAsReopening : Bool
    bsdRankConjectureRecognizedAsTwoObserverWeld : Bool
    uniformNonDescentGrammarAvailable : Bool
    postcompositionCannotRestoreErasedInformation : Bool

    hodgeAlgebraicLiftConstructed : Bool
    bsdRankWeldConstructedUnconditionally : Bool
    polynomialAlgorithmFamilyExhaustionConstructed : Bool
    anyOfThreeMillenniumProblemsSolvedHere : Bool

open MillenniumResidualClassifierBoundary public

canonicalMillenniumResidualClassifierBoundary :
  MillenniumResidualClassifierBoundary
canonicalMillenniumResidualClassifierBoundary =
  millennium-residual-classifier-boundary
    true true true true
    false false false false
