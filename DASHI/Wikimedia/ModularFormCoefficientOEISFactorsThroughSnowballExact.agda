module DASHI.Wikimedia.ModularFormCoefficientOEISFactorsThroughSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimJMathematicsNumberOEISSecondOrderQidSnowballExact as Second
import DASHI.Wikimedia.IbrahimBase369JOEISMoonshineSnowballExact as JOEIS
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs
import DASHI.Physics.Closure.TriadicModularAutomorphicGate as ModularGate
import DASHI.Moonshine.JCoefficientCharacterBridge as JCoeff
import DASHI.Moonshine.MonsterGradedVOABridgeExact as MonsterVOA

------------------------------------------------------------------------
-- MODULAR FORM / COEFFICIENT SEQUENCE / OEIS FACTORISATION SNOWBALL
--
-- Q870797 supplies external identity only.  The repository's theorem-bearing
-- modular promotion surface is ModularTransformationGate: transformation law,
-- parameter domain, automorphy factor, weight, level and coefficient agreement
-- are all separate obligations.  Therefore a coefficient sequence is a useful
-- projection of a modular object, but is not in general a sufficient observer
-- for the whole modular-form consumer.
------------------------------------------------------------------------

modularFormIdentity : Identity.ExternalIdentityDemand
modularFormIdentity = Second.modularFormQid

record ModularFormObservationAxes : Set where
  constructor modular-form-observation-axes
  field
    coefficientSequence : Bool
    parameterDomain : Bool
    transformationLaw : Bool
    automorphyFactor : Bool
    weight : Bool
    level : Bool
    characterOrMultiplier : Bool
    holomorphyOrMeromorphy : Bool
    cuspGrowthOrPoleData : Bool
    normalization : Bool
    provenance : Bool
open ModularFormObservationAxes public

canonicalModularFormAxes : ModularFormObservationAxes
canonicalModularFormAxes = modular-form-observation-axes
  true true true true true true true true true true true

------------------------------------------------------------------------
-- Consumer-indexed FactorsThrough candidates.
------------------------------------------------------------------------

data ModularConsumer : Set where
  exactCoefficientAtIndex fullCoefficientStream modularIdentity
  transformationBehaviour heckeEigenBehaviour moonshineFirstCoefficient
  fullModularObject : ModularConsumer

record CoefficientFactorsThroughCandidate : Set where
  constructor coefficient-factors-through-candidate
  field
    consumer : ModularConsumer
    observer : String
    factorsThroughObserver : Bool
    omittedAxes : String
    failedFactorisationMaySnowball : Bool
open CoefficientFactorsThroughCandidate public

coefficientAtIndexThroughSequence : CoefficientFactorsThroughCandidate
coefficientAtIndexThroughSequence = coefficient-factors-through-candidate
  exactCoefficientAtIndex
  "coefficient sequence indexed by n"
  true
  "none for the coefficient-at-index query once same-series identity/revision is fixed"
  false

fullStreamThroughSequence : CoefficientFactorsThroughCandidate
fullStreamThroughSequence = coefficient-factors-through-candidate
  fullCoefficientStream
  "complete ordered coefficient sequence"
  true
  "source/revision still required for same-object attribution"
  false

modularIdentityThroughCoefficientsAlone : CoefficientFactorsThroughCandidate
modularIdentityThroughCoefficientsAlone = coefficient-factors-through-candidate
  modularIdentity
  "coefficient sequence alone"
  false
  "parameter domain; transformation law; automorphy factor; weight/level/character; analytic conditions; normalization; provenance"
  true

transformationThroughCoefficientsAlone : CoefficientFactorsThroughCandidate
transformationThroughCoefficientsAlone = coefficient-factors-through-candidate
  transformationBehaviour
  "coefficient sequence alone"
  false
  "group action/domain/action law and automorphy factor"
  true

heckeThroughCoefficientsAlone : CoefficientFactorsThroughCandidate
heckeThroughCoefficientsAlone = coefficient-factors-through-candidate
  heckeEigenBehaviour
  "coefficient sequence alone"
  false
  "Hecke operator action, simultaneous eigen receipt and commuting-operator structure"
  true

fullObjectThroughModularGate : CoefficientFactorsThroughCandidate
fullObjectThroughModularGate = coefficient-factors-through-candidate
  fullModularObject
  "ModularTransformationGate plus coefficient agreement and source identity"
  true
  "higher structures such as Eisenstein basis, Hecke eigensystem, VOA or genus-zero remain separate consumers"
  false

------------------------------------------------------------------------
-- Existing J / Monster coefficient seam retained without overpromotion.
------------------------------------------------------------------------

firstMoonshineCoefficientOEIS : JOEIS.OEISCoordinate
firstMoonshineCoefficientOEIS = JOEIS.jCoefficientOEIS

monsterDegreeOEIS : JOEIS.OEISCoordinate
monsterDegreeOEIS = JOEIS.monsterRepresentationOEIS

record MoonshineCoefficientProjection : Set where
  constructor moonshine-coefficient-projection
  field
    jCoefficient196884Paid : Bool
    monsterDegree196883Paid : Bool
    arithmeticPlusOnePaid : Bool
    gradedTraceBridgeExists : Bool
    voaConstructionPaidByArithmetic : Bool
    modularityPaidByArithmetic : Bool
    genusZeroPaidByArithmetic : Bool
open MoonshineCoefficientProjection public

currentMoonshineCoefficientProjection : MoonshineCoefficientProjection
currentMoonshineCoefficientProjection = moonshine-coefficient-projection
  true true true true false false false

firstCoefficientArithmetic : 196884 ≡ 1 + 196883
firstCoefficientArithmetic = JCoeff.firstCoefficientArithmetic

------------------------------------------------------------------------
-- Promotion ladder: coefficient evidence can survive all-pairs comparison,
-- but promotion to modular structure requires the theorem-bearing gate.
------------------------------------------------------------------------

data PromotionStage : Set where
  externalSequenceIdentity exactCoefficientAgreement qSeriesCandidate
  modularTransformationPaid eisensteinBasisPaid heckeEigenPaid
  gradedVOAPaid moonshineModularityPaid genusZeroPaid : PromotionStage

record PromotionEdge : Set where
  constructor promotion-edge
  field
    from : PromotionStage
    to : PromotionStage
    automatic : Bool
    missingReceipt : String
open PromotionEdge public

sequenceToCoefficient : PromotionEdge
sequenceToCoefficient = promotion-edge externalSequenceIdentity exactCoefficientAgreement false
  "same-object source/revision/index agreement"

coefficientToQSeries : PromotionEdge
coefficientToQSeries = promotion-edge exactCoefficientAgreement qSeriesCandidate false
  "ordered complete coefficient carrier plus q-variable/normalization convention"

qSeriesToModular : PromotionEdge
qSeriesToModular = promotion-edge qSeriesCandidate modularTransformationPaid false
  "ModularTransformationGate: domain, group action, automorphy factor, weight, level, transformation law, coefficient agreement"

modularToHecke : PromotionEdge
modularToHecke = promotion-edge modularTransformationPaid heckeEigenPaid false
  "Hecke probe tracks the same modular sector plus simultaneous-eigen and commuting-operator receipts"

modularToMoonshine : PromotionEdge
modularToMoonshine = promotion-edge modularTransformationPaid moonshineModularityPaid false
  "same graded VOA/Monster action and McKay-Thompson modularity receipts"

moonshineToGenusZero : PromotionEdge
moonshineToGenusZero = promotion-edge moonshineModularityPaid genusZeroPaid false
  "genus-zero/Hauptmodul theorem"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameCoefficientSequenceCreatesSameModularObject : Set where
data OEISSequenceCreatesModularTransformationLaw : Set where
data FirstCoefficientCreatesMoonshineTheorem : Set where
data ModularityCreatesGenusZeroAutomatically : Set where
data QidCreatesTransformationLaw : Set where

coefficientsDoNotCreateWholeModularObject : SameCoefficientSequenceCreatesSameModularObject → ⊥
coefficientsDoNotCreateWholeModularObject ()

oeisDoesNotCreateTransformationLaw : OEISSequenceCreatesModularTransformationLaw → ⊥
oeisDoesNotCreateTransformationLaw ()

firstCoefficientDoesNotCreateMoonshine : FirstCoefficientCreatesMoonshineTheorem → ⊥
firstCoefficientDoesNotCreateMoonshine ()

modularityDoesNotCreateGenusZero : ModularityCreatesGenusZeroAutomatically → ⊥
modularityDoesNotCreateGenusZero ()

qidDoesNotCreateTransformationLaw : QidCreatesTransformationLaw → ⊥
qidDoesNotCreateTransformationLaw ()

modularPromotionStatement : String
modularPromotionStatement = ModularGate.modularGateStatement

monsterCoefficientArithmeticDoesNotCloseMoonshine : Bool
monsterCoefficientArithmeticDoesNotCloseMoonshine = true

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary
