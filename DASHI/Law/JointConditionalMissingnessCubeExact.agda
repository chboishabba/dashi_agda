module DASHI.Law.JointConditionalMissingnessCubeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as NF

------------------------------------------------------------------------
-- Joint conditional missingness cube.
------------------------------------------------------------------------

data OutcomeAxis : Set where searchYes searchNo : OutcomeAxis
data OfficerAxis : Set where officerA officerB : OfficerAxis
data PlaceAxis : Set where placeA placeB : PlaceAxis
data DeploymentAxis : Set where deploymentA deploymentB : DeploymentAxis
data GroupAxis : Set where groupA groupB : GroupAxis

record JointCell : Set where
  constructor jointCell
  field
    outcome : OutcomeAxis
    officer : OfficerAxis
    place : PlaceAxis
    deployment : DeploymentAxis
    group : GroupAxis
    observedCount : ℕ
    missingCount : ℕ
    cellReference : String

open JointCell public

------------------------------------------------------------------------
-- Two populations with identical one-axis marginal crosstabs but different
-- officer×outcome interaction structure.
------------------------------------------------------------------------

data InteractionPattern : Set where
  missingOnOfficerAWhenSearched
  missingOnOfficerAWhenNotSearched : InteractionPattern

record InteractionPopulation : Set where
  constructor interactionPopulation
  field
    officerAMissing : ℕ
    officerBMissing : ℕ
    searchedMissing : ℕ
    nonSearchedMissing : ℕ
    jointA searchedA nonSearchedA jointB searchedB nonSearchedB : ℕ
    interactionPattern : InteractionPattern
    populationReference : String

open InteractionPopulation public

populationSearchConcentrated : InteractionPopulation
populationSearchConcentrated = interactionPopulation
  2 2 2 2
  2 2 0 2 0 2
  missingOnOfficerAWhenSearched
  "synthetic population: officer A missingness concentrated in searched cells"

populationNonSearchConcentrated : InteractionPopulation
populationNonSearchConcentrated = interactionPopulation
  2 2 2 2
  2 0 2 2 2 0
  missingOnOfficerAWhenNotSearched
  "synthetic population: same officer/outcome margins, opposite interaction concentration"

record OneAxisMissingnessProjection : Set where
  constructor oneAxisMissingnessProjection
  field
    officerAMargin officerBMargin : ℕ
    searchedMargin nonSearchedMargin : ℕ

open OneAxisMissingnessProjection public

oneAxisProjection : InteractionPopulation → OneAxisMissingnessProjection
oneAxisProjection p = oneAxisMissingnessProjection
  (officerAMissing p) (officerBMissing p)
  (searchedMissing p) (nonSearchedMissing p)

interactionProjection : InteractionPopulation → InteractionPattern
interactionProjection = interactionPattern

sameOneAxisProjection :
  oneAxisProjection populationSearchConcentrated ≡
  oneAxisProjection populationNonSearchConcentrated
sameOneAxisProjection = refl

interactionPatternsDiffer :
  interactionProjection populationSearchConcentrated ≡
  interactionProjection populationNonSearchConcentrated → ⊥
interactionPatternsDiffer ()

separateOneAxisCrosstabsNonFactorability :
  NF.NonFactorabilityWitness oneAxisProjection interactionProjection
separateOneAxisCrosstabsNonFactorability = NF.nonFactorabilityWitness
  populationSearchConcentrated
  populationNonSearchConcentrated
  sameOneAxisProjection
  interactionPatternsDiffer

separateOneAxisCrosstabsCannotRecoverJointInteraction :
  NF.FactorsThrough oneAxisProjection interactionProjection → ⊥
separateOneAxisCrosstabsCannotRecoverJointInteraction =
  NF.witnessRulesOutEveryFlatFactorisation separateOneAxisCrosstabsNonFactorability

separateCrosstabRechartCannotRecoverInteraction :
  ∀ {Recharted : Set} →
  (rechart : OneAxisMissingnessProjection → Recharted) →
  NF.FactorsThrough
    (λ p → rechart (oneAxisProjection p))
    interactionProjection → ⊥
separateCrosstabRechartCannotRecoverInteraction rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart separateOneAxisCrosstabsNonFactorability

------------------------------------------------------------------------
-- BIDI for joint interaction claims.
------------------------------------------------------------------------

data JointMissingnessClaim : Set where
  officerMarginal
  outcomeMarginal
  officerOutcomeInteraction
  fullJointConditionalMechanism : JointMissingnessClaim

data JointMissingnessProducer : Set where
  officerCrossTabProducer
  outcomeCrossTabProducer
  officerOutcomeJointTableProducer
  fullJointCubeProducer : JointMissingnessProducer

reverseJointMissingness : JointMissingnessClaim → JointMissingnessProducer
reverseJointMissingness officerMarginal = officerCrossTabProducer
reverseJointMissingness outcomeMarginal = outcomeCrossTabProducer
reverseJointMissingness officerOutcomeInteraction = officerOutcomeJointTableProducer
reverseJointMissingness fullJointConditionalMechanism = fullJointCubeProducer

record JointMissingnessCutset : Set where
  constructor jointMissingnessCutset
  field
    officerMarginClosed : Bool
    outcomeMarginClosed : Bool
    officerOutcomeJointClosed : Bool
    fullCubeClosed : Bool
    cutsetReference : String

open JointMissingnessCutset public

data JointMissingnessResidual : Set where
  officerMarginResidual outcomeMarginResidual officerOutcomeJointResidual fullCubeResidual jointMissingnessClosed : JointMissingnessResidual

firstJointResidual : JointMissingnessClaim → JointMissingnessCutset → JointMissingnessResidual
firstJointResidual officerMarginal c with officerMarginClosed c
... | false = officerMarginResidual
... | true = jointMissingnessClosed
firstJointResidual outcomeMarginal c with outcomeMarginClosed c
... | false = outcomeMarginResidual
... | true = jointMissingnessClosed
firstJointResidual officerOutcomeInteraction c with officerMarginClosed c
... | false = officerMarginResidual
... | true with outcomeMarginClosed c
...   | false = outcomeMarginResidual
...   | true with officerOutcomeJointClosed c
...     | false = officerOutcomeJointResidual
...     | true = jointMissingnessClosed
firstJointResidual fullJointConditionalMechanism c with officerOutcomeJointClosed c
... | false = officerOutcomeJointResidual
... | true with fullCubeClosed c
...   | false = fullCubeResidual
...   | true = jointMissingnessClosed

canonicalMarginsOnly : JointMissingnessCutset
canonicalMarginsOnly = jointMissingnessCutset true true false false
  "officer and outcome margins closed; joint interaction table still open"

marginsDoNotCloseInteraction :
  firstJointResidual officerOutcomeInteraction canonicalMarginsOnly ≡ officerOutcomeJointResidual
marginsDoNotCloseInteraction = refl

fullCubeNeedsMoreThanPairwiseJointTable :
  firstJointResidual fullJointConditionalMechanism
    (jointMissingnessCutset true true true false "pairwise officer×outcome table closed; full cube open")
  ≡ fullCubeResidual
fullCubeNeedsMoreThanPairwiseJointTable = refl

record JointConditionalMissingnessBoundary : Set where
  constructor jointConditionalMissingnessBoundary
  field
    oneAxisMarginsDetermineInteraction : Bool
    oneAxisMarginsDetermineInteractionIsFalse : oneAxisMarginsDetermineInteraction ≡ false
    pairwiseInteractionDeterminesFullCube : Bool
    pairwiseInteractionDeterminesFullCubeIsFalse : pairwiseInteractionDeterminesFullCube ≡ false

canonicalJointConditionalBoundary : JointConditionalMissingnessBoundary
canonicalJointConditionalBoundary = jointConditionalMissingnessBoundary false refl false refl
