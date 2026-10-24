{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravityP1A2OpenLemmaASTExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.ExoticGravity.AntigravityP1A2CertifiedStressCylinderExact as CertifiedA2
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE2PinnedOSAlgebraExact as E2
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact as R110
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119Round109ConcreteLocalCExact as Round109
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119WilsonSourceOS2Exact as WilsonSource
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem

------------------------------------------------------------------------
-- A2 OPEN LEMMA: EXACT SAME-OBJECT STATEMENT
--
-- The current A2 source-semantic obligation is exactly
--
--   evaluator (selected Round109 stress pair)
--     = canonical Local-C encoded stress-cylinder observable
--
-- as equality of Configuration -> R functions.
--
-- The bare Round109 pair does not determine the evaluator.  Therefore the
-- evaluator is syntax/data in the open lemma AST, while the same-object
-- equality is a separate solution type.  Constructing the AST cannot by itself
-- discharge the lemma.
------------------------------------------------------------------------

module _
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
    (provenance : R110.LiteralStressSameObjectProvenance Y group)
    (round109 : Round109.Round109ConcreteLocalCStressWeld Y group localC)
    (completionMatches :
      R110.markedCompletion provenance ≡ Round109.completion round109)
    (stressEncoding :
      E2.PinnedLocalCStressCylinderEmbedding
        {C = C} {S = S} Y group
        {G = G} {X = X} {Configuration = Configuration}
        {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector}
        {Hamiltonian = Hamiltonian} {Algebra = Algebra}
        {Scale = Scale} {Volume = Volume} {Root = Root}
        {ContinuumFamily = ContinuumFamily} {Core = Core}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division}
        {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
        localC)
    (wilsonApplication :
      WilsonSource.LiteralCMP119WilsonRPApplication
        Configuration
        (OSSystem.family osInputs group)
        (OSSystem.observableAlgebra osInputs))
  where

  Pair : Set
  Pair =
    Source.SourceNativeOrdinaryCharacteristicPair
      (R109.source (R110.sourceCauchy provenance))

  Observable : Set
  Observable = Configuration → ℝ

  selectedRound109Pair : Pair
  selectedRound109Pair =
    R109.stressInsertion (R110.sourceCauchy provenance)

  canonicalLocalCStressObservable : Observable
  canonicalLocalCStressObservable =
    E2.encodeStress stressEncoding (LocalC.stressTensor localC)

  A2SelectedPairCanonicalLocalCStressLemma :
    (ordinaryObservableOfPair : Pair → Observable) → Set
  A2SelectedPairCanonicalLocalCStressLemma ordinaryObservableOfPair =
    ordinaryObservableOfPair selectedRound109Pair
      ≡ canonicalLocalCStressObservable

  ----------------------------------------------------------------------
  -- Exact typed AST.
  ----------------------------------------------------------------------

  data A2Sort : Set where
    pairSort : A2Sort
    observableSort : A2Sort

  A2Denotation : A2Sort → Set
  A2Denotation pairSort = Pair
  A2Denotation observableSort = Observable

  data A2Term : A2Sort → Set where
    selectedPairTerm : A2Term pairSort
    canonicalStressTerm : A2Term observableSort
    evaluatePairTerm :
      (Pair → Observable) →
      A2Term pairSort →
      A2Term observableSort

  denoteA2Term :
    {sort : A2Sort} → A2Term sort → A2Denotation sort
  denoteA2Term selectedPairTerm = selectedRound109Pair
  denoteA2Term canonicalStressTerm = canonicalLocalCStressObservable
  denoteA2Term (evaluatePairTerm evaluator pairTerm) =
    evaluator (denoteA2Term pairTerm)

  record A2OpenLemmaAST : Set where
    constructor a2-open-lemma-ast
    field
      ordinaryObservableOfPair : Pair → Observable

  open A2OpenLemmaAST public

  lhsTerm : A2OpenLemmaAST → A2Term observableSort
  lhsTerm ast =
    evaluatePairTerm (ordinaryObservableOfPair ast) selectedPairTerm

  rhsTerm : A2OpenLemmaAST → A2Term observableSort
  rhsTerm ast = canonicalStressTerm

  A2LemmaGoal : A2OpenLemmaAST → Set
  A2LemmaGoal ast =
    denoteA2Term (lhsTerm ast) ≡ denoteA2Term (rhsTerm ast)

  A2LemmaSolution : A2OpenLemmaAST → Set
  A2LemmaSolution = A2LemmaGoal

  canonicalOpenLemmaAST :
    (Pair → Observable) → A2OpenLemmaAST
  canonicalOpenLemmaAST evaluator =
    a2-open-lemma-ast evaluator

  openLemmaGoalIsKeyLemma :
    (ast : A2OpenLemmaAST) →
    A2LemmaGoal ast
      ≡ A2SelectedPairCanonicalLocalCStressLemma
          (ordinaryObservableOfPair ast)
  openLemmaGoalIsKeyLemma ast = refl

  ----------------------------------------------------------------------
  -- Solved AST compiles directly to the already-owned certified A2 witness.
  ----------------------------------------------------------------------

  compileSolvedA2AST :
    (ast : A2OpenLemmaAST) →
    A2LemmaSolution ast →
    CertifiedA2.CertifiedA2PairObservableSemantics
      Y group localC provenance round109 completionMatches
      stressEncoding wilsonApplication
  compileSolvedA2AST ast solution = record
    { ordinaryObservableOfPair = ordinaryObservableOfPair ast
    ; selectedPairImageIsCanonicalLocalCStressObservable = solution
    }

------------------------------------------------------------------------
-- LEAST-PRIVILEGE INVARIANT BOUNDS
--
-- A2 remains ONE source-semantic package.  Internally it has exactly TWO
-- unproved pieces: source semantics for the evaluator, and the selected-image
-- same-object equality.  The lemma constrains no non-selected pair image and
-- requires no injectivity/surjectivity/global semantics from the evaluator.
-- Positive-time and gauge admissibility compile after the selected equality;
-- clustering and downstream covariance are already supplied elsewhere.
------------------------------------------------------------------------

a2SourceSemanticPackageCount : Nat
a2SourceSemanticPackageCount = 1

a2InternalOpenInvariantCount : Nat
a2InternalOpenInvariantCount = 2

evaluatorSourceSemanticsStillOpen : Bool
evaluatorSourceSemanticsStillOpen = true

selectedPairSameObjectEqualityStillOpen : Bool
selectedPairSameObjectEqualityStillOpen = true

nonSelectedPairImagesConstrainedByA2 : Bool
nonSelectedPairImagesConstrainedByA2 = false

evaluatorInjectivityRequired : Bool
evaluatorInjectivityRequired = false

evaluatorSurjectivityRequired : Bool
evaluatorSurjectivityRequired = false

allPairSemanticsRequired : Bool
allPairSemanticsRequired = false

positiveTimeSeparatelyOpen : Bool
positiveTimeSeparatelyOpen = false

gaugeInvarianceSeparatelyOpen : Bool
gaugeInvarianceSeparatelyOpen = false

clusteringSeparatelyOpen : Bool
clusteringSeparatelyOpen = false

downstreamCovarianceSeparatelyOpen : Bool
downstreamCovarianceSeparatelyOpen = false

q1PresentCutPathSemanticsDischargedByA2 : Bool
q1PresentCutPathSemanticsDischargedByA2 = false

record A2InvariantBounds : Set where
  constructor a2-invariant-bounds
  field
    sourcePackageCount : Nat
    internalOpenInvariantCount : Nat
    evaluatorSourceSemanticsOpen : Bool
    selectedSameObjectEqualityOpen : Bool
    nonSelectedImagesConstrained : Bool
    injectivityRequired : Bool
    surjectivityRequired : Bool
    globalPairSemanticsRequired : Bool
    positiveTimeOpen : Bool
    gaugeInvarianceOpen : Bool
    clusteringOpen : Bool
    downstreamCovarianceOpen : Bool
    q1DischargedByA2 : Bool

canonicalA2InvariantBounds : A2InvariantBounds
canonicalA2InvariantBounds =
  a2-invariant-bounds
    1 2 true true false false false false false false false false false
