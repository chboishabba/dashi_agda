module DASHI.Analysis.DeBruijnNewmanRiemannG2RiemannSiegelBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleG2CurrentCutExact as G2
import DASHI.Analysis.RiemannAristotleFiniteNearReflectionOrbitReturnExact as Near
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

------------------------------------------------------------------------
-- POLYMATH THEOREM 1.3 -> RH G2 SOURCE-EXACT AUDIT
--
-- External mathematical source for the Polymath statements only:
--   D. H. J. Polymath,
--   "Effective approximation of heat flow evolution of the Riemann xi
--   function, and a new upper bound for the de Bruijn-Newman constant",
--   Research in the Mathematical Sciences 6 (2019),
--   DOI 10.1007/s40687-019-0193-1, arXiv:1904.12438.
--
-- Theorem 1.3 is an effective Riemann--Siegel approximation to H_t(x+iy).
-- The proof culminates in equations (69)--(74): H_t/B_t is represented by the
-- finite expression f_t (or f_t-C_t/B_t) with explicit e_A,e_B,e_C/e_C,0
-- error budgets.  Section 7 then uses this finite expression for repeated
-- evaluations in the barrier verification.
--
-- This module does NOT attribute the bridge audit below to Polymath.  The
-- comparison with DASHI's current G2 zero-sum consumer is repository-native.
------------------------------------------------------------------------

data Polymath13Carrier : Set where
  heatFlowPoint : Polymath13Carrier
  finiteDirichletPolynomial : Polymath13Carrier
  explicitApproximationError : Polymath13Carrier

data G2Carrier : Set where
  zetaZeroNearCarrier : G2Carrier
  reflectionPairedZeroKernel : G2Carrier
  targetCenteredWeightedZeroIntegral : G2Carrier

data IndexLanguage : Set where
  positiveIntegerIndex : IndexLanguage
  zetaZeroIndex : IndexLanguage

data PhaseLanguage : Set where
  dirichletLogarithmicPhase : PhaseLanguage
  targetCenteredZeroOrdinatePhase : PhaseLanguage

data WeightLanguage : Set where
  polymathBtBnGammaWeights : WeightLanguage
  g2TaperCoshWeights : WeightLanguage

polymathIndexLanguage : IndexLanguage
polymathIndexLanguage = positiveIntegerIndex

g2IndexLanguage : IndexLanguage
g2IndexLanguage = zetaZeroIndex

indexLanguagesDiffer : polymathIndexLanguage ≡ g2IndexLanguage → ⊥
indexLanguagesDiffer ()

polymathPhaseLanguage : PhaseLanguage
polymathPhaseLanguage = dirichletLogarithmicPhase

g2PhaseLanguage : PhaseLanguage
g2PhaseLanguage = targetCenteredZeroOrdinatePhase

phaseLanguagesDiffer : polymathPhaseLanguage ≡ g2PhaseLanguage → ⊥
phaseLanguagesDiffer ()

polymathWeightLanguage : WeightLanguage
polymathWeightLanguage = polymathBtBnGammaWeights

g2WeightLanguage : WeightLanguage
g2WeightLanguage = g2TaperCoshWeights

weightLanguagesDiffer : polymathWeightLanguage ≡ g2WeightLanguage → ⊥
weightLanguagesDiffer ()

------------------------------------------------------------------------
-- Source-exact theorem surfaces recovered from Polymath.
------------------------------------------------------------------------

data Polymath13Surface : Set where
  effectiveHtOverBtApproximation : Polymath13Surface
  finiteFtEvaluationSurface : Polymath13Surface
  explicitEAEBECBudget : Polymath13Surface
  barrierEvaluationConsumer : Polymath13Surface

polymath13Reference : String
polymath13Reference =
  "Polymath 2019 Theorem 1.3 and equations (69)-(74): H_t(x+iy)/B_t(x+iy) is approximated by finite f_t with explicit e_A,e_B,e_C/e_C0 error; Section 7 uses f_t for barrier evaluation."

------------------------------------------------------------------------
-- Literal G2 consumer surfaces.
------------------------------------------------------------------------

g2ConsumerReference : String
g2ConsumerReference =
  G2.firstUnprovedHarmonicAnalysisTheorem G2.canonicalAristotleG2CurrentCut

nearCarrierReflectionStable :
  Near.finiteNearCarrierReflectionStableBySource Near.canonicalFiniteNearReflectionOrbitReturn
  ≡ true
nearCarrierReflectionStable =
  Near.finiteNearCarrierReflectionStableBySourceIsTrue
    Near.canonicalFiniteNearReflectionOrbitReturn

nearSummandAlreadyReflectionPaired :
  Near.nearSummandAlreadyReflectionPaired Near.canonicalFiniteNearReflectionOrbitReturn
  ≡ true
nearSummandAlreadyReflectionPaired =
  Near.nearSummandAlreadyReflectionPairedIsTrue
    Near.canonicalFiniteNearReflectionOrbitReturn

------------------------------------------------------------------------
-- What would be required for genuine theorem-bearing transport.
--
-- The Polymath finite n-sum evaluates H_t itself.  G2 consumes a finite sum over
-- zeta zeros sigma in nearOffFinset(t,J), after reflection pairing, inside a
-- q(u)-weighted integral with cosh(a_sigma u) cos((b_sigma-t)u).
--
-- A genuine bridge therefore needs an explicit theorem converting the H_t
-- evaluation language to THAT zero-indexed weighted consumer.  Similarity of
-- oscillation, the common xi/zeta ancestry, or a shared real parameter named t
-- is not enough.
------------------------------------------------------------------------

record RiemannSiegelToG2BridgeReceipt : Set₁ where
  constructor riemannSiegelToG2BridgeReceipt
  field
    exactH0XiCoordinateIdentification : Set
    integerSumToZeroCarrierTransform : Set
    targetCenterCoordinateCompatibility : Set
    nearOffFinsetCutoffCompatibility : Set
    reflectionPairCompatibility : Set
    taperWeightTransport : Set
    explicitErrorFitsG2Budget : Set
    exactTargetConsumerEquality : Set

open RiemannSiegelToG2BridgeReceipt public

-- No constructor is supplied from Theorem 1.3 alone.

data BridgeStage : Set where
  sourceTheoremRecovered
  carrierComparisonCompleted
  exactTransformRecovered
  g2BudgetDischarged
  theoremBearingBridge
  : BridgeStage

currentBridgeStage : BridgeStage
currentBridgeStage = carrierComparisonCompleted

sourceTheoremAloneNotTheoremBridge :
  sourceTheoremRecovered ≡ theoremBearingBridge → ⊥
sourceTheoremAloneNotTheoremBridge ()

carrierComparisonAloneNotTheoremBridge :
  carrierComparisonCompleted ≡ theoremBearingBridge → ⊥
carrierComparisonAloneNotTheoremBridge ()

------------------------------------------------------------------------
-- Strength classification after the term-for-term comparison.
------------------------------------------------------------------------

currentPolymath13ToG2Relation : Relation.RelationKind
currentPolymath13ToG2Relation = Relation.sharedAnalyticProblemDomain

currentPolymath13ToG2Reuse : Relation.ReuseCapability currentPolymath13ToG2Relation
currentPolymath13ToG2Reuse = Relation.reuseSharedDomainForSourceSearch

polymath13DirectlyClosesG2 : Bool
polymath13DirectlyClosesG2 = false

exactIntegerSumToZeroSumTransformRecovered : Bool
exactIntegerSumToZeroSumTransformRecovered = false

exactG2TaperTransportRecovered : Bool
exactG2TaperTransportRecovered = false

polymath13ErrorBudgetDischargesG2Consumer : Bool
polymath13ErrorBudgetDischargesG2Consumer = false

polymath13DirectlyClosesG2IsFalse : polymath13DirectlyClosesG2 ≡ false
polymath13DirectlyClosesG2IsFalse = refl

exactIntegerSumToZeroSumTransformRecoveredIsFalse :
  exactIntegerSumToZeroSumTransformRecovered ≡ false
exactIntegerSumToZeroSumTransformRecoveredIsFalse = refl

------------------------------------------------------------------------
-- Important positive result of the audit.
--
-- Theorem 1.3 IS directly relevant to DBN certificate replay: it turns a large
-- class of H_t evaluations into finite sums plus explicit source-owned errors.
-- Thus its strongest present cross-pollination is exact finite-certificate
-- interpretation for DBN, while its relation to the current G2 zero-sum leaf
-- remains source-search strength until the missing transform is constructed.
------------------------------------------------------------------------

data PresentUse : Set where
  dbnFiniteEvaluationInterpretation
  rhSourceSearchGuide
  directG2Lemma
  : PresentUse

highestJustifiedPresentUse : PresentUse
highestJustifiedPresentUse = dbnFiniteEvaluationInterpretation

------------------------------------------------------------------------
-- Highest-alpha RH continuation after this audit.
--
-- Do not re-run Theorem 1.3 as though it already estimated nearOffFinset.
-- Search instead for an explicit-formula / Hadamard / log-derivative bridge
-- that converts finite H_0/xi information into the SAME target-centred zero
-- carrier and q-weighted integral required by G2.  Only such a bridge can
-- upgrade shared-domain relation to exact lemma-consumer relation.
------------------------------------------------------------------------

record NextExactBridgeSearch : Set where
  constructor nextExactBridgeSearch
  field
    sourceSearchTarget : String
    exactTarget : String
    requireZeroCarrierIdentity : Bool
    requireTaperIdentity : Bool
    requireErrorConsumerCompatibility : Bool
    mayPromoteFromSharedVocabulary : Bool
    mayPromoteFromSharedVocabularyIsFalse : mayPromoteFromSharedVocabulary ≡ false

canonicalNextExactBridgeSearch : NextExactBridgeSearch
canonicalNextExactBridgeSearch =
  nextExactBridgeSearch
    "explicit-formula/Hadamard/log-derivative identities connecting xi or H_0 evaluations to finite target-centred zeta-zero sums"
    g2ConsumerReference
    true
    true
    true
    false refl
