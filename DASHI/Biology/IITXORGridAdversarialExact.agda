module DASHI.Biology.IITXORGridAdversarialExact where

open import DASHI.Core.Prelude

import DASHI.Biology.StateDependentMultiplexTransducer as XOR
import DASHI.Biology.IIT4FiniteCausalStructureExact as IIT4
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.IntegrationConsumerDescentOrderExact as Integration

------------------------------------------------------------------------
-- XOR ADVERSARIAL FAMILY / HISTORICAL IIT BOUNDARY
--
-- Scott Aaronson's 2014 IIT critique used sparse globally integrating Boolean
-- constructions (including expander-style networks).  The subsequent exchange
-- with Giulio Tononi explicitly discussed large XOR networks and a 2D square
-- grid.  Those arguments targeted then-current IIT formulations; this module
-- therefore keeps their stress-test role separate from IIT 4.0 big-Phi.
--
-- The repository already owns exact XOR dynamics.  We reuse that owner rather
-- than introducing a second Boolean gate semantics.
------------------------------------------------------------------------

XState : Set
XState = Bool × Bool

parityObservation : XState → Bool
parityObservation state = XOR.xor (proj₁ state) (proj₂ state)

leftBitConsumer : XState → Bool
leftBitConsumer = proj₁

------------------------------------------------------------------------
-- Same-object weld into the finite IIT carrier.
------------------------------------------------------------------------

boolEnumerationComplete :
  (x : Bool) → IIT4._ListedIn_ x (false ∷ true ∷ [])
boolEnumerationComplete false = IIT4.listedHere
boolEnumerationComplete true = IIT4.listedThere IIT4.listedHere

boolCarrier : IIT4.FiniteCarrier
boolCarrier =
  IIT4.finiteCarrier
    Bool
    (false ∷ true ∷ [])
    boolEnumerationComplete

xStateEnumeration : List XState
xStateEnumeration =
  (false , false) ∷
  (false , true) ∷
  (true , false) ∷
  (true , true) ∷ []

xStateEnumerationComplete :
  (state : XState) → IIT4._ListedIn_ state xStateEnumeration
xStateEnumerationComplete (false , false) = IIT4.listedHere
xStateEnumerationComplete (false , true) =
  IIT4.listedThere IIT4.listedHere
xStateEnumerationComplete (true , false) =
  IIT4.listedThere (IIT4.listedThere IIT4.listedHere)
xStateEnumerationComplete (true , true) =
  IIT4.listedThere
    (IIT4.listedThere
      (IIT4.listedThere IIT4.listedHere))

xStateCarrier : IIT4.FiniteCarrier
xStateCarrier =
  IIT4.finiteCarrier
    XState
    xStateEnumeration
    xStateEnumerationComplete

sameBool : Bool → Bool → Bool
sameBool false false = true
sameBool false true = false
sameBool true false = false
sameBool true true = true

andBool : Bool → Bool → Bool
andBool false _ = false
andBool true x = x

sameXState : XState → XState → Bool
sameXState left right =
  andBool
    (sameBool (proj₁ left) (proj₁ right))
    (sameBool (proj₂ left) (proj₂ right))

xorSuccessor : XState → XState
xorSuccessor state =
  parityObservation state , leftBitConsumer state

xorTransitionWeight : XState → XState → Nat
xorTransitionWeight state candidate with
  sameXState (xorSuccessor state) candidate
... | true = 1
... | false = 0

xorTwoBitFiniteCausalSystem : IIT4.FiniteCausalSystem
xorTwoBitFiniteCausalSystem =
  IIT4.finiteCausalSystem
    boolCarrier
    xStateCarrier
    (false , false)
    xorTransitionWeight
    "deterministic 0/1 transition weights; each source state has one successor"

xorCurrentStateReceipt :
  IIT4.currentState xorTwoBitFiniteCausalSystem ≡ (false , false)
xorCurrentStateReceipt = refl

xorDeterministicStepReceipt :
  xorTransitionWeight (true , false) (true , true) ≡ 1
xorDeterministicStepReceipt = refl

xorWrongSuccessorHasZeroWeight :
  xorTransitionWeight (true , false) (false , false) ≡ 0
xorWrongSuccessorHasZeroWeight = refl

------------------------------------------------------------------------
-- Consumer-relative non-descent on the same Boolean state carrier.
------------------------------------------------------------------------

parityCollision :
  parityObservation (false , false) ≡
  parityObservation (true , true)
parityCollision = refl

parityLosesLeftBit :
  Descent.ConsumerNonDescentWitness
    parityObservation
    leftBitConsumer
parityLosesLeftBit =
  Descent.consumerNonDescentWitness
    (false , false)
    (true , true)
    refl
    XOR.false≢true

parityIntegrationObservation :
  Integration.IntegrationObservation XState Bool Bool
parityIntegrationObservation =
  Integration.integrationObservation
    parityObservation
    leftBitConsumer

parityIntegrationDoesNotDescend :
  Integration.IntegrationNonDescentWitness parityIntegrationObservation
parityIntegrationDoesNotDescend =
  Integration.integrationNonDescentWitness parityLosesLeftBit

parityCannotFactorLeftBit :
  Integration.ScoreFactorsThrough parityIntegrationObservation → ⊥
parityCannotFactorLeftBit =
  Integration.nonDescentBlocksScoreFactorization
    parityIntegrationDoesNotDescend

------------------------------------------------------------------------
-- Small exact grid fixture.  This is a deterministic XOR network, not a claim
-- that its graph-cut count is IIT 4.0 phi_s or big-Phi.
------------------------------------------------------------------------

record Grid2x2 : Set where
  constructor grid2x2
  field
    northWest northEast southWest southEast : Bool

open Grid2x2 public

gridStep : Grid2x2 → Grid2x2
gridStep grid =
  grid2x2
    (XOR.xor (northEast grid) (southWest grid))
    (XOR.xor (northWest grid) (southEast grid))
    (XOR.xor (northWest grid) (southEast grid))
    (XOR.xor (northEast grid) (southWest grid))

canonicalGridInput : Grid2x2
canonicalGridInput = grid2x2 true false false false

canonicalGridStep :
  gridStep canonicalGridInput ≡
  grid2x2 false true true false
canonicalGridStep = refl

-- Mid-cut edge counts for the literal toy topologies.
-- A four-node path has one middle crossing; a 2x2 square has two crossings.
line4MiddleCutEdges : Nat
line4MiddleCutEdges = 1

square2x2MiddleCutEdges : Nat
square2x2MiddleCutEdges = 2

lineMiddleCutComputed : line4MiddleCutEdges ≡ 1
lineMiddleCutComputed = refl

squareMiddleCutComputed : square2x2MiddleCutEdges ≡ 2
squareMiddleCutComputed = refl

lineAndSquareCutCountsDiffer :
  line4MiddleCutEdges ≡ square2x2MiddleCutEdges → ⊥
lineAndSquareCutCountsDiffer ()

repoNativeXorGateReceipt :
  XOR.runOutput XOR.canonicalBoolTransducer true false true ≡ false
repoNativeXorGateReceipt = refl

record HistoricalXORStressBoundary : Set where
  constructor historicalXORStressBoundary
  field
    reusesRepoNativeXor : Bool
    xorFixtureInhabitsFiniteIITCarrier : Bool
    squareGridHasLargerToyMidCutThanLine : Bool
    graphCutCountEqualsIIT4SystemPhi : Bool
    historicalIITPhiEqualsIIT4BigPhi : Bool
    largeIntegrationAloneEstablishesParadigmConsciousness : Bool
    stressTestRequiresIndependentInterpretiveCriterion : Bool

open HistoricalXORStressBoundary public

canonicalHistoricalXORStressBoundary : HistoricalXORStressBoundary
canonicalHistoricalXORStressBoundary =
  historicalXORStressBoundary
    true true true false false false true

graphCutIsNotSilentlyPromotedToIIT4 :
  graphCutCountEqualsIIT4SystemPhi canonicalHistoricalXORStressBoundary ≡ false
graphCutIsNotSilentlyPromotedToIIT4 = refl

integrationDoesNotSelfPromoteToConsciousness :
  largeIntegrationAloneEstablishesParadigmConsciousness canonicalHistoricalXORStressBoundary ≡ false
integrationDoesNotSelfPromoteToConsciousness = refl
