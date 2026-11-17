module DASHI.Cognition.PNF.X369CenteredDirectedConsumerMDLExact where

------------------------------------------------------------------------
-- CONSUMER-RELATIVE MDL instantiated on the ORIGINAL centred triad
-- feature source. Compare only the DECLARED coordinate-projection
-- portfolio: first channel alone (1 integer scalar), first + forward
-- (2 scalars), or full original directed T (3 scalars).
--
-- On the zero-DC subspace the first two channels recover the reverse
-- exactly and beat the full three-channel *original scalar count*.
-- This does NOT prove optimality among arbitrary nonlinear integer
-- encodings, data bitrate, memory bandwidth, latency or physics.
--
-- Reuse the existing consumer MDL owner, not a replacement theory.
-- Proposed proof source; pending Agda 2.9 kernel acceptance.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _-_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:-_; _:*_; con; _:=_)
import DASHI.Cognition.PNF.X369DirectedRouterConditionalCodecExact as Original
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL

record CenteredDirected : Set where
  constructor centeredDirected
  field
    originalChannels : Original.Directed
    certifiedZeroDC :
      Original.originalDirectedTotal originalChannels ≡ (+ 0)
open CenteredDirected public

consumer : CenteredDirected → ℤ
consumer z = Original.sourceReverse (originalChannels z)

firstCode : CenteredDirected → ℤ
firstCode z = Original.sourceSelf (originalChannels z)

twoCode : CenteredDirected → ℤ × ℤ
twoCode z = Original.encodeDirectedTwo (originalChannels z)

fullCode : CenteredDirected → Original.Directed
fullCode = originalChannels

-- A certified zero-DC triple is reconstructible from the FIRST
-- TWO coordinates. This holds for EVERY such triple, not just the
-- explicit examples, and is independent of a weight configuration.
recoverCentered :
  (z : CenteredDirected) →
  Original.decodeDirectedWithKnownDC (+ 0) (twoCode z)
  ≡ originalChannels z
recoverCentered (centeredDirected d zero) =
  trans
    (cong
      (λ total → Original.decodeDirectedWithKnownDC
        total (Original.encodeDirectedTwo d))
      (sym zero))
    (Original.twoDirectedPlusTotalReconstructsOriginal d)

twoCodeSufficient :
  Descent.ConsumerSufficient twoCode consumer
twoCodeSufficient left right equal =
  trans
    (sym (cong Original.sourceReverse (recoverCentered left)))
    (trans
      (cong
        (λ code → Original.sourceReverse
          (Original.decodeDirectedWithKnownDC (+ 0) code))
        equal)
      (cong Original.sourceReverse (recoverCentered right)))

fullCodeSufficient :
  Descent.ConsumerSufficient fullCode consumer
fullCodeSufficient left right equal =
  cong Original.sourceReverse equal

-- Counterexample within the ACTUAL original triad feature source.
-- x=(1,0,0), h=(0,0,0) versus h=(0,1,-1).
-- Both DC sums are 0; both first directed channels are 0;
-- the reverse consumers differ (0 versus -1).
-- We express negative one as 0 - 1 via original integer operations.
centeredA centeredB : CenteredDirected
centeredA = centeredDirected
  (Original.originalDirected (+ 1) (+ 0) (+ 0)
                             (+ 0) (+ 0) (+ 0)) refl
centeredB = centeredDirected
  (Original.originalDirected (+ 1) (+ 0) (+ 0)
                             (+ 0) (+ 1) ((+ 0) - (+ 1))) refl

sameFirstCode : firstCode centeredA ≡ firstCode centeredB
sameFirstCode = refl

differentReverse :
  consumer centeredA ≡ consumer centeredB → ⊥
differentReverse ()

firstCodeNotSufficient :
  Descent.ConsumerSufficient firstCode consumer → ⊥
firstCodeNotSufficient sufficient =
  differentReverse (sufficient centeredA centeredB sameFirstCode)

data Stage : Set where
  firstOnly : Stage
  centeredTwo : Stage
  rawThree : Stage

stageCost : Stage → Nat
stageCost firstOnly = 1
stageCost centeredTwo = 2
stageCost rawThree = 3

stageAdequacy : Stage → Set
stageAdequacy firstOnly =
  Descent.ConsumerSufficient firstCode consumer
stageAdequacy centeredTwo =
  Descent.ConsumerSufficient twoCode consumer
stageAdequacy rawThree =
  Descent.ConsumerSufficient fullCode consumer

stageReference : Stage → String
stageReference firstOnly = "original self channel only"
stageReference centeredTwo = "original self+forward; zero-DC restricted source"
stageReference rawThree = "original full directed triple; zero-DC restricted source"

stageRefines : Stage → Stage → Set
stageRefines left right = left ≡ right

sourceCoordinateMDL : MDL.ConsumerMDLProblem
sourceCoordinateMDL =
  MDL.consumerMDLProblem
    Stage
    (λ _ → ⊤)
    stageAdequacy
    stageCost
    stageRefines
    stageReference
    "number of original fixed-width ℤ feature coordinates, not bits"
    "original reverse-channel consumer on certified zero-DC triads"

centeredTwoEligible : MDL.Eligible sourceCoordinateMDL centeredTwo
centeredTwoEligible = tt , twoCodeSufficient

rawThreeEligible : MDL.Eligible sourceCoordinateMDL rawThree
rawThreeEligible = tt , fullCodeSufficient

firstOnlyIneligible :
  MDL.Eligible sourceCoordinateMDL firstOnly → ⊥
firstOnlyIneligible eligible = firstCodeNotSufficient (proj₂ eligible)

-- Within this declared three-stage coordinate-projection portfolio,
-- two retained channels have minimum admissible scalar COUNT.
-- The one-scalar candidate is rejected by an actual source collision.
centeredTwoIsMinimalInDeclaredPortfolio :
  MDL.MinimalEligibleDescription sourceCoordinateMDL centeredTwo
centeredTwoIsMinimalInDeclaredPortfolio =
  MDL.minimalEligibleDescription
    tt
    twoCodeSufficient
    proof
    "only original coordinate projections; full nonlinear codes excluded"
  where
    proof :
      (candidate : Stage) →
      MDL.Admissible sourceCoordinateMDL candidate →
      MDL.ConsumerAdequate sourceCoordinateMDL candidate →
      stageCost centeredTwo ≤ stageCost candidate
    proof firstOnly admitted adequate =
      ⊥-elim (firstCodeNotSufficient adequate)
    proof centeredTwo admitted adequate =
      s≤s (s≤s z≤n)
    proof rawThree admitted adequate =
      s≤s (s≤s z≤n)


------------------------------------------------------------------------
-- Typed original-source C3 action on the admitted centered MDL carrier.
-- This makes the smaller sufficient feature code action-preserving,
-- not just a one-time readout construction.
------------------------------------------------------------------------

rotatedTotalEqualsOriginal :
  (d : Original.Directed) →
  Original.originalDirectedTotal (Original.rotateFullDirected d)
  ≡ Original.originalDirectedTotal d
rotatedTotalEqualsOriginal (Original.directed s f r) =
  solve 3
    (λ s f r →
      (((r :+ s) :+ f) := ((s :+ f) :+ r)))
    refl s f r

rotateCenteredSource : CenteredDirected → CenteredDirected
rotateCenteredSource (centeredDirected d zero) =
  centeredDirected
    (Original.rotateFullDirected d)
    (trans (rotatedTotalEqualsOriginal d) zero)

centeredTwoCodeIntertwinesOriginalC3 :
  (z : CenteredDirected) →
  twoCode (rotateCenteredSource z)
  ≡ Original.rotateCenteredTwo (twoCode z)
centeredTwoCodeIntertwinesOriginalC3
  (centeredDirected d zero) =
  Original.sourceCenteredC3TwoChannelIntertwines d zero

-- These are SOURCE directed-channel actions. They do not
-- identify a semantic argument rotation, trialectic face or
-- neural hidden-space intertwiner.

-- This witness does not authorize compression of arbitrary non-centred
-- source states or semantic/face/future consumers not shown sufficient.
