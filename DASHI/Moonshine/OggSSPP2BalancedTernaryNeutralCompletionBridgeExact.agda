module DASHI.Moonshine.OggSSPP2BalancedTernaryNeutralCompletionBridgeExact where

------------------------------------------------------------------------
-- p=2 BALANCED-TERNARY DUPLICATED-CENTRE COMPLETION
--        ~= EXISTING ORIENTED10 COMPLETION CARRIER
--
-- DASHI CONTRIBUTION
--
-- OggSSPP2BalancedTernaryPuncturedPlaneExact constructs the ten-state carrier
--
--   lower centre + upper centre + punctured T^2
--
-- with 1+1+8 states.
--
-- JInvariant369NeutralCuspRelationCrossPollinationExact independently owns
--
--   Oriented10 = ComplementMode5 x BinaryPhase
--
-- and a ten->nine quotient that collapses only the duplicated orientation of
-- the distinguished mode09 identity.
--
-- This module proves an exact finite rechart between those two ten-state
-- presentations and proves their ten->nine collapse diagrams commute.
--
-- This is a same-presentation theorem for the finite carriers.  It does not
-- identify the p=2 arithmetic Gaussian-CM source with either carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Completion
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.JInvariant369NeutralCuspRelationCrossPollinationExact as Neutral
import DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact as Plane
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Exact ten-state rechart.
------------------------------------------------------------------------

duplicatedCentreToOriented10 :
  Plane.DuplicatedCentreNineSheet ->
  Neutral.Oriented10
duplicatedCentreToOriented10 Plane.lowerCentre =
  Completion.mode09 , Completion.counterPhase
duplicatedCentreToOriented10 Plane.upperCentre =
  Completion.mode09 , Completion.directPhase
duplicatedCentreToOriented10
  (Plane.puncturedPoint Plane.negativeFirstAxis) =
  Completion.mode18 , Completion.counterPhase
duplicatedCentreToOriented10
  (Plane.puncturedPoint Plane.positiveFirstAxis) =
  Completion.mode18 , Completion.directPhase
duplicatedCentreToOriented10
  (Plane.puncturedPoint Plane.negativeSecondAxis) =
  Completion.mode27 , Completion.counterPhase
duplicatedCentreToOriented10
  (Plane.puncturedPoint Plane.positiveSecondAxis) =
  Completion.mode27 , Completion.directPhase
duplicatedCentreToOriented10
  (Plane.puncturedPoint Plane.negativeEqualDiagonal) =
  Completion.mode36 , Completion.counterPhase
duplicatedCentreToOriented10
  (Plane.puncturedPoint Plane.positiveEqualDiagonal) =
  Completion.mode36 , Completion.directPhase
duplicatedCentreToOriented10
  (Plane.puncturedPoint Plane.negativeOppositeDiagonal) =
  Completion.mode45 , Completion.counterPhase
duplicatedCentreToOriented10
  (Plane.puncturedPoint Plane.positiveOppositeDiagonal) =
  Completion.mode45 , Completion.directPhase

oriented10ToDuplicatedCentre :
  Neutral.Oriented10 ->
  Plane.DuplicatedCentreNineSheet
oriented10ToDuplicatedCentre
  (Completion.mode09 , Completion.counterPhase) =
  Plane.lowerCentre
oriented10ToDuplicatedCentre
  (Completion.mode09 , Completion.directPhase) =
  Plane.upperCentre
oriented10ToDuplicatedCentre
  (Completion.mode18 , Completion.counterPhase) =
  Plane.puncturedPoint Plane.negativeFirstAxis
oriented10ToDuplicatedCentre
  (Completion.mode18 , Completion.directPhase) =
  Plane.puncturedPoint Plane.positiveFirstAxis
oriented10ToDuplicatedCentre
  (Completion.mode27 , Completion.counterPhase) =
  Plane.puncturedPoint Plane.negativeSecondAxis
oriented10ToDuplicatedCentre
  (Completion.mode27 , Completion.directPhase) =
  Plane.puncturedPoint Plane.positiveSecondAxis
oriented10ToDuplicatedCentre
  (Completion.mode36 , Completion.counterPhase) =
  Plane.puncturedPoint Plane.negativeEqualDiagonal
oriented10ToDuplicatedCentre
  (Completion.mode36 , Completion.directPhase) =
  Plane.puncturedPoint Plane.positiveEqualDiagonal
oriented10ToDuplicatedCentre
  (Completion.mode45 , Completion.counterPhase) =
  Plane.puncturedPoint Plane.negativeOppositeDiagonal
oriented10ToDuplicatedCentre
  (Completion.mode45 , Completion.directPhase) =
  Plane.puncturedPoint Plane.positiveOppositeDiagonal

duplicatedCentreOrientedRoundTrip :
  (state : Plane.DuplicatedCentreNineSheet) ->
  oriented10ToDuplicatedCentre
    (duplicatedCentreToOriented10 state)
  ≡ state
duplicatedCentreOrientedRoundTrip Plane.lowerCentre = refl
duplicatedCentreOrientedRoundTrip Plane.upperCentre = refl
duplicatedCentreOrientedRoundTrip
  (Plane.puncturedPoint Plane.negativeFirstAxis) = refl
duplicatedCentreOrientedRoundTrip
  (Plane.puncturedPoint Plane.positiveFirstAxis) = refl
duplicatedCentreOrientedRoundTrip
  (Plane.puncturedPoint Plane.negativeSecondAxis) = refl
duplicatedCentreOrientedRoundTrip
  (Plane.puncturedPoint Plane.positiveSecondAxis) = refl
duplicatedCentreOrientedRoundTrip
  (Plane.puncturedPoint Plane.negativeEqualDiagonal) = refl
duplicatedCentreOrientedRoundTrip
  (Plane.puncturedPoint Plane.positiveEqualDiagonal) = refl
duplicatedCentreOrientedRoundTrip
  (Plane.puncturedPoint Plane.negativeOppositeDiagonal) = refl
duplicatedCentreOrientedRoundTrip
  (Plane.puncturedPoint Plane.positiveOppositeDiagonal) = refl

orientedDuplicatedCentreRoundTrip :
  (state : Neutral.Oriented10) ->
  duplicatedCentreToOriented10
    (oriented10ToDuplicatedCentre state)
  ≡ state
orientedDuplicatedCentreRoundTrip
  (Completion.mode09 , Completion.counterPhase) = refl
orientedDuplicatedCentreRoundTrip
  (Completion.mode09 , Completion.directPhase) = refl
orientedDuplicatedCentreRoundTrip
  (Completion.mode18 , Completion.counterPhase) = refl
orientedDuplicatedCentreRoundTrip
  (Completion.mode18 , Completion.directPhase) = refl
orientedDuplicatedCentreRoundTrip
  (Completion.mode27 , Completion.counterPhase) = refl
orientedDuplicatedCentreRoundTrip
  (Completion.mode27 , Completion.directPhase) = refl
orientedDuplicatedCentreRoundTrip
  (Completion.mode36 , Completion.counterPhase) = refl
orientedDuplicatedCentreRoundTrip
  (Completion.mode36 , Completion.directPhase) = refl
orientedDuplicatedCentreRoundTrip
  (Completion.mode45 , Completion.counterPhase) = refl
orientedDuplicatedCentreRoundTrip
  (Completion.mode45 , Completion.directPhase) = refl

------------------------------------------------------------------------
-- 2. Rechart ordinary nine-sheet to the existing Quotient9 carrier.
------------------------------------------------------------------------

nineSheetToQuotient9 :
  Triadic.NineSheet ->
  Neutral.Quotient9
nineSheetToQuotient9
  (Triadic.zeroTrit , Triadic.zeroTrit) =
  Neutral.identity
nineSheetToQuotient9
  (Triadic.negativeTrit , Triadic.zeroTrit) =
  Neutral.mode18counter
nineSheetToQuotient9
  (Triadic.positiveTrit , Triadic.zeroTrit) =
  Neutral.mode18direct
nineSheetToQuotient9
  (Triadic.zeroTrit , Triadic.negativeTrit) =
  Neutral.mode27counter
nineSheetToQuotient9
  (Triadic.zeroTrit , Triadic.positiveTrit) =
  Neutral.mode27direct
nineSheetToQuotient9
  (Triadic.negativeTrit , Triadic.negativeTrit) =
  Neutral.mode36counter
nineSheetToQuotient9
  (Triadic.positiveTrit , Triadic.positiveTrit) =
  Neutral.mode36direct
nineSheetToQuotient9
  (Triadic.negativeTrit , Triadic.positiveTrit) =
  Neutral.mode45counter
nineSheetToQuotient9
  (Triadic.positiveTrit , Triadic.negativeTrit) =
  Neutral.mode45direct

quotient9ToNineSheet :
  Neutral.Quotient9 ->
  Triadic.NineSheet
quotient9ToNineSheet Neutral.identity =
  Triadic.zeroTrit , Triadic.zeroTrit
quotient9ToNineSheet Neutral.mode18counter =
  Triadic.negativeTrit , Triadic.zeroTrit
quotient9ToNineSheet Neutral.mode18direct =
  Triadic.positiveTrit , Triadic.zeroTrit
quotient9ToNineSheet Neutral.mode27counter =
  Triadic.zeroTrit , Triadic.negativeTrit
quotient9ToNineSheet Neutral.mode27direct =
  Triadic.zeroTrit , Triadic.positiveTrit
quotient9ToNineSheet Neutral.mode36counter =
  Triadic.negativeTrit , Triadic.negativeTrit
quotient9ToNineSheet Neutral.mode36direct =
  Triadic.positiveTrit , Triadic.positiveTrit
quotient9ToNineSheet Neutral.mode45counter =
  Triadic.negativeTrit , Triadic.positiveTrit
quotient9ToNineSheet Neutral.mode45direct =
  Triadic.positiveTrit , Triadic.negativeTrit

nineQuotientRoundTrip :
  (sheet : Triadic.NineSheet) ->
  quotient9ToNineSheet (nineSheetToQuotient9 sheet) ≡ sheet
nineQuotientRoundTrip (Triadic.zeroTrit , Triadic.zeroTrit) = refl
nineQuotientRoundTrip (Triadic.negativeTrit , Triadic.zeroTrit) = refl
nineQuotientRoundTrip (Triadic.positiveTrit , Triadic.zeroTrit) = refl
nineQuotientRoundTrip (Triadic.zeroTrit , Triadic.negativeTrit) = refl
nineQuotientRoundTrip (Triadic.zeroTrit , Triadic.positiveTrit) = refl
nineQuotientRoundTrip (Triadic.negativeTrit , Triadic.negativeTrit) = refl
nineQuotientRoundTrip (Triadic.positiveTrit , Triadic.positiveTrit) = refl
nineQuotientRoundTrip (Triadic.negativeTrit , Triadic.positiveTrit) = refl
nineQuotientRoundTrip (Triadic.positiveTrit , Triadic.negativeTrit) = refl

quotientNineRoundTrip :
  (state : Neutral.Quotient9) ->
  nineSheetToQuotient9 (quotient9ToNineSheet state) ≡ state
quotientNineRoundTrip Neutral.identity = refl
quotientNineRoundTrip Neutral.mode18counter = refl
quotientNineRoundTrip Neutral.mode18direct = refl
quotientNineRoundTrip Neutral.mode27counter = refl
quotientNineRoundTrip Neutral.mode27direct = refl
quotientNineRoundTrip Neutral.mode36counter = refl
quotientNineRoundTrip Neutral.mode36direct = refl
quotientNineRoundTrip Neutral.mode45counter = refl
quotientNineRoundTrip Neutral.mode45direct = refl

------------------------------------------------------------------------
-- 3. The two independently-owned ten->nine collapses commute.
------------------------------------------------------------------------

neutralCollapseCommutes :
  (state : Plane.DuplicatedCentreNineSheet) ->
  nineSheetToQuotient9 (Plane.collapseDuplicatedCentre state)
  ≡
  Neutral.quotientOriented10
    (duplicatedCentreToOriented10 state)
neutralCollapseCommutes Plane.lowerCentre = refl
neutralCollapseCommutes Plane.upperCentre = refl
neutralCollapseCommutes
  (Plane.puncturedPoint Plane.negativeFirstAxis) = refl
neutralCollapseCommutes
  (Plane.puncturedPoint Plane.positiveFirstAxis) = refl
neutralCollapseCommutes
  (Plane.puncturedPoint Plane.negativeSecondAxis) = refl
neutralCollapseCommutes
  (Plane.puncturedPoint Plane.positiveSecondAxis) = refl
neutralCollapseCommutes
  (Plane.puncturedPoint Plane.negativeEqualDiagonal) = refl
neutralCollapseCommutes
  (Plane.puncturedPoint Plane.positiveEqualDiagonal) = refl
neutralCollapseCommutes
  (Plane.puncturedPoint Plane.negativeOppositeDiagonal) = refl
neutralCollapseCommutes
  (Plane.puncturedPoint Plane.positiveOppositeDiagonal) = refl

------------------------------------------------------------------------
-- 4. Semantic firewall.
------------------------------------------------------------------------

data FiniteRechartCreatesArithmeticCMIdentity : Set where
data FiniteRechartCreatesJInvariantSemanticIdentity : Set where

finiteRechartDoesNotCreateArithmeticCMIdentity :
  FiniteRechartCreatesArithmeticCMIdentity -> ⊥
finiteRechartDoesNotCreateArithmeticCMIdentity ()

finiteRechartDoesNotCreateJInvariantSemanticIdentity :
  FiniteRechartCreatesJInvariantSemanticIdentity -> ⊥
finiteRechartDoesNotCreateJInvariantSemanticIdentity ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record P2BalancedTernaryNeutralCompletionBridgeBoundary : Set where
  constructor p2-balanced-ternary-neutral-completion-bridge-boundary
  field
    duplicatedCentreTenRechartsToExistingOrientedTen : Bool
    ordinaryNineSheetRechartsToExistingQuotientNine : Bool
    twoTenToNineCollapseDiagramsCommute : Bool
    equalFinitePresentationCreatesArithmeticCMIdentity : Bool
    equalFinitePresentationCreatesJInvariantSemanticIdentity : Bool

canonicalP2BalancedTernaryNeutralCompletionBridgeBoundary :
  P2BalancedTernaryNeutralCompletionBridgeBoundary
canonicalP2BalancedTernaryNeutralCompletionBridgeBoundary =
  p2-balanced-ternary-neutral-completion-bridge-boundary
    true true true false false
