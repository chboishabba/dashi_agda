module DASHI.Biology.TernaryHallTransitionCoalitionExact where

open import DASHI.Core.Prelude

import DASHI.Biology.HallOfHallsCoalition as Hall
import DASHI.Biology.DASHIYijingRelationalOperatorsExact as Yijing
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- Joint hall/transition coalition.
--
-- The received moving-line cast supplies a typed initial/resulting transition;
-- the hall carrier supplies recursive geometry, viewpoint contrast, and
-- projective underdetermination.  Their conjunction is a finite candidate,
-- not an assertion that a divination recovered or predicted a vision.

record TernaryHallCandidate : Set where
  constructor ternaryHallCandidate
  field
    hallCandidate : Hall.HallCoalitionCandidate
    transitionCarrier : Bool
    movingEvidence : Bool
    ternaryMediator : Triadic.KernelTrit

open TernaryHallCandidate public

staticArchitectureCandidate : TernaryHallCandidate
staticArchitectureCandidate =
  ternaryHallCandidate
    Hall.architectureOnlyCandidate
    false
    false
    Triadic.negativeTrit

movingProjectionCandidate : TernaryHallCandidate
movingProjectionCandidate =
  ternaryHallCandidate
    Hall.projectionOnlyCandidate
    true
    true
    Triadic.positiveTrit

integratedTernaryHallCandidate : TernaryHallCandidate
integratedTernaryHallCandidate =
  ternaryHallCandidate
    Hall.integratedHallCandidate
    true
    true
    Triadic.zeroTrit

transitionPenalty : TernaryHallCandidate → Nat
transitionPenalty
  (ternaryHallCandidate
    Hall.architectureOnlyCandidate false false Triadic.negativeTrit) = 2
transitionPenalty
  (ternaryHallCandidate
    Hall.projectionOnlyCandidate true true Triadic.positiveTrit) = 1
transitionPenalty
  (ternaryHallCandidate
    Hall.integratedHallCandidate true true Triadic.zeroTrit) = 0
transitionPenalty candidate = 3

jointObjective : TernaryHallCandidate → Nat
jointObjective candidate =
  Hall.hallObjective (hallCandidate candidate)
  +
  transitionPenalty candidate

staticArchitectureObjectiveIsEight :
  jointObjective staticArchitectureCandidate ≡ 8
staticArchitectureObjectiveIsEight = refl

movingProjectionObjectiveIsSix :
  jointObjective movingProjectionCandidate ≡ 6
movingProjectionObjectiveIsSix = refl

integratedTernaryHallObjectiveIsZero :
  jointObjective integratedTernaryHallCandidate ≡ 0
integratedTernaryHallObjectiveIsZero = refl

canonicalTernaryHallCandidates : List TernaryHallCandidate
canonicalTernaryHallCandidates =
  staticArchitectureCandidate
  ∷ movingProjectionCandidate
  ∷ integratedTernaryHallCandidate
  ∷ []

selectedTernaryHallCandidate : TernaryHallCandidate
selectedTernaryHallCandidate = integratedTernaryHallCandidate

selectedTernaryHallMinimalOverCanonicalFamily :
  jointObjective selectedTernaryHallCandidate
  ≤
  jointObjective staticArchitectureCandidate
  ×
  jointObjective selectedTernaryHallCandidate
  ≤
  jointObjective movingProjectionCandidate
  ×
  jointObjective selectedTernaryHallCandidate
  ≤
  jointObjective integratedTernaryHallCandidate
selectedTernaryHallMinimalOverCanonicalFamily =
  z≤n , z≤n , ≤-refl

canonicalCast : Yijing.CastTransformation
canonicalCast =
  Yijing.compileCast Yijing.canonicalClassicalCast

canonicalCastInitialIsExpected :
  Yijing.initialHexagram canonicalCast
  ≡
  Yijing.canonicalCastInitial
canonicalCastInitialIsExpected = refl

canonicalCastResultIsExpected :
  Yijing.resultingHexagram canonicalCast
  ≡
  Yijing.canonicalCastResulting
canonicalCastResultIsExpected = refl

record TernaryHallCoalitionWitness : Set₁ where
  constructor ternaryHallCoalitionWitness
  field
    selected : TernaryHallCandidate
    selectedObjectiveZero : jointObjective selected ≡ 0
    hallWitness : Hall.HallOfHallsCoalitionWitness
    castWitness : Yijing.CastTransformation
    castInitial :
      Yijing.initialHexagram castWitness ≡ Yijing.canonicalCastInitial
    castResult :
      Yijing.resultingHexagram castWitness ≡ Yijing.canonicalCastResulting

open TernaryHallCoalitionWitness public

canonicalTernaryHallCoalitionWitness : TernaryHallCoalitionWitness
canonicalTernaryHallCoalitionWitness =
  ternaryHallCoalitionWitness
    selectedTernaryHallCandidate
    integratedTernaryHallObjectiveIsZero
    Hall.canonicalHallOfHallsCoalitionWitness
    canonicalCast
    canonicalCastInitialIsExpected
    canonicalCastResultIsExpected

record TernaryHallBoundary : Set where
  constructor ternaryHallBoundary
  field
    zeroObjectiveRecoversRememberedScene : Bool
    zeroObjectiveRecoversRememberedSceneIsFalse :
      zeroObjectiveRecoversRememberedScene ≡ false

    movingCastPredictsExternalEvent : Bool
    movingCastPredictsExternalEventIsFalse :
      movingCastPredictsExternalEvent ≡ false

canonicalTernaryHallBoundary : TernaryHallBoundary
canonicalTernaryHallBoundary =
  ternaryHallBoundary false refl false refl
