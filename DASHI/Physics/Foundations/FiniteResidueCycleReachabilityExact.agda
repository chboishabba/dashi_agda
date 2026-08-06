module DASHI.Physics.Foundations.FiniteResidueCycleReachabilityExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Residue carriers are finite cyclic algebras.  They are not positional base
-- numeral systems merely because their cardinalities are six and nine.

data Residue6 : Set where
  residue6Zero : Residue6
  residue6One : Residue6
  residue6Two : Residue6
  residue6Three : Residue6
  residue6Four : Residue6
  residue6Five : Residue6

successor6 : Residue6 → Residue6
successor6 residue6Zero = residue6One
successor6 residue6One = residue6Two
successor6 residue6Two = residue6Three
successor6 residue6Three = residue6Four
successor6 residue6Four = residue6Five
successor6 residue6Five = residue6Zero

successor6Three : Residue6 → Residue6
successor6Three x = successor6 (successor6 (successor6 x))

successor6Six : Residue6 → Residue6
successor6Six x = successor6Three (successor6Three x)

sixCycleReturns : (x : Residue6) → successor6Six x ≡ x
sixCycleReturns residue6Zero = refl
sixCycleReturns residue6One = refl
sixCycleReturns residue6Two = refl
sixCycleReturns residue6Three = refl
sixCycleReturns residue6Four = refl
sixCycleReturns residue6Five = refl

data Residue9 : Set where
  residue9Zero : Residue9
  residue9One : Residue9
  residue9Two : Residue9
  residue9Three : Residue9
  residue9Four : Residue9
  residue9Five : Residue9
  residue9Six : Residue9
  residue9Seven : Residue9
  residue9Eight : Residue9

successor9 : Residue9 → Residue9
successor9 residue9Zero = residue9One
successor9 residue9One = residue9Two
successor9 residue9Two = residue9Three
successor9 residue9Three = residue9Four
successor9 residue9Four = residue9Five
successor9 residue9Five = residue9Six
successor9 residue9Six = residue9Seven
successor9 residue9Seven = residue9Eight
successor9 residue9Eight = residue9Zero

successor9Three : Residue9 → Residue9
successor9Three x = successor9 (successor9 (successor9 x))

successor9Six : Residue9 → Residue9
successor9Six x = successor9Three (successor9Three x)

successor9Nine : Residue9 → Residue9
successor9Nine x = successor9Three (successor9Six x)

nineCycleReturns : (x : Residue9) → successor9Nine x ≡ x
nineCycleReturns residue9Zero = refl
nineCycleReturns residue9One = refl
nineCycleReturns residue9Two = refl
nineCycleReturns residue9Three = refl
nineCycleReturns residue9Four = refl
nineCycleReturns residue9Five = refl
nineCycleReturns residue9Six = refl
nineCycleReturns residue9Seven = refl
nineCycleReturns residue9Eight = refl

------------------------------------------------------------------------
-- Bounded reachability is a finite transition theorem, not a statement about
-- unbounded overflow semantics.

data ReachState : Set where
  reachStart : ReachState
  reachMiddle : ReachState
  reachTerminal : ReachState

reachStep : ReachState → ReachState
reachStep reachStart = reachMiddle
reachStep reachMiddle = reachTerminal
reachStep reachTerminal = reachTerminal

reachStepTwo : ReachState → ReachState
reachStepTwo x = reachStep (reachStep x)

terminalReachableWithinTwo :
  reachStepTwo reachStart ≡ reachTerminal
terminalReachableWithinTwo = refl

terminalIsAbsorbing : reachStep reachTerminal ≡ reachTerminal
terminalIsAbsorbing = refl

------------------------------------------------------------------------
-- Finite geometric-series witnesses.  They are compatible with later p-adic
-- completion but do not by themselves prove convergence in Q_3.

partialSum0 : Nat
partialSum0 = 1

partialSum1 : Nat
partialSum1 = 1 + 3

partialSum2 : Nat
partialSum2 = 1 + 3 + 9

partialSum3 : Nat
partialSum3 = 1 + 3 + 9 + 27

partialSum3IsForty : partialSum3 ≡ 40
partialSum3IsForty = refl

scaledGeometricIdentityAtDepthThree :
  2 * partialSum3 + 1 ≡ 81
scaledGeometricIdentityAtDepthThree = refl

record PadicCompletionObligation : Set where
  constructor padicCompletionObligation
  field
    completeNonArchimedeanFieldSupplied : Bool
    normOfThreeStrictlyBelowOneProved : Bool
    cauchyPartialSumsProved : Bool
    infiniteSeriesLimitIdentified : Bool

open PadicCompletionObligation public

currentPadicCompletionObligation : PadicCompletionObligation
currentPadicCompletionObligation =
  padicCompletionObligation false false false false

record FiniteResidueCycleReachabilityBoundary : Set where
  constructor finiteResidueCycleReachabilityBoundary
  field
    residueSixIsPositionalBaseSixNotation : Bool
    residueSixIsPositionalBaseSixNotationIsFalse :
      residueSixIsPositionalBaseSixNotation ≡ false

    residueNineIsNonaryIntegrationLogic : Bool
    residueNineIsNonaryIntegrationLogicIsFalse :
      residueNineIsNonaryIntegrationLogic ≡ false

    missingAdditiveInversesProveParaconsistency : Bool
    missingAdditiveInversesProveParaconsistencyIsFalse :
      missingAdditiveInversesProveParaconsistency ≡ false

    boundedReachabilityProvesUnboundedOverflowSemantics : Bool
    boundedReachabilityProvesUnboundedOverflowSemanticsIsFalse :
      boundedReachabilityProvesUnboundedOverflowSemantics ≡ false

    finitePartialSumsProveThreeAdicConvergence : Bool
    finitePartialSumsProveThreeAdicConvergenceIsFalse :
      finitePartialSumsProveThreeAdicConvergence ≡ false

open FiniteResidueCycleReachabilityBoundary public

canonicalFiniteResidueCycleReachabilityBoundary :
  FiniteResidueCycleReachabilityBoundary
canonicalFiniteResidueCycleReachabilityBoundary =
  finiteResidueCycleReachabilityBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
