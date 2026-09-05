module DASHI.Physics.Plasma.LoureiroHermiteClosureReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Viriato/KREHM Hermite chain.  Infinite expansion is formally equivalent to
-- the kinetic representation; finite numerical M requires a closure for g_{M+1}.

data HermiteIndexRole : Set where retainedInterior terminalRetained firstDiscarded : HermiteIndexRole

data ClosureKind : Set where hardZero hyperCollision asymptoticTail userSpecified : ClosureKind

record HermiteTerminalState : Set where
  constructor hermite-terminal-state
  field
    terminalIndex : Nat
    terminalMoment : String
    discardedNeighbour : String
    closure : ClosureKind
    closureFormula : String
    collisionOperator : String
    sourceReference : String

open HermiteTerminalState public

record HermiteClosureReceipt : Set where
  constructor hermite-closure-receipt
  field
    state : HermiteTerminalState
    lowerMomentsCoupleToNeighbours : Bool
    lowerMomentsCoupleToNeighboursIsTrue : lowerMomentsCoupleToNeighbours ≡ true
    terminalEquationReferencesDiscardedNeighbourBeforeClosure : Bool
    terminalEquationReferencesDiscardedNeighbourBeforeClosureIsTrue :
      terminalEquationReferencesDiscardedNeighbourBeforeClosure ≡ true
    closureInsertedBeforeFiniteEvolutionClosed : Bool
    closureInsertedBeforeFiniteEvolutionClosedIsTrue :
      closureInsertedBeforeFiniteEvolutionClosed ≡ true

open HermiteClosureReceipt public

record HermiteClosureBoundary : Set where
  constructor hermite-closure-boundary
  field
    finiteMIsDefinitionallyExactKineticState : Bool
    finiteMIsDefinitionallyExactKineticStateIsFalse : finiteMIsDefinitionallyExactKineticState ≡ false
    gMPlusOneCanBeIgnoredWithoutAClosureChoice : Bool
    gMPlusOneCanBeIgnoredWithoutAClosureChoiceIsFalse : gMPlusOneCanBeIgnoredWithoutAClosureChoice ≡ false
    closureChoiceCannotAffectDissipationTail : Bool
    closureChoiceCannotAffectDissipationTailIsFalse : closureChoiceCannotAffectDissipationTail ≡ false
    convergenceNeedsMomentOrTailStudy : Bool
    convergenceNeedsMomentOrTailStudyIsTrue : convergenceNeedsMomentOrTailStudy ≡ true

canonicalHermiteClosureBoundary : HermiteClosureBoundary
canonicalHermiteClosureBoundary = hermite-closure-boundary false refl false refl false refl true refl
