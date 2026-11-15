{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345ZeroOutputSupportCounterexampleRound847Exact where

------------------------------------------------------------------------
-- R847 / ACTUAL REPOSITORY ZERO-OUTPUT SUPPORT COUNTEREXAMPLE.
--
-- This is a constructive source-specific no-go for the OLD R846
-- InactiveActiveFibreEmpty proposition, not an NS blow-up assertion.
--
-- The six selected 3-4-5 velocity modes include the opposite pair
-- p=(-3,-4,0) and q=(3,4,0). The actual cutoff-4 physical triad
-- enumerator includes (p,q,k=0), and the original mixedCellActive
-- selector retains it. Yet forcingActive 0 = false.
--
-- Thus the old assertion
--   forcingActive k = false ->
--   filterSelected mixedCellActive (physicalOutputFiber 4 k) = []
-- is FALSE at k=0. It cannot be supplied as a source certificate.
--
-- The actual projected forcing AT k=0 still vanishes by the already
-- established Round436 transversality argument (NOT by empty fibre).
-- This module proves the nonemptiness of the real source-selected list.
--
-- The required R846 repair treats zero output separately and limits
-- the remaining finite support-empty condition to k != 0.
--
-- Agda local-kernel receipt still required; no external axiom.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSupportMaxCutRound834Exact as Sparse

zeroPair : Cube.Pair Z3.FourierMode Z3.FourierMode
zeroPair = Cube.pair Active.k₁ Active.k₈

zeroPairSumIsZero : Z3.addMode Active.k₁ Active.k₈ ≡ Z3.zeroMode
zeroPairSumIsZero = refl

zeroTriad : Physical.PhysicalTriadIncidence
zeroTriad = Physical.pairTriad zeroPair

leftSeedInActualCutoff : Active.k₁ Cube.∈ Cube.cutoffModes 4
leftSeedInActualCutoff =
  Cube.cutoffModeEnumerationComplete 4 Active.k₁
    (Physical.modeWithinCutoffSound 4 Active.k₁ refl)

rightSeedInActualCutoff : Active.k₈ Cube.∈ Cube.cutoffModes 4
rightSeedInActualCutoff =
  Cube.cutoffModeEnumerationComplete 4 Active.k₈
    (Physical.modeWithinCutoffSound 4 Active.k₈ refl)

actualSelectedPairEnumerated :
  zeroPair Cube.∈
    Cube.cartesian (Cube.cutoffModes 4) (Cube.cutoffModes 4)
actualSelectedPairEnumerated =
  Cube.cartesianComplete
    leftSeedInActualCutoff rightSeedInActualCutoff

actualZeroTriadEnumerated :
  zeroTriad Cube.∈ Physical.physicalTriadEnumeration 4
actualZeroTriadEnumerated =
  Physical.enumerateFromPairsComplete
    actualSelectedPairEnumerated refl

actualZeroTriadInOutputFiber :
  zeroTriad Cube.∈ Output.physicalOutputFiber 4 Z3.zeroMode
actualZeroTriadInOutputFiber =
  Output.physicalOutputFiberComplete
    actualZeroTriadEnumerated zeroPairSumIsZero

actualZeroTriadSelected : Snapshot.mixedCellActive zeroTriad ≡ true
actualZeroTriadSelected = refl

selectedMember :
  ∀ {items : List Physical.PhysicalTriadIncidence}
    {tau : Physical.PhysicalTriadIncidence} →
  tau Cube.∈ items →
  Snapshot.mixedCellActive tau ≡ true →
  tau Cube.∈ Sparse.filterSelected Snapshot.mixedCellActive items
selectedMember {items = []} () selected
selectedMember {items = x ∷ xs} (Cube.here refl) selected
  rewrite selected = Cube.here refl
selectedMember {items = x ∷ xs} (Cube.there member) selected
  with Snapshot.mixedCellActive x
... | true = Cube.there (selectedMember member selected)
... | false = selectedMember member selected

actualZeroSelectedFibreNonempty :
  zeroTriad Cube.∈
    Sparse.filterSelected Snapshot.mixedCellActive
      (Output.physicalOutputFiber 4 Z3.zeroMode)
actualZeroSelectedFibreNonempty =
  selectedMember actualZeroTriadInOutputFiber actualZeroTriadSelected

actualZeroForcingClassifierIsInactive :
  Snapshot.forcingActive Z3.zeroMode ≡ false
actualZeroForcingClassifierIsInactive = refl

noMemberOfEmpty :
  ∀ {A : Set} {x : A} → x Cube.∈ [] → ⊥
noMemberOfEmpty ()

-- Constructive refutation of the exact old R846 F1 proposition.
originalR846AllModeSupportEmptyIsFalse :
  ((mode : Z3.FourierMode) →
    Snapshot.forcingActive mode ≡ false →
    Sparse.filterSelected Snapshot.mixedCellActive
      (Output.physicalOutputFiber 4 mode) ≡ []) →
  ⊥
originalR846AllModeSupportEmptyIsFalse oldF1 =
  noMemberOfEmpty
    (subst
      (λ items → zeroTriad Cube.∈ items)
      (oldF1 Z3.zeroMode actualZeroForcingClassifierIsInactive)
      actualZeroSelectedFibreNonempty)
