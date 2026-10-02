{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345ForcingSupportExhaustionRound848Exact where

------------------------------------------------------------------------
-- R848 / FINITE SIX-SEED PAIR-SUM EXHAUSTION FOR THE CORRECTED F1' LEAF
--
-- R847 observes that R846's original list-emptiness target is too strong at
-- output zero: reality-paired active seeds contribute incidences p+(-p)=0,
-- although every literal R30 ordered interaction there is zero by R436.
--
-- For nonzero output, the finite support statement is exact.  The six active
-- velocity modes are
--   k1,k2,k4,k5,k7,k8.
-- Exhausting the 6 x 6 ordered sums shows:
--
--   * sums outside the radius-four cube cannot occur in the physical fibre;
--   * in-cube sums are exactly zero or one of forcing-active k1..k8.
--
-- Hence an output which is BOTH forcing-inactive and nonzero has no selected
-- active seed-seed incidence.  This closes R847's corrected F1' combinatorial
-- leaf.  No vector arithmetic, helicity evaluation, estimate or trajectory is
-- used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberConjugationRound35Exact as Fibre35
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot
import DASHI.Physics.Closure.NSTriadKNR650Rational345CanonicalStateRound838Exact as State838
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSupportMaxCutRound834Exact as Sparse
import DASHI.Physics.Closure.NSTriadKNR650Rational345ForcingSupportZeroOutputRound847Exact as R847

data SeedOutputClass (mode : Z3.FourierMode) : Set where
  outputZero :
    mode ≡ Z3.zeroMode →
    SeedOutputClass mode
  outputForcingActive :
    Snapshot.forcingActive mode ≡ true →
    SeedOutputClass mode

------------------------------------------------------------------------
-- Literal 6 x 6 ordered seed-pair sum table.
-- Impossible clauses are exactly the pair sums leaving the radius-four cube.
------------------------------------------------------------------------

activePairOutputClass :
  ∀ {p q} →
  State838.VelocityActiveHit p →
  State838.VelocityActiveHit q →
  Physical.modeWithinCutoff 4 (Z3.addMode p q) ≡ true →
  SeedOutputClass (Z3.addMode p q)

activePairOutputClass (State838.hit₁ refl) (State838.hit₁ refl) ()
activePairOutputClass (State838.hit₁ refl) (State838.hit₂ refl) ()
activePairOutputClass (State838.hit₁ refl) (State838.hit₄ refl) ()
activePairOutputClass (State838.hit₁ refl) (State838.hit₅ refl) within =
  outputForcingActive refl
activePairOutputClass (State838.hit₁ refl) (State838.hit₇ refl) within =
  outputForcingActive refl
activePairOutputClass (State838.hit₁ refl) (State838.hit₈ refl) within =
  outputZero refl

activePairOutputClass (State838.hit₂ refl) (State838.hit₁ refl) ()
activePairOutputClass (State838.hit₂ refl) (State838.hit₂ refl) ()
activePairOutputClass (State838.hit₂ refl) (State838.hit₄ refl) within =
  outputForcingActive refl
activePairOutputClass (State838.hit₂ refl) (State838.hit₅ refl) within =
  outputForcingActive refl
activePairOutputClass (State838.hit₂ refl) (State838.hit₇ refl) within =
  outputZero refl
activePairOutputClass (State838.hit₂ refl) (State838.hit₈ refl) within =
  outputForcingActive refl

activePairOutputClass (State838.hit₄ refl) (State838.hit₁ refl) ()
activePairOutputClass (State838.hit₄ refl) (State838.hit₂ refl) within =
  outputForcingActive refl
activePairOutputClass (State838.hit₄ refl) (State838.hit₄ refl) ()
activePairOutputClass (State838.hit₄ refl) (State838.hit₅ refl) within =
  outputZero refl
activePairOutputClass (State838.hit₄ refl) (State838.hit₇ refl) within =
  outputForcingActive refl
activePairOutputClass (State838.hit₄ refl) (State838.hit₈ refl) within =
  outputForcingActive refl

activePairOutputClass (State838.hit₅ refl) (State838.hit₁ refl) within =
  outputForcingActive refl
activePairOutputClass (State838.hit₅ refl) (State838.hit₂ refl) within =
  outputForcingActive refl
activePairOutputClass (State838.hit₅ refl) (State838.hit₄ refl) within =
  outputZero refl
activePairOutputClass (State838.hit₅ refl) (State838.hit₅ refl) ()
activePairOutputClass (State838.hit₅ refl) (State838.hit₇ refl) within =
  outputForcingActive refl
activePairOutputClass (State838.hit₅ refl) (State838.hit₈ refl) ()

activePairOutputClass (State838.hit₇ refl) (State838.hit₁ refl) within =
  outputForcingActive refl
activePairOutputClass (State838.hit₇ refl) (State838.hit₂ refl) within =
  outputZero refl
activePairOutputClass (State838.hit₇ refl) (State838.hit₄ refl) within =
  outputForcingActive refl
activePairOutputClass (State838.hit₇ refl) (State838.hit₅ refl) within =
  outputForcingActive refl
activePairOutputClass (State838.hit₇ refl) (State838.hit₇ refl) ()
activePairOutputClass (State838.hit₇ refl) (State838.hit₈ refl) ()

activePairOutputClass (State838.hit₈ refl) (State838.hit₁ refl) within =
  outputZero refl
activePairOutputClass (State838.hit₈ refl) (State838.hit₂ refl) within =
  outputForcingActive refl
activePairOutputClass (State838.hit₈ refl) (State838.hit₄ refl) within =
  outputForcingActive refl
activePairOutputClass (State838.hit₈ refl) (State838.hit₅ refl) ()
activePairOutputClass (State838.hit₈ refl) (State838.hit₇ refl) ()
activePairOutputClass (State838.hit₈ refl) (State838.hit₈ refl) ()

mixedActiveP :
  (tau : Physical.PhysicalTriadIncidence) →
  Snapshot.mixedCellActive tau ≡ true →
  Snapshot.velocityActive (Physical.p tau) ≡ true
mixedActiveP tau selected
  with Snapshot.velocityActive (Physical.p tau)
     | Snapshot.velocityActive (Physical.q tau)
... | true | q = refl
... | false | q = Output.falseNotTrue selected

mixedActiveQ :
  (tau : Physical.PhysicalTriadIncidence) →
  Snapshot.mixedCellActive tau ≡ true →
  Snapshot.velocityActive (Physical.q tau) ≡ true
mixedActiveQ tau selected
  with Snapshot.velocityActive (Physical.p tau)
     | Snapshot.velocityActive (Physical.q tau)
... | true | true = refl
... | true | false = Output.falseNotTrue selected
... | false | q = Output.falseNotTrue selected

selectedFibreOutputClass :
  ∀ {mode tau} →
  tau Cube.∈ Output.physicalOutputFiber 4 mode →
  Snapshot.mixedCellActive tau ≡ true →
  SeedOutputClass mode
selectedFibreOutputClass {mode} {tau} member selected =
  subst SeedOutputClass outputEquality pairClass
  where
  globalMember :
    tau Cube.∈ Physical.physicalTriadEnumeration 4
  globalMember = Fibre35.physicalOutputFiberMemberEnumeration member

  outputWithin :
    Physical.modeWithinCutoff 4 (Physical.k tau) ≡ true
  outputWithin = Physical.enumeratedOutputWithin globalMember

  sumWithin :
    Physical.modeWithinCutoff 4
      (Z3.addMode (Physical.p tau) (Physical.q tau)) ≡ true
  sumWithin =
    subst
      (λ output → Physical.modeWithinCutoff 4 output ≡ true)
      (sym (Physical.resonance tau))
      outputWithin

  pHit : State838.VelocityActiveHit (Physical.p tau)
  pHit =
    State838.velocityActiveSound
      (Physical.p tau) (mixedActiveP tau selected)

  qHit : State838.VelocityActiveHit (Physical.q tau)
  qHit =
    State838.velocityActiveSound
      (Physical.q tau) (mixedActiveQ tau selected)

  pairClass :
    SeedOutputClass
      (Z3.addMode (Physical.p tau) (Physical.q tau))
  pairClass = activePairOutputClass pHit qHit sumWithin

  outputEquality :
    Z3.addMode (Physical.p tau) (Physical.q tau) ≡ mode
  outputEquality =
    trans
      (Physical.resonance tau)
      (Output.physicalOutputFiberSound member)

selectedImpossibleAtInactiveNonzero :
  ∀ {mode tau} →
  Snapshot.forcingActive mode ≡ false →
  Output.modeEqual mode Z3.zeroMode ≡ false →
  tau Cube.∈ Output.physicalOutputFiber 4 mode →
  Snapshot.mixedCellActive tau ≡ true →
  ⊥
selectedImpossibleAtInactiveNonzero
    {mode} inactive nonzero member selected
  with selectedFibreOutputClass member selected
... | outputZero same =
    Output.falseNotTrue
      (trans
        (sym nonzero)
        (Output.modeEqualComplete same))
... | outputForcingActive active =
    Output.falseNotTrue
      (trans (sym inactive) active)

filterEmptyWhenNoSelected :
  (select : Physical.PhysicalTriadIncidence → Bool) →
  (items : List Physical.PhysicalTriadIncidence) →
  ((tau : Physical.PhysicalTriadIncidence) →
    tau Cube.∈ items →
    select tau ≡ true →
    ⊥) →
  Sparse.filterSelected select items ≡ []
filterEmptyWhenNoSelected select [] impossible = refl
filterEmptyWhenNoSelected select (tau ∷ rest) impossible
  with select tau in decision
... | true =
    ⊥-elim
      (impossible tau (Cube.here refl) decision)
... | false =
    filterEmptyWhenNoSelected select rest
      (λ selected member active →
        impossible selected (Cube.there member) active)

inactiveNonzeroActiveFibreEmpty :
  R847.InactiveNonzeroActiveFibreEmpty
inactiveNonzeroActiveFibreEmpty mode inactive nonzero =
  filterEmptyWhenNoSelected
    Snapshot.mixedCellActive
    (Output.physicalOutputFiber 4 mode)
    (λ tau member active →
      selectedImpossibleAtInactiveNonzero
        inactive nonzero member active)

round848SixBySixSeedPairSupportExhausted : Bool
round848SixBySixSeedPairSupportExhausted = true

round848ZeroOutputExplicitlySeparated : Bool
round848ZeroOutputExplicitlySeparated = true

round848InactiveNonzeroSupportEmptyClosed : Bool
round848InactiveNonzeroSupportEmptyClosed = true

round848F1CorrectedClosed : Bool
round848F1CorrectedClosed = true

round848OnlyActiveR224R230VectorEvaluationRemains : Bool
round848OnlyActiveR224R230VectorEvaluationRemains = true

round848AdditionalAnalyticEstimateRequired : Bool
round848AdditionalAnalyticEstimateRequired = false

round848ClayPromotion : Bool
round848ClayPromotion = false

round848F1CorrectedClosedIsTrue :
  round848F1CorrectedClosed ≡ true
round848F1CorrectedClosedIsTrue = refl

round848OnlyActiveR224R230VectorEvaluationRemainsIsTrue :
  round848OnlyActiveR224R230VectorEvaluationRemains ≡ true
round848OnlyActiveR224R230VectorEvaluationRemainsIsTrue = refl
