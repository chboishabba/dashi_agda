{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345MixedOutputSupportRound848Exact where

------------------------------------------------------------------------
-- R848 / MINKOWSKI SUPPORT OF THE SIX-MODE 3-4-5 VELOCITY
--
-- Inside the radius-four cube, a pair of active velocity modes can sum only
-- to one of the eight selected forcing modes or to zero.  This closes the
-- support fact needed to remove all inactive outputs from the R692 sum.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNFixedOutputFiberThreeDOFRound72Exact as R72
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFullGramCoherentFoldRound597Exact as R597
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSupportMaxCutRound834Exact as Sparse
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot
import DASHI.Physics.Closure.NSTriadKNR650Rational345CanonicalStateRound838Exact as State838

F : C3.RealField _
F = Rational.rationalRealField

mixedLeftActive :
  (tau : Physical.PhysicalTriadIncidence) →
  Snapshot.mixedCellActive tau ≡ true →
  Snapshot.velocityActive (Physical.p tau) ≡ true
mixedLeftActive tau proof
  with Snapshot.velocityActive (Physical.p tau)
     | Snapshot.velocityActive (Physical.q tau)
... | true | true = refl
... | true | false with proof
...   | ()
... | false | q with proof
...   | ()

mixedRightActive :
  (tau : Physical.PhysicalTriadIncidence) →
  Snapshot.mixedCellActive tau ≡ true →
  Snapshot.velocityActive (Physical.q tau) ≡ true
mixedRightActive tau proof
  with Snapshot.velocityActive (Physical.p tau)
     | Snapshot.velocityActive (Physical.q tau)
... | true | true = refl
... | true | false with proof
...   | ()
... | false | q with proof
...   | ()

data SeedSumSupport (p q : Z3.FourierMode) : Set where
  selectedSum :
    Snapshot.forcingActive (Z3.addMode p q) ≡ true →
    SeedSumSupport p q
  zeroSum :
    Z3.addMode p q ≡ Z3.zeroMode →
    SeedSumSupport p q

seedSumSupport :
  (p q : Z3.FourierMode) →
  Snapshot.velocityActive p ≡ true →
  Snapshot.velocityActive q ≡ true →
  Physical.modeWithinCutoff 4 (Z3.addMode p q) ≡ true →
  SeedSumSupport p q
seedSumSupport p q pActive qActive within
  with State838.velocityActiveSound p pActive
     | State838.velocityActiveSound q qActive
... | State838.hit₁ pe | State838.hit₁ qe rewrite pe | qe =
      Output.falseNotTrue within
... | State838.hit₁ pe | State838.hit₂ qe rewrite pe | qe =
      Output.falseNotTrue within
... | State838.hit₁ pe | State838.hit₄ qe rewrite pe | qe =
      Output.falseNotTrue within
... | State838.hit₁ pe | State838.hit₅ qe rewrite pe | qe = selectedSum refl
... | State838.hit₁ pe | State838.hit₇ qe rewrite pe | qe = selectedSum refl
... | State838.hit₁ pe | State838.hit₈ qe rewrite pe | qe = zeroSum refl

... | State838.hit₂ pe | State838.hit₁ qe rewrite pe | qe =
      Output.falseNotTrue within
... | State838.hit₂ pe | State838.hit₂ qe rewrite pe | qe =
      Output.falseNotTrue within
... | State838.hit₂ pe | State838.hit₄ qe rewrite pe | qe = selectedSum refl
... | State838.hit₂ pe | State838.hit₅ qe rewrite pe | qe = selectedSum refl
... | State838.hit₂ pe | State838.hit₇ qe rewrite pe | qe = zeroSum refl
... | State838.hit₂ pe | State838.hit₈ qe rewrite pe | qe = selectedSum refl

... | State838.hit₄ pe | State838.hit₁ qe rewrite pe | qe =
      Output.falseNotTrue within
... | State838.hit₄ pe | State838.hit₂ qe rewrite pe | qe = selectedSum refl
... | State838.hit₄ pe | State838.hit₄ qe rewrite pe | qe =
      Output.falseNotTrue within
... | State838.hit₄ pe | State838.hit₅ qe rewrite pe | qe = zeroSum refl
... | State838.hit₄ pe | State838.hit₇ qe rewrite pe | qe = selectedSum refl
... | State838.hit₄ pe | State838.hit₈ qe rewrite pe | qe = selectedSum refl

... | State838.hit₅ pe | State838.hit₁ qe rewrite pe | qe = selectedSum refl
... | State838.hit₅ pe | State838.hit₂ qe rewrite pe | qe = selectedSum refl
... | State838.hit₅ pe | State838.hit₄ qe rewrite pe | qe = zeroSum refl
... | State838.hit₅ pe | State838.hit₅ qe rewrite pe | qe =
      Output.falseNotTrue within
... | State838.hit₅ pe | State838.hit₇ qe rewrite pe | qe = selectedSum refl
... | State838.hit₅ pe | State838.hit₈ qe rewrite pe | qe =
      Output.falseNotTrue within

... | State838.hit₇ pe | State838.hit₁ qe rewrite pe | qe = selectedSum refl
... | State838.hit₇ pe | State838.hit₂ qe rewrite pe | qe = zeroSum refl
... | State838.hit₇ pe | State838.hit₄ qe rewrite pe | qe = selectedSum refl
... | State838.hit₇ pe | State838.hit₅ qe rewrite pe | qe = selectedSum refl
... | State838.hit₇ pe | State838.hit₇ qe rewrite pe | qe =
      Output.falseNotTrue within
... | State838.hit₇ pe | State838.hit₈ qe rewrite pe | qe =
      Output.falseNotTrue within

... | State838.hit₈ pe | State838.hit₁ qe rewrite pe | qe = zeroSum refl
... | State838.hit₈ pe | State838.hit₂ qe rewrite pe | qe = selectedSum refl
... | State838.hit₈ pe | State838.hit₄ qe rewrite pe | qe = selectedSum refl
... | State838.hit₈ pe | State838.hit₅ qe rewrite pe | qe =
      Output.falseNotTrue within
... | State838.hit₈ pe | State838.hit₇ qe rewrite pe | qe =
      Output.falseNotTrue within
... | State838.hit₈ pe | State838.hit₈ qe rewrite pe | qe =
      Output.falseNotTrue within

selectedMixedCellOutputSupport :
  ∀ {output tau} →
  tau Cube.∈ Output.physicalOutputFiber 4 output →
  Snapshot.mixedCellActive tau ≡ true →
  (Snapshot.forcingActive output ≡ true) ⊎ (output ≡ Z3.zeroMode)
selectedMixedCellOutputSupport {output} {tau} member selected =
  let
    sourceMember =
      R72.physicalOutputFiberMemberInEnumeration member
    withinK =
      Physical.enumeratedOutputWithin sourceMember
    withinSum :
      Physical.modeWithinCutoff 4
        (Z3.addMode (Physical.p tau) (Physical.q tau))
      ≡ true
    withinSum =
      subst
        (λ mode → Physical.modeWithinCutoff 4 mode ≡ true)
        (sym (Physical.resonance tau))
        withinK
    support =
      seedSumSupport
        (Physical.p tau) (Physical.q tau)
        (mixedLeftActive tau selected)
        (mixedRightActive tau selected)
        withinSum
    outputEq = Output.physicalOutputFiberSound member
  in
  case support outputEq
  where
  case :
    SeedSumSupport (Physical.p tau) (Physical.q tau) →
    Physical.k tau ≡ output →
    (Snapshot.forcingActive output ≡ true) ⊎
      (output ≡ Z3.zeroMode)
  case (selectedSum active) outputEq =
    inj₁
      (subst
        (λ mode → Snapshot.forcingActive mode ≡ true)
        (trans (Physical.resonance tau) outputEq)
        active)
  case (zeroSum zero) outputEq =
    inj₂
      (trans
        (sym outputEq)
        (trans
          (sym (Physical.resonance tau))
          zero))

filterSelectedEmpty :
  (select : Physical.PhysicalTriadIncidence → Bool) →
  (items : List Physical.PhysicalTriadIncidence) →
  ((tau : Physical.PhysicalTriadIncidence) →
    tau Cube.∈ items → select tau ≡ false) →
  Sparse.filterSelected select items ≡ []
filterSelectedEmpty select [] allFalse = refl
filterSelectedEmpty select (tau ∷ rest) allFalse
  with select tau in decision
... | true =
  Output.falseNotTrue
    (trans
      (sym (allFalse tau (Cube.here refl)))
      decision)
... | false =
  filterSelectedEmpty select rest
    (λ selected member → allFalse selected (Cube.there member))

mixedFilterEmptyAtInactiveNonzero :
  (output : Z3.FourierMode) →
  Z3.NonZeroMode output →
  Snapshot.forcingActive output ≡ false →
  Sparse.filterSelected Snapshot.mixedCellActive
    (Output.physicalOutputFiber 4 output)
  ≡ []
mixedFilterEmptyAtInactiveNonzero output outputNonzero inactive =
  filterSelectedEmpty
    Snapshot.mixedCellActive
    (Output.physicalOutputFiber 4 output)
    reject
  where
  reject :
    (tau : Physical.PhysicalTriadIncidence) →
    tau Cube.∈ Output.physicalOutputFiber 4 output →
    Snapshot.mixedCellActive tau ≡ false
  reject tau member
    with Snapshot.mixedCellActive tau in decision
  ... | false = refl
  ... | true with selectedMixedCellOutputSupport member decision
  ...   | inj₁ active =
        Output.falseNotTrue (trans (sym inactive) active)
  ...   | inj₂ zero =
        ⊥-elim (Z3.notZero outputNonzero zero)

mixedFixedOutputZeroAtInactiveNonzero :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (output : Z3.FourierMode) →
  Z3.NonZeroMode output →
  Snapshot.forcingActive output ≡ false →
  Work.fixedOutputMixedProduct
    Active.selected345HelicalScalars
    Snapshot.velocity345 4 output
  ≡ C3.complex3Zero F
mixedFixedOutputZeroAtInactiveNonzero output nonzero inactive =
  trans
    (Snapshot.pruneMixed345
      (Output.physicalOutputFiber 4 output))
    (cong
      (R224.foldVector
        (R224.mixedPlusMinus
          Active.selected345HelicalScalars Snapshot.velocity345))
      (mixedFilterEmptyAtInactiveNonzero output nonzero inactive))

coherentWorkZeroAtInactiveNonzero :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (forcing : Z3.FourierMode → C3.Complex3 F) →
  (output : Z3.FourierMode) →
  Z3.NonZeroMode output →
  Snapshot.forcingActive output ≡ false →
  Work.coherentWork
    (Work.fixedOutputMixedProduct
      Active.selected345HelicalScalars
      Snapshot.velocity345 4 output)
    (Work.fixedOutputCommutator
      Active.selected345HelicalScalars
      Snapshot.velocity345 forcing 4 output)
  ≡ 0
coherentWorkZeroAtInactiveNonzero forcing output nonzero inactive
  rewrite mixedFixedOutputZeroAtInactiveNonzero output nonzero inactive =
  R597.workZeroLeft
    (Work.fixedOutputCommutator
      Active.selected345HelicalScalars
      Snapshot.velocity345 forcing 4 output)

round848SeedMinkowskiSupportClosed : Bool
round848SeedMinkowskiSupportClosed = true

round848InactiveNonzeroMixedOutputsVanish : Bool
round848InactiveNonzeroMixedOutputsVanish = true

round848InactiveNonzeroCoherentWorkVanishes : Bool
round848InactiveNonzeroCoherentWorkVanishes = true

round848ClayPromotion : Bool
round848ClayPromotion = false
