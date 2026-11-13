{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345NonzeroSupportRound848Exact where

------------------------------------------------------------------------
-- R848 / REPAIRED R846 NONZERO SUPPORT THEOREM, ACTUAL FINITE SOURCE.
--
-- The literal selected velocity support has SIX Fourier modes.
-- Its complete 6x6 Cartesian seed-pair table has 36 ordered entries.
-- Exactly 22 of those pairs have output within [-4,4]^3:
-- 16 have one of the eight nonzero 3-4-5 output modes; SIX have k=0.
--
-- R847 proves the ORIGINAL all-mode empty-active-fibre premise FALSE
-- at zero. This module closes its correct NONZERO form using:
--   * the real Z3.addMode on literal six source modes,
--   * the real Physical.modeWithinCutoff 4 predicate,
--   * the real Snapshot.forcingActive classifier,
--   * existing State838.velocityActiveSound membership evidence,
--   * original physicalTriadEnumeration/output-fibre membership.
--
-- It does NOT evaluate the remaining active R224/R230 helical folds,
-- identify real finite-ODE trajectories, or prove NS global regularity.
-- The final R846 module reuses the pre-existing R436 transverse
-- zero-output theorem instead of pretending six zero-output cells absent.
--
-- No postulate, abstract Set-valued oracle or independent model.
-- SOURCE-WRITTEN. Requires pinned local Agda 2.9 kernel checking.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (sym; trans; subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot
import DASHI.Physics.Closure.NSTriadKNR650Rational345CanonicalStateRound838Exact as State838
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSupportMaxCutRound834Exact as Sparse
import DASHI.Physics.Closure.NSTriadKNR650Rational345ForcingSupportMaxCutRound846Exact as R846

SeedPair : Set
SeedPair = Cube.Pair Z3.FourierMode Z3.FourierMode

seedModes : List Z3.FourierMode
seedModes =
  Active.k₁ ∷ Active.k₂ ∷ Active.k₄ ∷
  Active.k₅ ∷ Active.k₇ ∷ Active.k₈ ∷ []

seedPairs : List SeedPair
seedPairs = Cube.cartesian seedModes seedModes

seedPairCountExact : Cube.length seedPairs ≡ 36
seedPairCountExact = refl

pairSum : SeedPair → Z3.FourierMode
pairSum pair = Z3.addMode (Cube.first pair) (Cube.second pair)

-- Eligibility is not asserted for zero output or out-of-cutoff sums.
pairOutputLegal : SeedPair → Bool
pairOutputLegal pair
  with Physical.modeWithinCutoff 4 (pairSum pair)
... | false = true
... | true with Output.modeEqual (pairSum pair) Z3.zeroMode
...   | true = true
...   | false = Snapshot.forcingActive (pairSum pair)

allLegal : List SeedPair → Bool
allLegal [] = true
allLegal (pair ∷ rest) with pairOutputLegal pair
... | true = allLegal rest
... | false = false

-- Exact 36-pair computation using the ORIGINAL Fourier/forcing functions.
allThirtySixSeedPairOutputsLegal : allLegal seedPairs ≡ true
allThirtySixSeedPairOutputsLegal = refl

allLegalMember :
  (items : List SeedPair) →
  (pair : SeedPair) →
  allLegal items ≡ true →
  pair Cube.∈ items →
  pairOutputLegal pair ≡ true
allLegalMember [] pair valid ()
allLegalMember (head ∷ rest) pair valid member
  with pairOutputLegal head in choice | member
... | true | Cube.here equality =
  subst (λ selected → pairOutputLegal selected ≡ true)
    (sym equality) choice
... | true | Cube.there tail =
  allLegalMember rest pair valid tail
... | false | _ = Output.falseNotTrue valid

sourcePairWithinCutoffNonzeroIsForcingActive :
  (pair : SeedPair) →
  pair Cube.∈ seedPairs →
  Physical.modeWithinCutoff 4 (pairSum pair) ≡ true →
  Output.modeEqual (pairSum pair) Z3.zeroMode ≡ false →
  Snapshot.forcingActive (pairSum pair) ≡ true
sourcePairWithinCutoffNonzeroIsForcingActive
  pair member within nonzero
  rewrite within | nonzero =
    allLegalMember seedPairs pair allThirtySixSeedPairOutputsLegal member

sourceVelocityActiveIsSeedMember :
  (mode : Z3.FourierMode) →
  Snapshot.velocityActive mode ≡ true →
  mode Cube.∈ seedModes
sourceVelocityActiveIsSeedMember mode active
  with State838.velocityActiveSound mode active
... | State838.hit₁ equality = Cube.here equality
... | State838.hit₂ equality = Cube.there (Cube.here equality)
... | State838.hit₄ equality =
  Cube.there (Cube.there (Cube.here equality))
... | State838.hit₅ equality =
  Cube.there (Cube.there (Cube.there (Cube.here equality)))
... | State838.hit₇ equality =
  Cube.there (Cube.there (Cube.there (Cube.there (Cube.here equality))))
... | State838.hit₈ equality =
  Cube.there (Cube.there (Cube.there (Cube.there
    (Cube.there (Cube.here equality)))))

selectedMixedLeft :
  (tau : Physical.PhysicalTriadIncidence) →
  Snapshot.mixedCellActive tau ≡ true →
  Snapshot.velocityActive (Physical.p tau) ≡ true
selectedMixedLeft tau active
  with Snapshot.velocityActive (Physical.p tau)
... | true = refl
... | false = Output.falseNotTrue active

selectedMixedRight :
  (tau : Physical.PhysicalTriadIncidence) →
  Snapshot.mixedCellActive tau ≡ true →
  Snapshot.velocityActive (Physical.q tau) ≡ true
selectedMixedRight tau active
  with Snapshot.velocityActive (Physical.p tau)
     | Snapshot.velocityActive (Physical.q tau)
... | true | true = refl
... | true | false = Output.falseNotTrue active
... | false | _ = Output.falseNotTrue active

selectedTriadPairIsSeedPair :
  (tau : Physical.PhysicalTriadIncidence) →
  Snapshot.mixedCellActive tau ≡ true →
  (Cube.pair (Physical.p tau) (Physical.q tau)) Cube.∈ seedPairs
selectedTriadPairIsSeedPair tau selected =
  Cube.cartesianComplete
    (sourceVelocityActiveIsSeedMember
      (Physical.p tau) (selectedMixedLeft tau selected))
    (sourceVelocityActiveIsSeedMember
      (Physical.q tau) (selectedMixedRight tau selected))

-- Source filter does not invent physical triads.
outputFilterMemberInOriginal :
  ∀ {output tau items} →
  tau Cube.∈ Output.filterOutput output items →
  tau Cube.∈ items
outputFilterMemberInOriginal {items = []} ()
outputFilterMemberInOriginal {output} {items = x ∷ rest} member
  with Output.modeEqual (Physical.k x) output in selected | member
... | true | Cube.here equality = Cube.here equality
... | true | Cube.there tail =
  Cube.there (outputFilterMemberInOriginal tail)
... | false | tail =
  Cube.there (outputFilterMemberInOriginal tail)

-- Generic selective list elimination: every retained head is impossible.
selectedFilterEmpty :
  (items : List Physical.PhysicalTriadIncidence) →
  ((tau : Physical.PhysicalTriadIncidence) →
    tau Cube.∈ items →
    Snapshot.mixedCellActive tau ≡ true → ⊥) →
  Sparse.filterSelected Snapshot.mixedCellActive items ≡ []
selectedFilterEmpty [] reject = refl
selectedFilterEmpty (head ∷ rest) reject
  with Snapshot.mixedCellActive head in selected
... | true =
  ⊥-elim (reject head (Cube.here refl) selected)
... | false =
  selectedFilterEmpty rest
    (λ tau member isSelected →
      reject tau (Cube.there member) isSelected)

-- F1 positive theorem for ALL Fourier outputs, excluding k=0 alone.
-- Every selected original triad's inputs belong to the ACTUAL six seed
-- modes; its sum is in the original cutoff 4 cube; the 36-pair finite
-- computation says every nonzero such sum is one of the eight forcing modes.
inactiveNonzeroFibreEmpty : R846.InactiveActiveFibreEmpty
inactiveNonzeroFibreEmpty output inactive nonzero =
  selectedFilterEmpty
    (Output.physicalOutputFiber 4 output)
    impossible
  where
  impossible :
    (tau : Physical.PhysicalTriadIncidence) →
    tau Cube.∈ Output.physicalOutputFiber 4 output →
    Snapshot.mixedCellActive tau ≡ true → ⊥
  impossible tau inFibre selected =
    let
      sourceMember : tau Cube.∈ Physical.physicalTriadEnumeration 4
      sourceMember = outputFilterMemberInOriginal inFibre

      outputWithin :
        Physical.modeWithinCutoff 4 (Physical.k tau) ≡ true
      outputWithin =
        Physical.enumeratedOutputWithin
          {N = 4}
          {pairs = Cube.cartesian (Cube.cutoffModes 4) (Cube.cutoffModes 4)}
          sourceMember

      sourceSumEqualsOutput :
        Z3.addMode (Physical.p tau) (Physical.q tau) ≡ output
      sourceSumEqualsOutput =
        trans (Physical.resonance tau)
          (Output.physicalOutputFiberSound inFibre)

      sourcePair : SeedPair
      sourcePair = Cube.pair (Physical.p tau) (Physical.q tau)

      sourcePairMember : sourcePair Cube.∈ seedPairs
      sourcePairMember = selectedTriadPairIsSeedPair tau selected

      sumWithin : Physical.modeWithinCutoff 4 (pairSum sourcePair) ≡ true
      sumWithin =
        subst
          (λ k → Physical.modeWithinCutoff 4 k ≡ true)
          (sym (Physical.resonance tau))
          outputWithin

      sumNonzero :
        Output.modeEqual (pairSum sourcePair) Z3.zeroMode ≡ false
      sumNonzero =
        subst
          (λ k → Output.modeEqual k Z3.zeroMode ≡ false)
          (sym sourceSumEqualsOutput) nonzero

      sourceActive :
        Snapshot.forcingActive (pairSum sourcePair) ≡ true
      sourceActive =
        sourcePairWithinCutoffNonzeroIsForcingActive
          sourcePair sourcePairMember sumWithin sumNonzero

      outputActive : Snapshot.forcingActive output ≡ true
      outputActive =
        subst (λ k → Snapshot.forcingActive k ≡ true)
          sourceSumEqualsOutput sourceActive
    in
    Output.falseNotTrue (trans (sym inactive) outputActive)

-- R846's caller may now supply R848.inactiveNonzeroFibreEmpty.
-- Its zero-mode branch must use R436; that path is wired in repaired R846.
