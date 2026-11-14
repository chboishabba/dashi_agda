module DASHI.Physics.YangMills.YMClayNativeOriginalSortDeciderExact where

------------------------------------------------------------------------
-- R443.F07 / R445.F21: CLOSED FINITE PROOF-RELEVANT DECISION PROCEDURE.
--
-- Reuse the exact selected native Bond, originalSorter and its
-- membership-indexed correctness proof. Decide EVERY intermediate
-- selection without inventing a permutation or a field. A successful
-- closed Boolean check yields the ORIGINAL canonical vector equality,
-- not a bare Set-valued field or a new assumed 1024-vector identity.
--
-- The booleans for native C3 and pair/spectator remain literal CLOSED
-- computational goals: source-written; kernel normalization pending.
-- This is finite original geometry only, NOT Haar/RG/CMP116/OS/Clay.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Vec.Base as Vec

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.YMClayNativeC3AdjacentSortProgramExact as Sort
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Single
import DASHI.Physics.YangMills.YMClayNativeSideFourC3VectorWeldExact as C3
import DASHI.Physics.YangMills.YMClayNativeOriginalSortMembershipCorrectExact as Proof
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClayNativeSideFourPairSpectatorSortProgramExact as Pairs
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN

-- The native finite Bond membership is DECIDABLE using exactly the old
-- originalBondDecide, with constructive negative evidence.
decideNativeMember :
  ∀ {n} (wanted : Sort.Bond) (source : Vec.Vec Sort.Bond n) →
  Torus.Dec (wanted Proof.∈ᵛ source)
decideNativeMember wanted Vec.[] =
  Torus.no (λ ())
decideNativeMember wanted (head Vec.∷ tail)
  with Sort.originalBondDecide wanted head
... | Torus.yes refl = Torus.yes Proof.here
... | Torus.no notHead with decideNativeMember wanted tail
... | Torus.yes inTail = Torus.yes (Proof.there inTail)
... | Torus.no notTail = Torus.no λ
  { Proof.here → notHead refl
  ; (Proof.there inTail) → notTail inTail
  }

-- Verify the precise original stepwise membership invariant; rejection
-- means the requested target cannot be certified by THIS selected sort.
decideAllSelectable :
  ∀ {n} (target source : Vec.Vec Sort.Bond n) →
  Torus.Dec (Proof.AllSelectable target source)
decideAllSelectable Vec.[] Vec.[] =
  Torus.yes Proof.done
decideAllSelectable (wanted Vec.∷ targetTail) source
  with decideNativeMember wanted source
... | Torus.no notPresent = Torus.no λ
  { (Proof.select member _) → notPresent member }
... | Torus.yes member with
    decideAllSelectable targetTail
      (Sort.originalTail
        (Product.permuteLinks
          (Sort.originalBubbleDesired wanted source) source))
... | Torus.yes ready = Torus.yes (Proof.select member ready)
... | Torus.no notReady = Torus.no λ
  { (Proof.select _ ready) → notReady ready }

-- Turn a fully COMPUTED yes/no decision into a small explicit Boolean.
-- Only proving equality to 'true' can project the positive witness;
-- there is no default, unsafe cast or empty-branch axiom.
isYes : ∀ {P : Set} → Torus.Dec P → Bool
isYes (Torus.yes _) = true
isYes (Torus.no _) = false

proofFromYes :
  ∀ {P : Set} (decision : Torus.Dec P) →
  isYes decision ≡ true → P
proofFromYes (Torus.yes proof) refl = proof
proofFromYes (Torus.no _) ()

originalC3SelectableDecision :
  Torus.Dec (Proof.AllSelectable
    (C3.forwardVector Single.canonicalLabelVector)
    Single.canonicalLabelVector)
originalC3SelectableDecision =
  decideAllSelectable
    (C3.forwardVector Single.canonicalLabelVector)
    Single.canonicalLabelVector

-- The next kernel-friendly finite goal is a single CLOSED Boolean
-- certificate. Independent exact Python confirms it, but this source
-- does not assert 'refl' before actual Agda normalization.
originalC3SelectableBooleanGoal : Set
originalC3SelectableBooleanGoal =
  isYes originalC3SelectableDecision ≡ true

originalC3CanonicalFromBoolean :
  originalC3SelectableBooleanGoal →
  Sort.constructedNativeC3CanonicalLabelGoal
originalC3CanonicalFromBoolean closed =
  Proof.originalSortToTargetCorrect
    (proofFromYes originalC3SelectableDecision closed)

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  where

  originalPairSelectableDecision :
    (lengthCheck : Pairs.originalPairSpectatorLengthGoal theory) →
    Torus.Dec (Proof.AllSelectable
      (Pairs.originalPairSpectatorTargetVector theory lengthCheck)
      Single.canonicalLabelVector)
  originalPairSelectableDecision lengthCheck =
    decideAllSelectable
      (Pairs.originalPairSpectatorTargetVector theory lengthCheck)
      Single.canonicalLabelVector

  originalPairSelectableBooleanGoal :
    (lengthCheck : Pairs.originalPairSpectatorLengthGoal theory) → Set
  originalPairSelectableBooleanGoal lengthCheck =
    isYes (originalPairSelectableDecision lengthCheck) ≡ true

  originalPairCanonicalFromBoolean :
    (lengthCheck : Pairs.originalPairSpectatorLengthGoal theory) →
    originalPairSelectableBooleanGoal lengthCheck →
    Pairs.originalPairSpectatorCanonicalLabelGoal theory lengthCheck
  originalPairCanonicalFromBoolean lengthCheck closed =
    Proof.originalSortToTargetCorrect
      (proofFromYes (originalPairSelectableDecision lengthCheck) closed)
