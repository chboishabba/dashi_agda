module DASHI.Physics.YangMills.YMClayNativeOriginalSortMembershipCorrectExact where

------------------------------------------------------------------------
-- 6 Nov 2026. R443.F07 / R445.F21 ORIGINAL sorting CORRECTNESS.
--
-- The old 1024-link sorter was a concrete program without a GENERAL
-- correctness lemma. Prove the hard algorithmic step ONCE:
-- when the desired original bond occurs in a nonempty native vector,
-- originalBubbleDesired moves it to its head.
--
-- Then originalSortToTarget is correct whenever every selected target
-- head still belongs to the current unsorted suffix. This is the
-- precise, NON-CIRCULAR selection-invariant required by the original
-- C3 and selected pair/spectator target programs. A concrete native
-- label-bijection certificate must next inhabit AllSelectable for
-- each original target. We deliberately do not assert that here.
--
-- This introduces NO new source bonds, link-carrier, Haar functional,
-- Gibbs distribution or Agda postulate. SOURCE ONLY: kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.YMClayNativeC3AdjacentSortProgramExact as Sort
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product

Bond : Set
Bond = Sort.Bond

-- Membership of the SAME original bond label, indexed by Vec length.
infix 4 _∈ᵛ_
data _∈ᵛ_ (wanted : Bond) : ∀ {n} → Vec.Vec Bond n → Set where
  here : ∀ {n} {tail : Vec.Vec Bond n} →
    wanted ∈ᵛ (wanted Vec.∷ tail)
  there : ∀ {n} {head : Bond} {tail : Vec.Vec Bond n} →
    wanted ∈ᵛ tail → wanted ∈ᵛ (head Vec.∷ tail)

fromEmpty : ∀ {A : Set} → Torus.Empty → A
fromEmpty ()

-- The exact original bubble program brings a present target to the
-- head. The proof follows the ORIGINAL decidable equality and
-- ORIGINAL Product.swapHead/fixHead/compose execution order.
bubbleDesiredHeadWhenMember :
  ∀ {n} (wanted : Bond) (source : Vec.Vec Bond (suc n)) →
  wanted ∈ᵛ source →
  Σ (Vec.Vec Bond n)
    (λ remainder →
      Product.permuteLinks (Sort.originalBubbleDesired wanted source)
        source
      ≡ wanted Vec.∷ remainder)
bubbleDesiredHeadWhenMember wanted ( .wanted Vec.∷ Vec.[]) here =
  Vec.[] , refl
bubbleDesiredHeadWhenMember wanted (first Vec.∷ Vec.[]) (there ())
bubbleDesiredHeadWhenMember wanted
    ( .wanted Vec.∷ second Vec.∷ rest) here
  with Sort.originalBondDecide wanted wanted
... | Torus.yes _ =
  (second Vec.∷ rest) , refl
... | Torus.no notEqual =
  fromEmpty (notEqual refl)
bubbleDesiredHeadWhenMember wanted
    (first Vec.∷ second Vec.∷ rest) (there member)
  with Sort.originalBondDecide first wanted
... | Torus.yes firstEquals =
  (second Vec.∷ rest) ,
    cong (λ chosen → chosen Vec.∷ second Vec.∷ rest) firstEquals
... | Torus.no _ with
    bubbleDesiredHeadWhenMember wanted (second Vec.∷ rest) member
... | (remainder , atHead) =
  (first Vec.∷ remainder) ,
    cong
      (λ moved →
        Product.permuteLinks Product.swapHead
          (first Vec.∷ moved))
      atHead

-- Inductive, proof-relevant assertion: for EVERY target head, the
-- target remains in the SOURCE suffix at the exact state produced by
-- the ORIGINAL bubble algorithm. This is strictly weaker than
-- assuming the final 1024-vector equality and is derived from a
-- native permutation/no-duplicates lemma in the next producer.
data AllSelectable :
  ∀ {n} → Vec.Vec Bond n → Vec.Vec Bond n → Set where
  done : AllSelectable Vec.[] Vec.[]
  select :
    ∀ {n} {wanted : Bond}
      {targetTail : Vec.Vec Bond n}
      {source : Vec.Vec Bond (suc n)} →
    wanted ∈ᵛ source →
    AllSelectable targetTail
      (Sort.originalTail
        (Product.permuteLinks
          (Sort.originalBubbleDesired wanted source) source)) →
    AllSelectable (wanted Vec.∷ targetTail) source

-- Generic original adjacent-swap SORT correctness, proved once by
-- structural induction. No 46,592-swap normalization is requested.
-- The remaining closed native obligation is to prove AllSelectable
-- for each original C3 / pair-spectator target; then this theorem
-- transports the result to the existing canonical-label goals.
originalSortToTargetCorrect :
  ∀ {n} {target source : Vec.Vec Bond n} →
  AllSelectable target source →
  Product.permuteLinks (Sort.originalSortToTarget target source) source
  ≡ target
originalSortToTargetCorrect done = refl
originalSortToTargetCorrect
    (select {wanted = wanted} {source = source} present tailReady)
  with bubbleDesiredHeadWhenMember wanted source present
... | (remainder , headProof) rewrite headProof =
  cong (Vec._∷_ wanted) (originalSortToTargetCorrect tailReady)
