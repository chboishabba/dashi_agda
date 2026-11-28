module DASHI.Physics.YangMills.YMClayR445CanonicalBondPermutationCodecExact where

------------------------------------------------------------------------
-- P0.B SOURCE-PRESERVING, FINITE 1024-BOND PERMUTATION CODEC.
--
-- Start with the *existing* original side-four finite positive-bond
-- enumeration/unique-completeness theorems, not an invented order.
-- Reorder it into 64 original coarse bonds x 2 axial fine phases,
-- followed by the remaining 896 original fine bonds.
--
-- The two lists are proved duplicate-free/disjoint/complete using
-- the existing constructive axial-index injection and original
-- finite list-membership calculus. This yields an ACTUAL bijective
-- Vec-to-Vec codec through the authoritative original bond-vector
-- encode/decode interface, without function extensionality.
--
-- No Gibbs action, Haar product, scalar analysis or RG inequality.
-- The arithmetic length/Count equalities below are computational
-- finite check candidates, pending the local Agda kernel receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Vec.Base as Vec using (Vec)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as T
import DASHI.Physics.YangMills.BalabanFiniteEnumerationDistinctExact as Unique
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayR445OriginalAxialBondParityInjectiveExact as Parity

FineBond : Set
FineBond = T.PositiveBond 4

Selected : Set
Selected = Parity.Selected

originalSelectedPairIndices : List Selected
originalSelectedPairIndices =
  T.cartesian
    (T.elements (Codec.originalPositiveBondFinite 2))
    (T.allCyclicIndices 2)

originalSelectedEncode : Selected → FineBond
originalSelectedEncode (T.pair coarse phase) =
  Parity.originalR445SelectedFineBond coarse phase

originalR445SelectedBondEnumeration : List FineBond
originalR445SelectedBondEnumeration =
  T.map originalSelectedEncode originalSelectedPairIndices

originalSelectedEncodeInjective :
  ∀ {left right : Selected} →
  originalSelectedEncode left ≡ originalSelectedEncode right →
  left ≡ right
originalSelectedEncodeInjective
    {T.pair coarse phase} {T.pair other otherPhase} eq =
  Parity.originalR445SelectedBondEncodingInjective
    coarse other phase otherPhase eq

originalR445SelectedBondEnumerationDistinct :
  Unique.DuplicateFree originalR445SelectedBondEnumeration
originalR445SelectedBondEnumerationDistinct =
  Unique.mapDuplicateFree originalSelectedEncodeInjective
    (Unique.cartesianDuplicateFree
      (Codec.originalPositiveBondDistinct 2)
      (Unique.allCyclicIndicesDuplicateFree 2))

-- Original exact equality decision for positive side-four bonds.
-- Native torus decidability returns T.Empty, while the existing
-- duplicate-free list calculus returns Data.Empty.⊥. Both are
-- uninhabited; an elimination is the only bridge required.
torusEmptyToBottom : T.Empty → ⊥
torusEmptyToBottom ()

torusEmptyElim : ∀ {A : Set} → T.Empty → A
torusEmptyElim ()

originalFineBondEquality : T.DecidableEquality FineBond
originalFineBondEquality =
  T.productDecidableEquality
    (T.periodicTorus4DecidableEquality 4)
    T.cyclicIndexDecidableEquality

-- Constructive decidable list membership. The residue is a filtered
-- subset of the authoritative ORIGINAL side-four bond enumeration.
decideListMembership :
  ∀ {A : Set} →
  T.DecidableEquality A →
  (item : A) (items : List A) →
  T.Dec (item T.∈ items)
decideListMembership decide item [] =
  T.no (λ ())
decideListMembership decide item (head ∷ tail)
  with decide item head | decideListMembership decide item tail
... | T.yes refl | _ = T.yes T.here
... | T.no unequal | T.yes inTail =
  T.yes (T.there inTail)
... | T.no unequal | T.no notInTail =
  T.no (λ { T.here → unequal refl
          ; (T.there member) → notInTail member })

selectedMembershipDecision :
  (fine : FineBond) →
  T.Dec (fine T.∈ originalR445SelectedBondEnumeration)
selectedMembershipDecision fine =
  decideListMembership originalFineBondEquality fine
    originalR445SelectedBondEnumeration

-- Exact canonical source residuals, not a generic freely chosen
-- 896-link field. Their order is the original canonical bond order.
removeSelected : List FineBond → List FineBond
removeSelected [] = []
removeSelected (bond ∷ rest) with selectedMembershipDecision bond
... | T.yes _ = removeSelected rest
... | T.no _ = bond ∷ removeSelected rest

originalR445ResidualBondEnumeration : List FineBond
originalR445ResidualBondEnumeration =
  removeSelected
    (T.elements (Codec.originalPositiveBondFinite 4))

-- Every retained residual is a member of the original canonical
-- bond enumeration; this is the key source-preservation proof.
removeSelectedSubsequence :
  ∀ {bond : FineBond} {items : List FineBond} →
  bond T.∈ removeSelected items →
  bond T.∈ items
removeSelectedSubsequence {items = []} ()
removeSelectedSubsequence {items = head ∷ tail} membership
  with selectedMembershipDecision head
... | T.yes _ = T.there (removeSelectedSubsequence membership)
... | T.no _ with membership
... | T.here = T.here
... | T.there inTail =
  T.there (removeSelectedSubsequence inTail)

-- Every retained residual is excluded from the 128 selected bonds.
removeSelectedFresh :
  ∀ {bond : FineBond} {items : List FineBond} →
  bond T.∈ removeSelected items →
  (bond T.∈ originalR445SelectedBondEnumeration →
   T.Empty)
removeSelectedFresh {items = []} ()
removeSelectedFresh {items = head ∷ tail} membership
  with selectedMembershipDecision head
... | T.yes _ = removeSelectedFresh membership
... | T.no absent with membership
... | T.here = absent
... | T.there inTail = removeSelectedFresh inTail

-- A canonical bond that was not selected is never removed.
removeSelectedRetainsNonselected :
  ∀ {bond : FineBond} {items : List FineBond} →
  (bond T.∈ originalR445SelectedBondEnumeration →
   T.Empty) →
  bond T.∈ items →
  bond T.∈ removeSelected items
removeSelectedRetainsNonselected {items = []} absent ()
removeSelectedRetainsNonselected {items = head ∷ tail}
    absent T.here with selectedMembershipDecision head
... | T.yes selected = torusEmptyElim (absent selected)
... | T.no _ = T.here
removeSelectedRetainsNonselected {items = head ∷ tail}
    absent (T.there inTail) with selectedMembershipDecision head
... | T.yes _ =
  removeSelectedRetainsNonselected absent inTail
... | T.no _ =
  T.there (removeSelectedRetainsNonselected absent inTail)

removeSelectedPreservesDistinct :
  ∀ {items : List FineBond} →
  Unique.DuplicateFree items →
  Unique.DuplicateFree (removeSelected items)
removeSelectedPreservesDistinct {items = []} Unique.[]-free =
  Unique.[]-free
removeSelectedPreservesDistinct {items = head ∷ tail}
    (Unique._∷-free_ absent distinct)
  with selectedMembershipDecision head
... | T.yes _ = removeSelectedPreservesDistinct distinct
... | T.no _ =
  Unique._∷-free_
    (λ inRest → absent (removeSelectedSubsequence inRest))
    (removeSelectedPreservesDistinct distinct)

originalR445ResidualBondEnumerationDistinct :
  Unique.DuplicateFree originalR445ResidualBondEnumeration
originalR445ResidualBondEnumerationDistinct =
  removeSelectedPreservesDistinct
    (Codec.originalPositiveBondDistinct 4)

originalR445SelectedResidualDisjoint :
  Unique.Disjoint
    originalR445SelectedBondEnumeration
    originalR445ResidualBondEnumeration
originalR445SelectedResidualDisjoint = record
  { disjoint = λ inSelected inResidual →
      torusEmptyToBottom (removeSelectedFresh inResidual inSelected)
  }

originalR445AllOriginalBondsCovered :
  (bond : FineBond) →
  (bond T.∈ originalR445SelectedBondEnumeration)
  ⊎ (bond T.∈ originalR445ResidualBondEnumeration)
originalR445AllOriginalBondsCovered bond
  with selectedMembershipDecision bond
... | T.yes selected = inj₁ selected
... | T.no absent =
  inj₂ (removeSelectedRetainsNonselected absent
    (T.complete (Codec.originalPositiveBondFinite 4) bond))

originalR445PairResidualBondEnumeration : List FineBond
originalR445PairResidualBondEnumeration =
  T._++_
    originalR445SelectedBondEnumeration
    originalR445ResidualBondEnumeration

originalR445PairResidualDistinct :
  Unique.DuplicateFree originalR445PairResidualBondEnumeration
originalR445PairResidualDistinct =
  Unique.appendDuplicateFree
    originalR445SelectedBondEnumerationDistinct
    originalR445ResidualBondEnumerationDistinct
    originalR445SelectedResidualDisjoint

originalR445PairResidualComplete :
  (bond : FineBond) →
  bond T.∈ originalR445PairResidualBondEnumeration
originalR445PairResidualComplete bond
  with originalR445AllOriginalBondsCovered bond
... | inj₁ selected =
  T.appendMembershipLeft selected
... | inj₂ residual =
  T.appendMembershipRight residual

-- The reordered source is a PROVED finite enumeration on precisely
-- the original positive-bond carrier, not an independent bond set.
originalR445PairResidualFinite : T.FiniteEnumeration FineBond
originalR445PairResidualFinite = record
  { elements = originalR445PairResidualBondEnumeration
  ; complete = originalR445PairResidualComplete
  }

-- Computation on exactly 64 coarse indices and two axial phases.
originalR445SelectedCountIs128 :
  Codec.listLength originalR445SelectedBondEnumeration ≡ 128
originalR445SelectedCountIs128 =
  trans
    (Codec.listLengthMap originalSelectedEncode originalSelectedPairIndices)
    (trans
      (Codec.listLengthCartesian
        (T.elements (Codec.originalPositiveBondFinite 2))
        (T.allCyclicIndices 2))
      refl)

-- The *actual* residual list is a filtered canonical 1024-link list;
-- count is computed from source indices rather than asserted as a
-- separately postulated residual dimension.
originalR445ResidualCountIs896 :
  Codec.listLength originalR445ResidualBondEnumeration ≡ 896
originalR445ResidualCountIs896 = refl

originalR445PairResidualCountIs1024 :
  Codec.listLength originalR445PairResidualBondEnumeration ≡ 1024
originalR445PairResidualCountIs1024 =
  trans
    (Codec.listLengthAppend
      originalR445SelectedBondEnumeration
      originalR445ResidualBondEnumeration)
    (trans
      (cong (λ count → count + Codec.listLength
        originalR445ResidualBondEnumeration)
        originalR445SelectedCountIs128)
      (trans
        (cong (λ count → 128 + count)
          originalR445ResidualCountIs896)
        refl))

-- Explicit reordering of the source's canonical vector representation
-- using BOTH constructed finite enumerations and their proven
-- completeness/no-duplicates, no axiom of vector permutation.
originalR445CanonicalToPairResidual :
  ∀ {A : Set} →
  Vec A (Codec.originalPositiveBondCount 4) →
  Vec A (Codec.listLength originalR445PairResidualBondEnumeration)
originalR445CanonicalToPairResidual vector =
  Codec.encodeField originalR445PairResidualFinite
    (Codec.decodeOriginalBonds 4 vector)

originalR445PairResidualToCanonical :
  ∀ {A : Set} →
  Vec A (Codec.listLength originalR445PairResidualBondEnumeration) →
  Vec A (Codec.originalPositiveBondCount 4)
originalR445PairResidualToCanonical vector =
  Codec.encodeOriginalBonds 4
    (Codec.decodeField originalR445PairResidualFinite vector)

originalR445CanonicalReorderRoundTrip :
  ∀ {A : Set} (vector : Vec A (Codec.originalPositiveBondCount 4)) →
  originalR445PairResidualToCanonical
    (originalR445CanonicalToPairResidual vector)
  ≡ vector
originalR445CanonicalReorderRoundTrip vector =
  trans
    (Codec.originalBondsEncodePointwise 4
      (Codec.decodeField originalR445PairResidualFinite
        (Codec.encodeField originalR445PairResidualFinite
          (Codec.decodeOriginalBonds 4 vector)))
      (Codec.decodeOriginalBonds 4 vector)
      (λ bond →
        Codec.decodeEncodeAt originalR445PairResidualFinite
          (Codec.decodeOriginalBonds 4 vector) bond))
    (Codec.originalBondsEncodeDecodeExactly 4 vector)

originalR445PairResidualReorderRoundTrip :
  ∀ {A : Set}
    (vector : Vec A
      (Codec.listLength originalR445PairResidualBondEnumeration)) →
  originalR445CanonicalToPairResidual
    (originalR445PairResidualToCanonical vector)
  ≡ vector
originalR445PairResidualReorderRoundTrip vector =
  trans
    (Codec.encodeFieldPointwise originalR445PairResidualFinite
      (Codec.decodeOriginalBonds 4
        (Codec.encodeOriginalBonds 4
          (Codec.decodeField originalR445PairResidualFinite vector)))
      (Codec.decodeField originalR445PairResidualFinite vector)
      (λ bond →
        Codec.originalBondsDecodeEncodeAt 4
          (Codec.decodeField originalR445PairResidualFinite vector)
          bond))
    (Codec.encodeDecodeExactly
      originalR445PairResidualFinite
      originalR445PairResidualDistinct vector)
