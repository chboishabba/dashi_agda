module DASHI.Physics.YangMills.YMClayNativeSideFourPairDistinctCertificateExact where

------------------------------------------------------------------------
-- R445 selected original side-four side-two link-pair finite certificate.
--
-- Do NOT introduce a new torus: use exactly the original
-- Codec.originalPositiveBondFinite 2 (64 coarse bonds),
-- Codec.originalPositiveBondFinite 4 (1024 fine bonds), and the
-- actual original two fine-bond endpoint maps from F15.
--
-- Fully constructed finite Boolean decision of duplicate-freeness on
-- the literal list [first(c), second(c)] for all 64 coarse bonds.
-- In this *closed* M=2,L=2 selected instance, equality decision uses
-- the original Torus.productDecidableEquality and original site/axis
-- decidable equalities. No postulate, Fin collision oracle or hand-fed
-- Boolean certificate. The intended closed decision evaluates to true
-- by normalization, requiring actual Agda kernel verification.
--
-- This is only a selected finite LABEL disjointness/count certificate:
-- the 1024-index reordering/permutation program and proof of full
-- Haar integration factorization remain a separate source-matched cut.
-- It also does not establish all-size endpoints, continuous Haar,
-- effective Gibbs density, RP, continuum, OS or Clay.
-- Wilson/Balaban; reused original DASHI native enumeration/decoders.
-- Source written, kernel acceptance pending; no --safe claim.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.List.Base as List
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayNativeSideFourTwoLinkPairSameObjectExact as Pair

OriginalFineBond : Set
OriginalFineBond = Torus.PositiveBond 4

OriginalCoarseBond : Set
OriginalCoarseBond = Torus.PositiveBond 2

originalCoarseBondLabels : List OriginalCoarseBond
originalCoarseBondLabels =
  Torus.elements (Codec.originalPositiveBondFinite 2)

originalFineBondLabels : List OriginalFineBond
originalFineBondLabels =
  Torus.elements (Codec.originalPositiveBondFinite 4)

-- Original pointwise bond-equality authority, not a guessed numeric
-- encoding of bond labels.
originalFineBondEquality :
  Torus.DecidableEquality OriginalFineBond
originalFineBondEquality =
  Torus.productDecidableEquality
    (Torus.periodicTorus4DecidableEquality 4)
    Torus.cyclicIndexDecidableEquality

originalBondEqualsBoolean :
  OriginalFineBond → OriginalFineBond → Bool
originalBondEqualsBoolean first second
  with originalFineBondEquality first second
... | Torus.yes _ = true
... | Torus.no _ = false

booleanAnd : Bool → Bool → Bool
booleanAnd true right = right
booleanAnd false right = false

booleanNot : Bool → Bool
booleanNot true = false
booleanNot false = true

memberBoolean : OriginalFineBond → List OriginalFineBond → Bool
memberBoolean bond [] = false
memberBoolean bond (head ∷ tail) =
  booleanAnd
    (booleanNot (originalBondEqualsBoolean bond head))
    (memberBoolean bond tail)
  -- This is a "not-member" conjunction, not a standard member predicate.

allDistinctBoolean : List OriginalFineBond → Bool
allDistinctBoolean [] = true
allDistinctBoolean (bond ∷ rest) =
  booleanAnd (memberBoolean bond rest) (allDistinctBoolean rest)

module _ {Value : Set} (group : Bond.ExactLinkGroup Value) where

  selectedFinePairLabels :
    List OriginalCoarseBond → List OriginalFineBond
  selectedFinePairLabels [] = []
  selectedFinePairLabels (coarse ∷ rest) =
    Pair.originalFirstFineBond group coarse
      ∷ Pair.originalSecondFineBond group coarse
      ∷ selectedFinePairLabels rest

  actualSelectedFineLabels : List OriginalFineBond
  actualSelectedFineLabels =
    selectedFinePairLabels originalCoarseBondLabels

  -- These numerical claims are on the actual original 4D product
  -- enumerations, NOT independently hard-coded finite-site data.
  selectedCoarseBondsAre64 :
    List.length originalCoarseBondLabels ≡ 64
  selectedCoarseBondsAre64 = refl

  actualSelectedFinePairsAre128 :
    List.length actualSelectedFineLabels ≡ 128
  actualSelectedFinePairsAre128 = refl

  originalFullFineBondsAre1024 :
    List.length originalFineBondLabels ≡ 1024
  originalFullFineBondsAre1024 = refl

  -- Fully closed finite decision. The reflexive proof obliges Agda to
  -- evaluate the ACTUAL original 128 original-bond labels. This is
  -- intentionally not replaced by a Boolean "isDistinct=true" axiom.
  actualSelectedFinePairLabelsDistinct :
    allDistinctBoolean actualSelectedFineLabels ≡ true
  actualSelectedFinePairLabelsDistinct = refl

-- Still missing before invoking product Haar over all native bonds:
-- a concrete 1024-index permutation / Vec coordinate reorder sending
-- these 128 selected fine labels to 64 consecutive ordered pairs and
-- all 896 others to the spectator suffix, and the exact decoder/selected
-- block identification under that permutation. Agda kernel pending.
