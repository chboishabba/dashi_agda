module DASHI.Physics.YangMills.YMClayOriginalF19R445EveryLinkValueBIDIExact where

------------------------------------------------------------------------
-- P0 F19 -> R445: ORIGINAL arbitrary link VALUE consumer, not merely
-- a 1024-element label count or a synthetic replacement field.
--
-- Original master sources:
--   F19 original selected-128 + canonical spectator-896 labels
--   R445 original complete 128+896 positive-bond codec
--   Codec original finite enumeration / encode/decode of ANY Link
--
-- The full ordered LABEL equality is a separate proof candidate on
-- this same #1536 branch:
--   YMClayOriginalF19R445Full1024LabelsP0Exact.
--
-- By transporting all original values along exactly that equality,
-- both source presentations read the SAME ORIGINAL bond field at
-- ALL 1024 positions, including all 896 interacting spectators.
-- No SU(N)-specific group commutation or factorization is assumed.
--
-- Does NOT itself certify that F19's native adjacent-swap permutation
-- is this target vector: original master
-- YMClayNative1024ClosedReindexHaarConsequencesExact owns that
-- source-derived permutation theorem; its transport is next.
--
-- Source-written; exact Agda 2.9 kernel not locally available.
-- Physical original W1/W3, E1 continuum and OS/H mass gap remain OPEN.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; subst)
import Data.Vec.Base as Vec

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClayNativeSideFourPairSpectatorSortProgramExact as F19
import DASHI.Physics.YangMills.YMClayOriginalF19R445Full1024LabelsP0Exact as Labels
import DASHI.Physics.YangMills.YMClayR445CanonicalBondPermutationCodecExact as R445
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec

module _
  {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  where

  -- Distinct Boolean F19 filter and Dec R445 filter have already been
  -- joined on the actual original source label list. Preserve the
  -- source's exact dependent vector lengths by transport, not coercion.
  originalAllOriginalLinkValuesPreserved :
    ∀ {Value : Set} (original : R445.FineBond → Value) →
    subst
      (λ labels → Vec.Vec Value (Codec.listLength labels))
      (Labels.originalF19Complete1024LabelOrderMatchesR445 theory)
      (Codec.listValues
        (F19.originalPairThenSpectatorLabels theory) original)
    ≡
    Codec.encodeField R445.originalR445PairResidualFinite original
  originalAllOriginalLinkValuesPreserved original
    rewrite Labels.originalF19Complete1024LabelOrderMatchesR445 theory =
      refl

  -- Concrete original canonical 1024-link vector, decoded ONCE by the
  -- original positive-bond enumeration: F19 order and R445 order read
  -- exactly the same original link values, no missing spectator field.
  originalEveryCanonicalVectorAgreesWithR445 :
    ∀ {Value : Set}
      (original : Vec.Vec Value (Codec.originalPositiveBondCount 4)) →
    subst
      (λ labels → Vec.Vec Value (Codec.listLength labels))
      (Labels.originalF19Complete1024LabelOrderMatchesR445 theory)
      (Codec.listValues
        (F19.originalPairThenSpectatorLabels theory)
        (Codec.decodeOriginalBonds 4 original))
    ≡
    R445.originalR445CanonicalToPairResidual original
  originalEveryCanonicalVectorAgreesWithR445 original =
    originalAllOriginalLinkValuesPreserved
      (Codec.decodeOriginalBonds 4 original)

  -- No replacement observable or new Gibbs state: any consumer over
  -- the ORIGINAL sorted 1024-link vector has identical value.
  originalEverySortedValueConsumerAgrees :
    ∀ {Value Scalar : Set}
      (original : Vec.Vec Value (Codec.originalPositiveBondCount 4))
      (consumer : Vec.Vec Value
        (Codec.listLength R445.originalR445PairResidualBondEnumeration)
        → Scalar) →
    consumer
      (subst
        (λ labels → Vec.Vec Value (Codec.listLength labels))
        (Labels.originalF19Complete1024LabelOrderMatchesR445 theory)
        (Codec.listValues
          (F19.originalPairThenSpectatorLabels theory)
          (Codec.decodeOriginalBonds 4 original)))
    ≡
    consumer (R445.originalR445CanonicalToPairResidual original)
  originalEverySortedValueConsumerAgrees original consumer =
    cong consumer (originalEveryCanonicalVectorAgreesWithR445 original)

-- The real native F19 adjacent-swap sorted permutation output is
-- separately compiler-owned by
-- YMClayNative1024ClosedReindexHaarConsequencesExact.
-- Next exact source-specific square is its target Vec against the
-- R445 sorted field via original finite listToVec/Vec.map transport.
