module DASHI.Physics.YangMills.BalabanEmbeddedCanonicalRationalConstrainedFoldExact where

------------------------------------------------------------------------
-- CANONICAL RATIONAL CONSTRAINED FOLD -> REAL SELECTED FOLD
--
-- Reuse the existing Round208 rational->real ring embedding and real finite sum.
-- No competing scalar ABI is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _+ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as AddEmbed
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanClayP3CanonicalRationalConstrainedSumExact as Canonical
import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral

realSelectedFold :
  ∀ {Fine Coarse}
    (embedding : RingEmbed.RationalRealRingEmbedding)
    (dataSet : Canonical.CanonicalRationalConstrainedSumData Fine Coarse) →
  List Fine → (Fine → ℚ) → Coarse → ℝ
realSelectedFold embedding dataSet fields value coarse =
  RingEmbed.realSum fields
    (λ fine →
      AddEmbed.Embed.embed
        (AddEmbed.base (RingEmbed.additive embedding))
        (Integral.selectedWith
          (Canonical.canonicalRationalConstrainedSum dataSet)
          value coarse fine))

embeddedFoldSelectedExact :
  ∀ {Fine Coarse}
    (embedding : RingEmbed.RationalRealRingEmbedding)
    (dataSet : Canonical.CanonicalRationalConstrainedSumData Fine Coarse)
    fields value coarse →
  AddEmbed.Embed.embed
    (AddEmbed.base (RingEmbed.additive embedding))
    (Integral.foldSelected
      (Canonical.canonicalRationalConstrainedSum dataSet)
      value coarse fields)
  ≡
  realSelectedFold embedding dataSet fields value coarse
embeddedFoldSelectedExact embedding dataSet [] value coarse =
  AddEmbed.Embed.zeroExact
    (AddEmbed.base (RingEmbed.additive embedding))
embeddedFoldSelectedExact embedding dataSet (fine ∷ fields) value coarse =
  trans
    (AddEmbed.addExact (RingEmbed.additive embedding)
      (value fine)
      (Integral.foldSelected
        (Canonical.canonicalRationalConstrainedSum dataSet)
        value coarse fields))
    (cong
      (λ tail →
        AddEmbed.Embed.embed
          (AddEmbed.base (RingEmbed.additive embedding))
          (value fine)
        +ℝ tail)
      (embeddedFoldSelectedExact
        embedding dataSet fields value coarse))

embeddedConstrainedIntegralExact :
  ∀ {Fine Coarse}
    (embedding : RingEmbed.RationalRealRingEmbedding)
    (dataSet : Canonical.CanonicalRationalConstrainedSumData Fine Coarse)
    fields weight coarse →
  AddEmbed.Embed.embed
    (AddEmbed.base (RingEmbed.additive embedding))
    (Integral.constrainedIntegral
      (Canonical.canonicalRationalConstrainedSum dataSet)
      fields weight coarse)
  ≡
  realSelectedFold embedding dataSet
    fields
    (Integral.selectedWith
      (Canonical.canonicalRationalConstrainedSum dataSet)
      weight coarse)
    coarse
embeddedConstrainedIntegralExact embedding dataSet fields weight coarse =
  embeddedFoldSelectedExact embedding dataSet
    fields
    (Integral.selectedWith
      (Canonical.canonicalRationalConstrainedSum dataSet)
      weight coarse)
    coarse

embeddedCanonicalRationalConstrainedFoldLevel : ProofLevel
embeddedCanonicalRationalConstrainedFoldLevel = machineChecked
