module DASHI.Physics.YangMills.BalabanCMP122ConditionalRGClosure where

-- Literal wrapper for Theorem 1 of Balaban, CMP 122 II (article pp. 355--356,
-- conclusion on p. 391).  The theorem is conditional: it assumes that every
-- effective coupling lies in a sufficiently small interval ]0, γ].
--
-- This is deliberately a paper-import boundary.  It does not claim to prove
-- the small-coupling trajectory, nor does it replace the separate continuum
-- or observable analysis which CMP 122 explicitly leaves for later work.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; _≤ℝ_ ; _<ℝ_ ; 0ℝ )
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; VerificationStatus
  ; balaban-cmp-122
  ; paperImport
  )

-- Sect. 2 [Balaban III] is referred to by CMP 122 II rather than reproduced
-- in its Theorem 1 statement.  Keep its representation and its three bound
-- families opaque until that earlier section is separately extracted.
record CMP122Section2InductivePackage : Set₁ where
  field
    EffectiveDensityRepresentation : ℕ → Set
    SmallFieldInductiveBounds : ℕ → Set
    LargeFieldRBounds : ℕ → Set
    ROperationExpansionConverges : ℕ → Set
    uniformInScaleAndVolume : Set

open CMP122Section2InductivePackage public

record BalabanCMP122ConditionalRGClosure : Set₁ where
  field
    γ : ℝ
    γ-positive : 0ℝ <ℝ γ

    effectiveCoupling : ℕ → ℝ
    couplingRemainsSmall :
      ∀ k → (0ℝ <ℝ effectiveCoupling k) × (effectiveCoupling k ≤ℝ γ)

    section2Package : CMP122Section2InductivePackage
    effectiveDensityRepresentation :
      ∀ k → EffectiveDensityRepresentation section2Package k
    smallFieldBounds :
      ∀ k → SmallFieldInductiveBounds section2Package k
    largeFieldRBounds :
      ∀ k → LargeFieldRBounds section2Package k
    polymerExpansionConverges :
      ∀ k → ROperationExpansionConverges section2Package k

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open BalabanCMP122ConditionalRGClosure public

-- The premise and conclusion have been transcribed, but no source witness is
-- installed here: it must be reviewed against Sect. 2 [III] before it can be
-- used as a paper import in a promoted route.
currentBalabanCMP122ConditionalRGClosureAvailable : Set
currentBalabanCMP122ConditionalRGClosureAvailable = ⊥

-- This metadata records the exact intended source citation without asserting
-- that the unextracted Sect. 2 package has already been instantiated.
currentBalabanCMP122Source : SourceAuthorityId
currentBalabanCMP122Source = balaban-cmp-122

currentBalabanCMP122Status : VerificationStatus
currentBalabanCMP122Status = paperImport
