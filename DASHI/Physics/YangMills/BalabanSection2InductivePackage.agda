module DASHI.Physics.YangMills.BalabanSection2InductivePackage where

-- Literal source-facing surface for Sect. 2 of Balaban, CMP 119 (1989),
-- pp. 254--263.  CMP 122 II, Theorem 1, says that its final R-operation
-- construction restores precisely this inductive package.  This module does
-- not translate those statements into DASHI's older diameter/KP interfaces.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ; _≤_)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; VerificationStatus
  ; balaban-cmp-119
  ; paperImport
  )

-- CMP 119 Sect. 2 uses a three-sequence domain index
-- (Ω_j, Λ_j, S_j), an effective density ρ_k, an operation T_k, and an
-- effective action decomposed as a Wilson term plus E_k, R_k, B_k and a
-- vacuum-energy constant; see (2.1), (2.18)--(2.23).
record BalabanSection2InductivePackage : Set₁ where
  field
    terminalScale : ℕ
    EffectiveDensity : ℕ → Set
    PolymerActivity : ℕ → Set
    ActivityNorm : (k : ℕ) → PolymerActivity k → Set

    -- Representation (2.18), operation factorisation (2.19)--(2.22), and
    -- action decomposition (2.23).
    effectiveDensityForm : (k : ℕ) → k ≤ terminalScale → EffectiveDensity k
    factorisedLargeFieldOperations : (k : ℕ) → k ≤ terminalScale → Set
    effectiveActionDecomposition : (k : ℕ) → k ≤ terminalScale → Set

    -- Sect. 2 separates fully-renormalised small-field E terms, R-operation
    -- terms with localized exponential decay (2.30)--(2.33), and boundary B
    -- terms near large-field regions.
    smallFieldEstimate : (k : ℕ) → k ≤ terminalScale → Set
    largeFieldREstimate : (k : ℕ) → k ≤ terminalScale → Set
    boundaryTermEstimate : (k : ℕ) → k ≤ terminalScale → Set
    localisationSummability : (k : ℕ) → k ≤ terminalScale → Set

    -- Regular configurations are selected by the source characteristic
    -- functions; they are part of the density representation, not a separate
    -- legacy ellipticity premise.  See (2.10), (2.17), and the discussion
    -- before (2.40).
    regularConfigurationControl : (k : ℕ) → k ≤ terminalScale → Set

    -- Theorem 1 in CMP 119: RT maps the scale-k induction class to the
    -- scale-(k+1) class, subject to its stated coupling hypotheses.
    rOperationConvergence : (k : ℕ) → k ≤ terminalScale → Set
    nextScaleClosure : (k : ℕ) → k ≤ terminalScale → Set
    uniformInVolume : Set

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open BalabanSection2InductivePackage public

-- Classification for old DASHI gates relative to the *published theorem
-- boundary*.  It deliberately distinguishes an internal ingredient of a
-- published proof from an explicit hypothesis of its theorem statement.
data PublishedTheoremRole : Set where
  explicitPublishedHypothesis : PublishedTheoremRole
  internalProofIngredient : PublishedTheoremRole
  embeddedInductiveCondition : PublishedTheoremRole
  roleStillNeedsAudit : PublishedTheoremRole

-- CMP 122 II Theorem 1 has one explicit mathematical premise: the complete
-- effective-coupling sequence stays in ]0, γ].  Its introduction says that
-- the new combinatorial bounds prove convergence of the whole R expansion.
-- Thus P06-style animal counting is not a second top-level premise of the
-- source theorem, although it remains relevant to an independent rebuild.
p06RoleInCMP122Theorem : PublishedTheoremRole
p06RoleInCMP122Theorem = internalProofIngredient

-- CMP 119 Sect. 2 works on regular configurations selected by characteristic
-- functions.  The exact relationship to DASHI's P33 single-link-positivity
-- wrapper has not yet been extracted, so it must not be promoted as either a
-- source theorem hypothesis or a proved source consequence.
p33RoleInCMP122Theorem : PublishedTheoremRole
p33RoleInCMP122Theorem = roleStillNeedsAudit

p06IsNotAnExplicitCMP122Hypothesis :
  p06RoleInCMP122Theorem ≡ internalProofIngredient
p06IsNotAnExplicitCMP122Hypothesis = refl

-- The public theorem boundary contains no P06/P33 slots.  The latter remain
-- compatibility/audit inputs only until their exact source roles are settled.
record UniformBalabanRGClosure : Set₁ where
  field
    section2 : BalabanSection2InductivePackage
    terminalScale : ℕ
    terminalScaleAgrees :
      terminalScale ≡ BalabanSection2InductivePackage.terminalScale section2
    allScalesEffectiveDensityForm :
      ∀ k →
      k ≤ BalabanSection2InductivePackage.terminalScale section2 →
      EffectiveDensity section2 k
    allScalesSmallFieldEstimate :
      ∀ k →
      (k≤sourceTerminal :
        k ≤ BalabanSection2InductivePackage.terminalScale section2) →
      smallFieldEstimate section2 k k≤sourceTerminal
    allScalesLargeFieldREstimate :
      ∀ k →
      (k≤sourceTerminal :
        k ≤ BalabanSection2InductivePackage.terminalScale section2) →
      largeFieldREstimate section2 k k≤sourceTerminal
    allScalesLocalisationSummability :
      ∀ k →
      (k≤sourceTerminal :
        k ≤ BalabanSection2InductivePackage.terminalScale section2) →
      localisationSummability section2 k k≤sourceTerminal
    allScalesROperationConvergence :
      ∀ k →
      (k≤sourceTerminal :
        k ≤ BalabanSection2InductivePackage.terminalScale section2) →
      rOperationConvergence section2 k k≤sourceTerminal
    allScalesNextStepClosure :
      ∀ k →
      (k≤sourceTerminal :
        k ≤ BalabanSection2InductivePackage.terminalScale section2) →
      nextScaleClosure section2 k k≤sourceTerminal
    uniformInVolume : uniformInVolume section2
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false
