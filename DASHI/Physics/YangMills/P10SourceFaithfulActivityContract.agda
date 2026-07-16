module DASHI.Physics.YangMills.P10SourceFaithfulActivityContract where

-- Source-faithful P10 boundary.
--
-- Balaban CMP 122 II separates two estimates which the old public P10
-- envelope conflates:
--
-- * (1.100) bounds R-terms by exp (-p₀(gₖ)) exp (-κ dₖ(X)); and
-- * (1.67)--(1.68) define the relative tree length dₖᶻ(Y) and bound the
--   localized K(Y)-terms by a separate relative-domain exponential.
--
-- This module deliberately keeps both source contracts explicit.  Neither is
-- a replacement theorem for the older length-based P10 envelope.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base renaming (ℕ to Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; ∃)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _≤ℝ_
  ; _*ℝ_
  ; -ℝ_
  )
open import DASHI.Physics.YangMills.BalabanLargeFieldSuppression using
  ( expℝ
  ; fromNat
  ; productℝ
  )
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; VerificationStatus
  ; eriksson-2602-0069
  ; paperImport
  )

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

-- `magnitude` is intentionally supplied separately from the activity itself:
-- the present legacy P10 source carrier is real-valued, while the physical
-- activity is complex-valued.  The consumer only needs a nonnegative majorant.
record P10SourceFaithfulActivityContract : Set₁ where
  field
    Domain : Set

    isLargeFieldDomain :
      Nat → Domain → Set

    -- This is the ordinary dₖ(X) of CMP 122 II (1.100).  It must not be
    -- instantiated by `length X` without a proved source interpretation.
    treeLength :
      Nat → Domain → Nat

    p₀-at-scale :
      Nat → ℝ

    κ-tree :
      ℝ

    magnitude :
      Nat → Domain → ℝ

    domainWeight :
      Nat → Domain → ℝ

    activityBound :
      ∀ k X →
      isLargeFieldDomain k X →
      magnitude k X ≤ℝ
        (expℝ (-ℝ (p₀-at-scale k)) *ℝ
         (expℝ (-ℝ (κ-tree *ℝ
           fromNat (treeLength k X))) *ℝ
          domainWeight k X))

    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

open P10SourceFaithfulActivityContract public

-- CMP 122 II (1.67)--(1.68): the separate localized/relative-domain layer.
-- `prefactor` records the source's small α (or the corresponding activity
-- prefactor); it is intentionally not identified with exp (-p₀(gₖ)).
record CMP122RelativeLocalizationActivityContract : Set₁ where
  field
    Domain : Set

    MCube : Set

    TreeCode : Set

    excludedRegion :
      Nat → Domain → Set

    -- Components of Y \ Z, represented by their constituent M-cubes.
    -- CMP 122 II (1.67) requires the relative tree to meet every M-cube of
    -- every one of these components.
    outsideComponents :
      Nat → Domain → List (List MCube)

    isLocalizationDomain :
      Nat → Domain → Set

    relativeTreeLength :
      Nat → Domain → Nat

    canonicalRelativeTree :
      Nat → Domain → TreeCode

    treeEdgeCount :
      TreeCode → Nat

    treeContainedInDomain :
      Nat → Domain → TreeCode → Set

    treeMeetsCube :
      TreeCode → MCube → Set

    relativeTreeAdmissible :
      Nat → Domain → TreeCode → Set

    relativeTreeAdmissibleMeaning :
      ∀ k Y T →
      relativeTreeAdmissible k Y T →
      (treeContainedInDomain k Y T) ×
      (∀ component C →
        component ∈ outsideComponents k Y →
        C ∈ component →
        treeMeetsCube T C)

    relativeTreeAdmissibleCanonical :
      ∀ k Y →
      isLocalizationDomain k Y →
      relativeTreeAdmissible k Y (canonicalRelativeTree k Y)

    relativeTreeLengthRealised :
      ∀ k Y →
      isLocalizationDomain k Y →
      treeEdgeCount (canonicalRelativeTree k Y)
        ≡ relativeTreeLength k Y

    relativeTreeLengthMinimal :
      ∀ k Y T →
      isLocalizationDomain k Y →
      relativeTreeAdmissible k Y T →
      relativeTreeLength k Y ≤ treeEdgeCount T

    κ-relative :
      ℝ

    relativeDecayMultiplier :
      ℝ

    prefactor :
      Nat → ℝ

    magnitude :
      Nat → Domain → ℝ

    domainWeight :
      Nat → Domain → ℝ

    activityBound :
      ∀ k Y →
      isLocalizationDomain k Y →
      magnitude k Y ≤ℝ
        (prefactor k *ℝ
         (expℝ (-ℝ
           (relativeDecayMultiplier *ℝ κ-relative *ℝ
            fromNat (relativeTreeLength k Y))) *ℝ
          domainWeight k Y))

    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

open CMP122RelativeLocalizationActivityContract public

-- CMP 122 II (1.79)--(1.89), followed by the component products in (1.92),
-- shows that the decisive p₀ penalty is attached to large-field components.
-- The coefficient is not universally one: for example (1.89) carries the
-- source coefficient 2 / (1 + β₀).  We therefore expose it as data.
record CMP122ComponentwiseLargeFieldSuppression : Set₁ where
  field
    Domain : Set

    LargeFieldComponent : Set

    largeFieldComponents :
      Nat → Domain → List LargeFieldComponent

    treeLength :
      Nat → Domain → Nat

    κ-tree :
      ℝ

    p₀-at-scale :
      Nat → ℝ

    componentP₀Coefficient :
      Nat → LargeFieldComponent → ℝ

    componentResidualWeight :
      Nat → LargeFieldComponent → ℝ

    magnitude :
      Nat → Domain → ℝ

    activityBound :
      ∀ k X →
      magnitude k X ≤ℝ
        (expℝ (-ℝ (κ-tree *ℝ fromNat (treeLength k X))) *ℝ
         productℝ
           (map
             (λ C →
               expℝ (-ℝ
                 (componentP₀Coefficient k C *ℝ p₀-at-scale k)) *ℝ
               componentResidualWeight k C)
             (largeFieldComponents k X)))

    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

open CMP122ComponentwiseLargeFieldSuppression public

-- P10/P11 replacement carrier ------------------------------------------------
--
-- This is deliberately a geometry-and-analytic-data carrier, rather than a
-- Boolean receipt.  It captures the corrected route through CMP 122 relative
-- domains: every block is owned once, halo coverage converts large components
-- to weighted relative volume, and the fibre/KP quantities are supplied as
-- theorem obligations over that exact carrier.
--
-- The existing public P10 API has only `List Nat` supports and a diameter
-- envelope.  It cannot inhabit this record until the source-domain carrier and
-- its component operation have actually been extracted.
record P10P11WeightedRelativeDomainCarrier : Set₁ where
  field
    Block : Set
    Polymer : Set
    Component : Set

    -- Ωⱼ and Rⱼ = Ωⱼ \ Ωⱼ₊₁ are represented extensionally.  The equalities
    -- below make terminal-scale ownership proof-relevant rather than a
    -- convention hidden in a serializer.
    inOmega : Nat → Block → Set
    inRelativeDomain : Nat → Block → Set
    terminalOwner : Block → Nat

    nestedDomains :
      ∀ j B → inOmega (Nat.suc j) B → inOmega j B

    relativeDomainElimination :
      ∀ j B → inRelativeDomain j B →
      inOmega j B × (inOmega (Nat.suc j) B → ⊥)

    relativeDomainIntroduction :
      ∀ j B → inOmega j B → (inOmega (Nat.suc j) B → ⊥) →
      inRelativeDomain j B

    ownerInRelativeDomain :
      ∀ B → inRelativeDomain (terminalOwner B) B

    ownerUnique :
      ∀ B j → inRelativeDomain j B → j ≡ terminalOwner B

    -- Mⱼ(U), Yⱼ, and the scale-j halo relation.  `componentMeetsLargeField`
    -- prevents an empty or detached halo from satisfying the volume bound.
    largeBlock : Nat → Block → Set
    polymerBlock : Polymer → Nat → Block → Set
    componentBlock : Polymer → Nat → Component → Block → Set
    haloContains : Nat → Block → Block → Set

    polymerUsesOnlyOwnedBlocks :
      ∀ Y j B → polymerBlock Y j B → inRelativeDomain j B

    haloCoverage :
      ∀ Y j B → polymerBlock Y j B →
      ∃ λ M → largeBlock j M × haloContains j M B

    componentMeetsLargeField :
      ∀ Y j C →
      (∃ λ B → componentBlock Y j C B) →
      ∃ λ M → largeBlock j M ×
        (∃ λ B → componentBlock Y j C B × haloContains j M B)

    -- These are the directly consumed finite weighted quantities.  A concrete
    -- instantiation must prove `haloCompression`; it may not replace it with a
    -- diameter comparison.
    weightedVolume : Polymer → ℝ
    weightedLargeBlockMass : Polymer → ℝ
    haloCapacity : ℝ
    haloCompression :
      ∀ Y →
      weightedVolume Y ≤ℝ haloCapacity *ℝ weightedLargeBlockMass Y

    -- The P10 score is gauge invariant at this interface.  The threshold and
    -- score lower bound are precisely the data from which the p₀ gain must be
    -- derived by a later ordered-exponential lemma.
    gaugeConfiguration : Set
    score : Nat → gaugeConfiguration → Block → ℝ
    scoreGaugeInvariant : Set
    threshold : Nat → ℝ
    weightedScore : gaugeConfiguration → Polymer → ℝ
    largeBlockMeetsThreshold :
      ∀ U j B → largeBlock j B → threshold j ≤ℝ score j U B
    thresholdScoreLowerBound :
      ∀ U Y → Set

    -- The five numerical quantities requested by the corrected route are not
    -- free labels: each is a function on this carrier, with a theorem field
    -- giving its source-side derivation.  `largeFieldDensityGain` is kept
    -- primitive here because RealAnalysisAxioms has no division or exponential
    -- monotonicity laws from which b·p₀²/ν can be formed internally yet.
    coreVolumeDecay : Nat → ℝ
    scoreDecay : Nat → ℝ
    localisationLoss : Nat → ℝ
    attachmentAnchorBound : Nat → ℝ
    largeFieldDensityGain : Nat → ℝ

    coreVolumeDecayDerived : ∀ k → Set
    scoreDecayDerived : ∀ k → Set
    localisationLossDerived : ∀ k → Set
    attachmentAnchorBoundDerived : ∀ k → Set
    largeFieldDensityGainDerived : ∀ k → Set

    componentActivity : Nat → gaugeConfiguration → Polymer → ℝ
    componentActivityBound :
      ∀ k U Y → Set

    weightedPolymerSuppression :
      ∀ k U Y → Set

    fibreResummationBound :
      ∀ k Y → Set

    strictKPMargin :
      ∀ k → Set

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus

open P10P11WeightedRelativeDomainCarrier public

-- A fully inhabited instance is the theorem-critical replacement for the old
-- string-only shell-bound surface.  The implication fields below are where the
-- missing ordered-exponential and finite-enumeration proofs must land.
record P10P11WeightedRelativeDomainClosure
  (carrier : P10P11WeightedRelativeDomainCarrier) : Set₁ where
  open P10P11WeightedRelativeDomainCarrier carrier
  field
    componentwiseToWeightedSuppression :
      ∀ k U Y →
      componentActivityBound k U Y →
      weightedPolymerSuppression k U Y

    weightedSuppressionToFibreBound :
      ∀ k Y →
      fibreResummationBound k Y

    fibreBoundToStrictKP :
      ∀ k →
      strictKPMargin k

open P10P11WeightedRelativeDomainClosure public

-- This is an audit gate, not a mathematical assertion: the current public
-- P10 activity API is length-based and therefore cannot yet inhabit the
-- (1.100) contract; likewise no extracted carrier yet inhabits the relative
-- (1.67)--(1.68) contract.
data P10SourceFaithfulInstantiationState : Set where
  relative-domain-model-unextracted : P10SourceFaithfulInstantiationState
  source-faithful-contract-instantiated : P10SourceFaithfulInstantiationState

currentP10SourceFaithfulInstantiationState :
  P10SourceFaithfulInstantiationState
currentP10SourceFaithfulInstantiationState =
  relative-domain-model-unextracted

currentP10SourceFaithfulSource : SourceAuthorityId
currentP10SourceFaithfulSource = eriksson-2602-0069

currentP10SourceFaithfulStatus : VerificationStatus
currentP10SourceFaithfulStatus = paperImport

currentP10P11WeightedRelativeDomainClosureAvailable : Bool
currentP10P11WeightedRelativeDomainClosureAvailable = false
