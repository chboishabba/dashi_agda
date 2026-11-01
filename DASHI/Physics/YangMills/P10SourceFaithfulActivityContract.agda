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
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base renaming (ℕ to Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; ∃)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _≤ℝ_
  ; _+ℝ_
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

    -- Mⱼ(U), Yⱼ, and the scale-j halo relation.  Large-field membership is
    -- configuration-dependent: a block cannot be declared large uniformly
    -- over all gauge configurations merely because a score is available.
    gaugeConfiguration : Set
    largeBlock : gaugeConfiguration → Nat → Block → Set
    polymerBlock : Polymer → Nat → Block → Set
    componentBlock : Polymer → Nat → Component → Block → Set
    haloContains : Nat → Block → Block → Set

    -- This is the finite connected-component carrier used by the source
    -- phrase "components".  `componentBlock` alone is not enough: these
    -- fields rule out an arbitrary unrelated relation being called a
    -- component decomposition.
    components : Polymer → Nat → List Component
    coversPolymer :
      ∀ Y j B → polymerBlock Y j B →
      ∃ λ C → C ∈ components Y j × componentBlock Y j C B
    uniqueComponent :
      ∀ Y j C D B → C ∈ components Y j → D ∈ components Y j →
      componentBlock Y j C B → componentBlock Y j D B → C ≡ D
    componentConnected :
      ∀ Y j C → C ∈ components Y j → Set
    componentMaximal :
      ∀ Y j C → C ∈ components Y j → Set

    polymerUsesOnlyOwnedBlocks :
      ∀ Y j B → polymerBlock Y j B → inRelativeDomain j B

    haloCoverage :
      ∀ U Y j B → polymerBlock Y j B →
      ∃ λ M → largeBlock U j M × haloContains j M B

    -- Literal component contact is deliberately stronger than mere halo
    -- proximity.  If CMP 122 supplies only a path-contact alternative, that
    -- alternative must replace this field in a source-specific instance.
    componentContainsLargeBlock :
      ∀ U Y j C → C ∈ components Y j →
      ∃ λ M → componentBlock Y j C M × largeBlock U j M

    -- These are the directly consumed finite weighted quantities.  A concrete
    -- instantiation must prove `haloCompression`; it may not replace it with a
    -- diameter comparison.
    weightedVolume : Polymer → ℝ
    weightedLargeBlockMass : gaugeConfiguration → Polymer → ℝ
    haloCapacity : Nat → ℝ

    -- A source model must say which scale supplies the weighted mass of a
    -- polymer rather than smuggling a scale choice into an implementation.
    terminalOwnerBlockScale : Polymer → Nat

    haloCompression :
      ∀ U Y →
      weightedVolume Y ≤ℝ
        haloCapacity (terminalOwnerBlockScale Y) *ℝ
        weightedLargeBlockMass U Y

    -- The P10 score is gauge invariant at this interface.  The threshold and
    -- score lower bound are precisely the data from which the p₀ gain must be
    -- derived by a later ordered-exponential lemma.
    score : Nat → gaugeConfiguration → Block → ℝ
    scoreGaugeInvariant : Set
    threshold : Nat → ℝ
    weightedScore : gaugeConfiguration → Polymer → ℝ
    largeBlockMeetsThreshold :
      ∀ U j B → largeBlock U j B → threshold j ≤ℝ score j U B
    thresholdScoreLowerBound :
      ∀ U Y →
      (threshold (terminalOwnerBlockScale Y) *ℝ
       threshold (terminalOwnerBlockScale Y)) *ℝ
      weightedLargeBlockMass U Y ≤ℝ weightedScore U Y

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

    jacobianLoss : Nat → ℝ
    localisationOperatorLoss : Nat → ℝ
    interpolationLoss : Nat → ℝ
    rescalingLoss : Nat → ℝ
    netVolumeDecay : Nat → ℝ

    localisationLossDecomposition : ∀ k →
      localisationLoss k ≡
        jacobianLoss k +ℝ localisationOperatorLoss k +ℝ
        interpolationLoss k +ℝ rescalingLoss k

    -- This division-free comparison is the intended content of the informal
    -- gain b·η²/ν.  It avoids adding division/logarithm infrastructure merely
    -- to state the P10/P11 source boundary.
    densityGainCertified : ∀ k →
      haloCapacity k *ℝ largeFieldDensityGain k ≤ℝ
      scoreDecay k *ℝ
      (threshold k *ℝ threshold k)

    netDecayBalancesLoss : ∀ k →
      netVolumeDecay k +ℝ localisationLoss k ≡
      coreVolumeDecay k +ℝ largeFieldDensityGain k

    componentActivity : Nat → gaugeConfiguration → Polymer → ℝ
    componentActivityBound :
      ∀ k U Y →
      componentActivity k U Y ≤ℝ
        (expℝ (-ℝ (coreVolumeDecay k *ℝ weightedVolume Y)) *ℝ
         expℝ (-ℝ (scoreDecay k *ℝ weightedScore U Y)))

    weightedPolymerSuppression :
      ∀ k U Y →
      componentActivity k U Y ≤ℝ
        expℝ (-ℝ (netVolumeDecay k *ℝ weightedVolume Y))

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
      ∀ k →
      (∀ U Y → weightedPolymerSuppression k U Y) →
      ∀ Y → fibreResummationBound k Y

    fibreBoundToStrictKP :
      ∀ k →
      (∀ Y → fibreResummationBound k Y) →
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
