module DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation where

-- Mathematical bridge for the last step of the CMP 99/CMP 109/CMP 116
-- domain-comparison argument.  This module deliberately contains no source
-- authority, availability, or promotion metadata.  Its conclusion is built
-- from the near and far estimates, rather than stored as a field of a receipt.

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _+ℝ_ ; _-ℝ_ ; -ℝ_ ; _*ℝ_ ; absℝ ; _≤ℝ_
  ; ≤ℝ-refl ; ≤ℝ-trans ; +-mono-≤ ; absZero ; absAddSubadditive
  ; +-identityˡ ; +-identityʳ ; +-assoc ; subSelf ; subAddDistributes )
open import DASHI.Physics.YangMills.BalabanLargeFieldSuppression using
  ( expℝ ; fromNat )

------------------------------------------------------------------------
-- Concrete finite marked resummation
--
-- CMP 109 writes the polarisation kernel as a sum of already twice
-- differentiated local activities E²(X;x,y).  CMP 99 controls one marked
-- random-walk replacement inside such an activity, and CMP 116 supplies the
-- residual tree-weight summability.  The following is the owned finite-sum
-- bridge between those three inputs.  The source estimates remain inputs, but
-- the resummed near-kernel inequality is constructed below.

sumℝ : {A : Set} → (A → ℝ) → List A → ℝ
sumℝ f [] = 0ℝ
sumℝ f (x ∷ xs) = f x +ℝ sumℝ f xs

cong₂ :
  {A B C : Set} →
  (f : A → B → C) →
  {a a′ : A} → {b b′ : B} →
  a ≡ a′ →
  b ≡ b′ →
  f a b ≡ f a′ b′
cong₂ f refl refl = refl

sym :
  {A : Set} →
  {x y : A} →
  x ≡ y →
  y ≡ x
sym refl = refl

sumℝ-++ :
  {A : Set} →
  (f : A → ℝ) →
  (left right : List A) →
  sumℝ f (left ++ right)
    ≡
  sumℝ f left +ℝ sumℝ f right
sumℝ-++ f [] right = sym (+-identityˡ (sumℝ f right))
sumℝ-++ f (x ∷ left) right
  rewrite sumℝ-++ f left right
  | +-assoc (f x) (sumℝ f left) (sumℝ f right) = refl

sumℝ-sub :
  {A : Set} →
  (f g : A → ℝ) →
  (xs : List A) →
  sumℝ f xs -ℝ sumℝ g xs
    ≡
  sumℝ (λ x → f x -ℝ g x) xs
sumℝ-sub f g [] rewrite subSelf 0ℝ = refl
sumℝ-sub f g (x ∷ xs)
  rewrite subAddDistributes (f x) (sumℝ f xs) (g x) (sumℝ g xs)
  | sumℝ-sub f g xs = refl

sumℝ-zero :
  {A : Set} →
  (xs : List A) →
  sumℝ (λ (_ : A) → 0ℝ) xs ≡ 0ℝ
sumℝ-zero [] = refl
sumℝ-zero (x ∷ xs)
  rewrite sumℝ-zero xs = +-identityʳ 0ℝ

sumℝ-commonDifferenceZero :
  {A : Set} →
  (f g : A → ℝ) →
  (xs : List A) →
  (∀ x → x ∈ xs → f x ≡ g x) →
  sumℝ (λ x → f x -ℝ g x) xs ≡ 0ℝ
sumℝ-commonDifferenceZero f g [] common = refl
sumℝ-commonDifferenceZero f g (x ∷ xs) common
  rewrite common x (here refl)
  | subSelf (g x)
  | sumℝ-commonDifferenceZero f g xs
      (λ y y∈xs → common y (there y∈xs)) =
  +-identityʳ 0ℝ

sumℝ-differenceAfterCommonCancellation :
  {A : Set} →
  (f g : A → ℝ) →
  (all common surviving : List A) →
  all ≡ common ++ surviving →
  (∀ x → x ∈ common → f x ≡ g x) →
  sumℝ f all -ℝ sumℝ g all
    ≡
  sumℝ (λ x → f x -ℝ g x) surviving
sumℝ-differenceAfterCommonCancellation f g all common surviving partition commonEq
  rewrite partition
  | sumℝ-++ f common surviving
  | sumℝ-++ g common surviving
  | subAddDistributes
      (sumℝ f common) (sumℝ f surviving)
      (sumℝ g common) (sumℝ g surviving)
  | sumℝ-sub f g common
  | sumℝ-sub f g surviving
  | sumℝ-commonDifferenceZero f g common commonEq =
  +-identityˡ
    (sumℝ (λ x → f x -ℝ g x) surviving)

sumℝ-mono :
  {A : Set} →
  (xs : List A) →
  {f g : A → ℝ} →
  (∀ x → f x ≤ℝ g x) →
  sumℝ f xs ≤ℝ sumℝ g xs
sumℝ-mono [] pointwise = ≤ℝ-refl
sumℝ-mono (x ∷ xs) pointwise =
  +-mono-≤ (pointwise x) (sumℝ-mono xs pointwise)

absSumℝ≤sumAbsℝ :
  {A : Set} →
  (f : A → ℝ) →
  (xs : List A) →
  absℝ (sumℝ f xs) ≤ℝ sumℝ (λ x → absℝ (f x)) xs
absSumℝ≤sumAbsℝ f [] rewrite absZero = ≤ℝ-refl
absSumℝ≤sumAbsℝ f (x ∷ xs) =
  ≤ℝ-trans
    (absAddSubadditive (f x) (sumℝ f xs))
    (+-mono-≤ ≤ℝ-refl (absSumℝ≤sumAbsℝ f xs))

------------------------------------------------------------------------
-- CMP 116 generalized-walk localization of the activity Hessian
--
-- CMP 116 (1.6)--(1.11) expands the nonlocal propagators substituted into
-- the local CMP 109 activity in generalized random walks and then decouples
-- them by the cube parameters s(Δ).  The finite walk lists below are the
-- concrete comparison layer needed before one may use a marked estimate for
-- the complete localised activity.  In particular, the marked distance is
-- attached to a walk footprint, not prematurely to its enclosing activity X.
--
-- `hessianDifferenceBySurvivingTerms` is the finite triangle inequality after
-- the common-footprint contributions have cancelled.  It is deliberately an
-- input from the CMP 99/116 walk expansion, rather than an assertion of the
-- final Hessian estimate.  The theorem below constructs that final estimate
-- from the individual surviving-walk bound and its walk sum.

record MarkedWalkHessianData
    (Domain Background History : Set) : Set₁ where
  field
    Cube Localisation Walk : Set

    -- In CMP 116 (1.6), ω = ((0 , X₀), (α₁ , X₁), …, (αₙ , Xₙ)).
    -- `walkFootprint` is the connected component Y₀ retained after the
    -- s-decoupling of (1.9) into (1.10), not merely the enclosing activity X.
    walkFootprint : Walk → Localisation
    commonRegion : Domain → Domain → Localisation → Set

    localisedHessian :
      ℕ → Domain → Background → History → Localisation → Cube → Cube → ℝ

    -- A common decoupled index family.  Domain dependence is in the value of
    -- a walk contribution, not in its code; this is the source-level pairing
    -- required for termwise common-region cancellation.
    walks :
      ℕ → Background → History → Localisation → Cube → Cube → List Walk

    walkHessianContribution :
      ℕ → Domain → Background → History → Walk → Localisation → Cube → Cube → ℝ

    -- Downstream walk expansion consumed by this finite resummation.  It is
    -- not, by itself, CMP 116 (1.23): that source expression first takes two
    -- field variations and then a multivariable Cauchy coefficient in the
    -- independent decoupling parameters.  The source-shaped construction of
    -- this equality belongs in BalabanDecoupledActivityHessian; this module
    -- starts only once that construction has produced scalar walk terms.
    hessianAsWalkSum :
      ∀ scale Ω U history X x y →
      localisedHessian scale Ω U history X x y
        ≡
      sumℝ
        (λ ω → walkHessianContribution scale Ω U history ω X x y)
        (walks scale U history X x y)

    -- A footprint wholly in the common region contributes the same local
    -- term for both domain sequences.  The source proof establishes this by
    -- equality of the restricted background data, not by equality of the
    -- complete nonlocal propagators.
    commonWalkCancels :
      ∀ scale Ω Ω′ U history X x y ω →
      commonRegion Ω Ω′ (walkFootprint ω) →
      walkHessianContribution scale Ω U history ω X x y
        ≡
      walkHessianContribution scale Ω′ U history ω X x y

    -- Equation (1.10) leaves only the connected component carrying the
    -- coefficient cube.  For a comparison, CMP 99 partitions the common
    -- generalized-walk index into the terms wholly inside the common region
    -- and the terms whose footprint reaches the discrepancy.
    commonWalks :
      ℕ → Domain → Domain → Background → History → Localisation → Cube → Cube → List Walk

    survivingWalks :
      ℕ → Domain → Domain → Background → History → Localisation → Cube → Cube → List Walk

    walkPartition :
      ∀ scale Ω Ω′ U history X x y →
      walks scale U history X x y
        ≡
      commonWalks scale Ω Ω′ U history X x y
        ++
      survivingWalks scale Ω Ω′ U history X x y

    commonWalksAreCommon :
      ∀ scale Ω Ω′ U history X x y ω →
      ω ∈ commonWalks scale Ω Ω′ U history X x y →
      commonRegion Ω Ω′ (walkFootprint ω)

    markedWalkMajorant :
      ℕ → Domain → Domain → Background → History → Walk → Localisation → Cube → Cube → ℝ

    -- CMP 99's surviving-walk estimate: each changed term has a factor
    -- controlled by the distance from that walk's footprint to the domain
    -- discrepancy.  The tree-length loss is retained in the majorant for the
    -- subsequent CMP 116 summation.
    survivingWalkMarkedBound :
      ∀ scale Ω Ω′ U history ω X x y →
      absℝ
        (walkHessianContribution scale Ω U history ω X x y
          -ℝ walkHessianContribution scale Ω′ U history ω X x y)
        ≤ℝ
      markedWalkMajorant scale Ω Ω′ U history ω X x y

    hessianMarkedMajorant :
      ℕ → Domain → Domain → Background → History → Localisation → Cube → Cube → ℝ

    -- CMP 116 (1.23) is the differentiated decoupled term.  Its estimate
    -- (1.24), supplemented by (1.25), retains an exponential in the
    -- decoupling component together with exp (- κ dⱼ (X)).  This field is
    -- precisely the finite surviving-walk sum after that residual positive
    -- tree-length rate has been retained; it is not a KP reconstruction.
    markedWalkSummability :
      ∀ scale Ω Ω′ U history X x y →
      sumℝ
        (λ ω → markedWalkMajorant scale Ω Ω′ U history ω X x y)
        (survivingWalks scale Ω Ω′ U history X x y)
        ≤ℝ
      hessianMarkedMajorant scale Ω Ω′ U history X x y

open MarkedWalkHessianData public

hessianDifferenceAsSurvivingWalkSum :
  ∀ {Domain Background History}
  (walkData : MarkedWalkHessianData Domain Background History)
  scale Ω Ω′ U history X x y →
  localisedHessian walkData scale Ω U history X x y
    -ℝ localisedHessian walkData scale Ω′ U history X x y
    ≡
  sumℝ
    (λ ω →
      walkHessianContribution walkData scale Ω U history ω X x y
        -ℝ walkHessianContribution walkData scale Ω′ U history ω X x y)
    (survivingWalks walkData scale Ω Ω′ U history X x y)
hessianDifferenceAsSurvivingWalkSum walkData scale Ω Ω′ U history X x y
  rewrite hessianAsWalkSum walkData scale Ω U history X x y
  | hessianAsWalkSum walkData scale Ω′ U history X x y =
  sumℝ-differenceAfterCommonCancellation
    (λ ω → walkHessianContribution walkData scale Ω U history ω X x y)
    (λ ω → walkHessianContribution walkData scale Ω′ U history ω X x y)
    (walks walkData scale U history X x y)
    (commonWalks walkData scale Ω Ω′ U history X x y)
    (survivingWalks walkData scale Ω Ω′ U history X x y)
    (walkPartition walkData scale Ω Ω′ U history X x y)
    (λ ω ω∈common → commonWalkCancels walkData scale Ω Ω′ U history X x y ω
      (commonWalksAreCommon walkData scale Ω Ω′ U history X x y ω ω∈common))

markedLocalisedHessianEstimate :
  ∀ {Domain Background History}
  (walkData : MarkedWalkHessianData Domain Background History)
  scale Ω Ω′ U history X x y →
  absℝ
    (localisedHessian walkData scale Ω U history X x y
      -ℝ localisedHessian walkData scale Ω′ U history X x y)
    ≤ℝ
  hessianMarkedMajorant walkData scale Ω Ω′ U history X x y
markedLocalisedHessianEstimate walkData scale Ω Ω′ U history X x y
  rewrite hessianDifferenceAsSurvivingWalkSum
    walkData scale Ω Ω′ U history X x y =
  ≤ℝ-trans
    (absSumℝ≤sumAbsℝ
      (λ ω →
        walkHessianContribution walkData scale Ω U history ω X x y
          -ℝ walkHessianContribution walkData scale Ω′ U history ω X x y)
      (survivingWalks walkData scale Ω Ω′ U history X x y))
    (≤ℝ-trans
      (sumℝ-mono
        (survivingWalks walkData scale Ω Ω′ U history X x y)
        (λ ω → survivingWalkMarkedBound
          walkData scale Ω Ω′ U history ω X x y))
      (markedWalkSummability walkData scale Ω Ω′ U history X x y))

record MarkedLocalisationResummationData
    (Domain Background History : Set) : Set₁ where
  field
    Cube Localisation : Set

    localisations : ℕ → Cube → Cube → List Localisation
    E² : ℕ → Domain → Background → History → Localisation → Cube → Cube → ℝ
    polarisation : ℕ → Domain → Background → History → Cube → Cube → ℝ

    -- The following three real-valued functions are the literal analytic
    -- quantities to be bounded: a marked CMP 99 walk majorant, its charged
    -- (collar-or-large-localisation) majorant, and the ordinary spatial/
    -- collar envelope after CMP 116 resummation.
    markedMajorant chargedMajorant :
      ℕ → Domain → Domain → Background → History → Localisation → Cube → Cube → ℝ
    nearEnvelope : ℕ → Domain → Domain → Background → History → Cube → Cube → ℝ

    -- This is the ordinary finite triangle inequality for the explicit CMP
    -- 109 localisation sum.  It is deliberately weaker than the desired
    -- near estimate: it contains no collar decay and no resummation result.
    polarisationDifferenceByLocalisedTerms :
      ∀ scale Ω Ω′ U history x y →
      absℝ (polarisation scale Ω U history x y
        -ℝ polarisation scale Ω′ U history x y)
        ≤ℝ
      sumℝ
        (λ X → absℝ
          (E² scale Ω U history X x y
            -ℝ E² scale Ω′ U history X x y))
        (localisations scale x y)

    -- Source-specific marked estimate for the complete differentiated local
    -- activity.  CMP 109 (4.35) is
    --
    --   ⟨ δ²_H E (X , 1) , Hⱼ(D₀) , Hⱼ(D₀) ⟩.
    --
    -- Thus a comparison which fixes the local activity E(X , 1) and changes
    -- only the background/propagator construction may use the two Hⱼ-factor
    -- telescope.  A comparison which also changes that local activity needs
    -- a marked Hessian-difference term.  This primitive deliberately covers
    -- both cases rather than asserting either one without its source premise.
    markedLocalisedEstimate :
      ∀ scale Ω Ω′ U history X x y →
      absℝ (E² scale Ω U history X x y
        -ℝ E² scale Ω′ U history X x y)
        ≤ℝ
      markedMajorant scale Ω Ω′ U history X x y

    -- Owned charging target: a surviving marked walk either pays its marked
    -- distance or its localisation tree length.  The actual block-scale
    -- geometry proving this inequality is the remaining CMP 99/109 lemma.
    markedDistanceOrLargeLocalisation :
      ∀ scale Ω Ω′ U history X x y →
      markedMajorant scale Ω Ω′ U history X x y
        ≤ℝ
      chargedMajorant scale Ω Ω′ U history X x y

    -- CMP 116, applied only after the residual decay has been retained.
    -- This is a summability input over the explicit finite localisation list,
    -- not a prepackaged statement about the polarisation kernel.
    chargedLocalisationSummability :
      ∀ scale Ω Ω′ U history x y →
      sumℝ (λ X → chargedMajorant scale Ω Ω′ U history X x y)
        (localisations scale x y)
        ≤ℝ
      nearEnvelope scale Ω Ω′ U history x y

open MarkedLocalisationResummationData public

markedResummedNearKernel :
  ∀ {Domain Background History}
  (resummation : MarkedLocalisationResummationData Domain Background History)
  scale Ω Ω′ U history x y →
  absℝ (polarisation resummation scale Ω U history x y
    -ℝ polarisation resummation scale Ω′ U history x y)
    ≤ℝ
  nearEnvelope resummation scale Ω Ω′ U history x y
markedResummedNearKernel resummation scale Ω Ω′ U history x y =
  ≤ℝ-trans
    (polarisationDifferenceByLocalisedTerms resummation scale Ω Ω′ U history x y)
    (≤ℝ-trans
      (sumℝ-mono
        (localisations resummation scale x y)
        (λ X → ≤ℝ-trans
          (markedLocalisedEstimate resummation scale Ω Ω′ U history X x y)
          (markedDistanceOrLargeLocalisation resummation scale Ω Ω′ U history X x y)))
      (chargedLocalisationSummability resummation scale Ω Ω′ U history x y))

------------------------------------------------------------------------
-- From the resummed kernel to the near coordinate moment
--
-- This is kept separate because the exact coordinate weight in CMP 109
-- (5.42) depends on the Fourier/derivative convention.  Nevertheless its
-- finite near-region sum is now an explicit object, rather than a field
-- asserting the completed near-moment conclusion.

record MarkedNearMomentData
    (Domain Background History : Set) : Set₁ where
  field
    resummation : MarkedLocalisationResummationData Domain Background History
    origin : Cube resummation

    nearCoordinates :
      ℕ → Domain → Domain → Cube resummation → List (Cube resummation)

    collarRadiusFor : Domain → Domain → ℕ

    nearContribution :
      ℕ → Domain → Domain → Background → History → ℝ

    coordinateMajorant :
      ℕ → Domain → Domain → Background → History → Cube resummation → ℝ

    nearEnvelopeConstant nearEnvelopeRate : ℝ

    -- The triangle/coordinate-weight step for the literal finite moment.
    -- It is strictly before the marked resummation estimate: no collar decay
    -- has been concluded here.
    nearContributionByCoordinates :
      ∀ scale Ω Ω′ U history →
      nearContribution scale Ω Ω′ U history
        ≤ℝ
      sumℝ
        (coordinateMajorant scale Ω Ω′ U history)
        (nearCoordinates scale Ω Ω′ origin)

    -- A coordinate term is controlled by the already resummed marked kernel.
    coordinateMajorantByNearKernel :
      ∀ scale Ω Ω′ U history x →
      coordinateMajorant scale Ω Ω′ U history x
        ≤ℝ
      nearEnvelope resummation scale Ω Ω′ U history origin x

    -- This is the elementary finite coordinate-moment estimate, after the
    -- near collar factor has been extracted.  Its proof is where the exact
    -- |x|² convention and the finite moment S(δ) are instantiated.
    resummedNearEnvelopeMoment :
      ∀ scale Ω Ω′ U history →
      sumℝ
        (nearEnvelope resummation scale Ω Ω′ U history origin)
        (nearCoordinates scale Ω Ω′ origin)
        ≤ℝ
      nearEnvelopeConstant *ℝ expℝ
        (-ℝ (nearEnvelopeRate *ℝ fromNat
          (collarRadiusFor Ω Ω′)))

open MarkedNearMomentData public

nearWeightedMomentFromMarkedResummation :
  ∀ {Domain Background History}
  (moment : MarkedNearMomentData Domain Background History)
  scale Ω Ω′ U history →
  nearContribution moment scale Ω Ω′ U history
    ≤ℝ
  nearEnvelopeConstant moment *ℝ expℝ
    (-ℝ (nearEnvelopeRate moment *ℝ fromNat
      (collarRadiusFor moment Ω Ω′)))
nearWeightedMomentFromMarkedResummation moment scale Ω Ω′ U history =
  ≤ℝ-trans
    (nearContributionByCoordinates moment scale Ω Ω′ U history)
    (≤ℝ-trans
      (sumℝ-mono
        (nearCoordinates moment scale Ω Ω′ (origin moment))
        (coordinateMajorantByNearKernel moment scale Ω Ω′ U history))
      (resummedNearEnvelopeMoment moment scale Ω Ω′ U history))

-- Legacy compatibility endgame.  It retains the former opaque
-- `nearWeightedMoment` input for clients that have not migrated.  New work
-- must use `ConcreteMarkedPolarisationTailData` and
-- `concreteBetaDomainTail` below, where the near moment is constructed.
--
-- `nearWeightedMoment` is the result of the genuinely source-specific
-- calculation:
--
--   marked CMP 99 walk difference
--   + CMP 109 differentiated local activity
--   + CMP 116 residual tree-length summability.
--
-- `farWeightedMoment` uses the ordinary spatial decay of the two resummed
-- kernels.  The two contributions need not be literal positive summands; the
-- source proof supplies the displayed triangle/splitting inequality.
record LegacyMarkedPolarisationMomentData
    (Domain Background History : Set) : Set₁ where
  field
    betaMoment : ℕ → Domain → Background → History → ℝ
    collarRadius : Domain → Domain → ℕ

    nearContribution farContribution :
      ℕ → Domain → Domain → Background → History → ℝ

    nearConstant nearRate farConstant farRate : ℝ
    tailConstant tailRate : ℝ

    momentSplit :
      ∀ scale Ω Ω′ U history →
      absℝ (betaMoment scale Ω U history -ℝ betaMoment scale Ω′ U history)
        ≤ℝ
      nearContribution scale Ω Ω′ U history
        +ℝ farContribution scale Ω Ω′ U history

    nearWeightedMoment :
      ∀ scale Ω Ω′ U history →
      nearContribution scale Ω Ω′ U history
        ≤ℝ
      nearConstant *ℝ expℝ
        (-ℝ (nearRate *ℝ fromNat (collarRadius Ω Ω′)))

    farWeightedMoment :
      ∀ scale Ω Ω′ U history →
      farContribution scale Ω Ω′ U history
        ≤ℝ
      farConstant *ℝ expℝ
        (-ℝ (farRate *ℝ fromNat (collarRadius Ω Ω′)))

    -- This is the elementary real-analysis endgame.  It is intentionally
    -- separate from marked resummation: one may use any
    -- `tailRate < min nearRate farRate`, with the polynomial far-tail factor
    -- absorbed into `tailConstant`.
    mergeNearFarDecay :
      ∀ radius →
      nearConstant *ℝ expℝ (-ℝ (nearRate *ℝ fromNat radius))
        +ℝ
      farConstant *ℝ expℝ (-ℝ (farRate *ℝ fromNat radius))
        ≤ℝ
      tailConstant *ℝ expℝ (-ℝ (tailRate *ℝ fromNat radius))

open LegacyMarkedPolarisationMomentData public

-- This is an actual construction of the beta-domain-tail conclusion.  The
-- remaining work is concentrated in `nearWeightedMoment`, not hidden in this
-- theorem's output.
legacyBetaDomainTail :
  ∀ {Domain Background History}
  (momentData : LegacyMarkedPolarisationMomentData Domain Background History)
  scale Ω Ω′ U history →
  absℝ
    (betaMoment momentData scale Ω U history
      -ℝ betaMoment momentData scale Ω′ U history)
    ≤ℝ
  tailConstant momentData *ℝ expℝ
    (-ℝ (tailRate momentData *ℝ fromNat
      (collarRadius momentData Ω Ω′)))
legacyBetaDomainTail momentData scale Ω Ω′ U history =
  ≤ℝ-trans
    (momentSplit momentData scale Ω Ω′ U history)
    (≤ℝ-trans
      (+-mono-≤
        (nearWeightedMoment momentData scale Ω Ω′ U history)
        (farWeightedMoment momentData scale Ω Ω′ U history))
      (mergeNearFarDecay momentData (collarRadius momentData Ω Ω′)))

------------------------------------------------------------------------
-- Canonical endgame: the near moment is constructed from marked resummation

record ConcreteMarkedPolarisationTailData
    (Domain Background History : Set) : Set₁ where
  field
    nearMoment : MarkedNearMomentData Domain Background History

    betaMoment : ℕ → Domain → Background → History → ℝ
    farContribution : ℕ → Domain → Domain → Background → History → ℝ
    farConstant farRate tailConstant tailRate : ℝ

    momentSplit :
      ∀ scale Ω Ω′ U history →
      absℝ (betaMoment scale Ω U history -ℝ betaMoment scale Ω′ U history)
        ≤ℝ
      nearContribution nearMoment scale Ω Ω′ U history
        +ℝ farContribution scale Ω Ω′ U history

    farWeightedMoment :
      ∀ scale Ω Ω′ U history →
      farContribution scale Ω Ω′ U history
        ≤ℝ
      farConstant *ℝ expℝ
        (-ℝ (farRate *ℝ fromNat
          (collarRadiusFor nearMoment Ω Ω′)))

    mergeNearFarDecay :
      ∀ radius →
      nearEnvelopeConstant nearMoment *ℝ expℝ
        (-ℝ (nearEnvelopeRate nearMoment *ℝ fromNat radius))
        +ℝ
      farConstant *ℝ expℝ (-ℝ (farRate *ℝ fromNat radius))
        ≤ℝ
      tailConstant *ℝ expℝ (-ℝ (tailRate *ℝ fromNat radius))

open ConcreteMarkedPolarisationTailData public

concreteBetaDomainTail :
  ∀ {Domain Background History}
  (tailData : ConcreteMarkedPolarisationTailData Domain Background History)
  scale Ω Ω′ U history →
  absℝ
    (betaMoment tailData scale Ω U history
      -ℝ betaMoment tailData scale Ω′ U history)
    ≤ℝ
  tailConstant tailData *ℝ expℝ
    (-ℝ (tailRate tailData *ℝ fromNat
      (collarRadiusFor (nearMoment tailData) Ω Ω′)))
concreteBetaDomainTail tailData scale Ω Ω′ U history =
  ≤ℝ-trans
    (momentSplit tailData scale Ω Ω′ U history)
    (≤ℝ-trans
      (+-mono-≤
        (nearWeightedMomentFromMarkedResummation
          (nearMoment tailData) scale Ω Ω′ U history)
        (farWeightedMoment tailData scale Ω Ω′ U history))
      (mergeNearFarDecay tailData
        (collarRadiusFor (nearMoment tailData) Ω Ω′)))
