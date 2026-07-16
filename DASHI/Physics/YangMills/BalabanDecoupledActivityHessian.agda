module DASHI.Physics.YangMills.BalabanDecoupledActivityHessian where

-- CMP 116 (1.9)--(1.10) decouples a local activity by parameters s(Δ), while
-- (1.23) takes the field Hessian and then extracts a finite multivariable
-- Cauchy coefficient.  This module keeps those axes separate.  It proves the
-- Cauchy lifting step only: the marked boundary-integrand comparison remains
-- the source-specific analytic theorem still to be constructed.

open import Data.List.Base using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; 1ℝ ; _+ℝ_ ; _-ℝ_ ; _*ℝ_ ; absℝ ; _≤ℝ_
  ; ≤ℝ-refl ; ≤ℝ-trans ; +-mono-≤ ; absZero ; absAddSubadditive
  ; +-identityʳ ; subSelf ; subMulDistributes ; mulSubDistributes
  ; subAddCancelMiddle ; mulOneʳ ; mulZeroʳ ; mulZeroˡ ; oneNonnegative ; mulMonotoneNonnegative
  ; *-distribˡ-+ )
open import DASHI.Foundations.ComplexAxiomatic using (ℂ)
open import DASHI.Foundations.FinitePolydiscCauchyAxioms

------------------------------------------------------------------------
-- Finite factor replacement algebra
--
-- This is the literal one-factor telescope used after CMP 116 expands a
-- decoupled generalized-walk boundary integrand into finitely many factors.
-- It is proved by list induction; no pre-summed integrand comparison is an
-- input here.

productℝ :
  {A : Set} →
  (A → ℝ) → List A → ℝ
productℝ f [] = 1ℝ
productℝ f (x ∷ xs) = f x *ℝ productℝ f xs

sumℝ :
  {A : Set} →
  (A → ℝ) → List A → ℝ
sumℝ f [] = 0ℝ
sumℝ f (x ∷ xs) = f x +ℝ sumℝ f xs

cong :
  {A B : Set} →
  {x y : A} →
  (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

trans :
  {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

replaceLeft≤ :
  {a b c : ℝ} →
  a ≡ b → a ≤ℝ c → b ≤ℝ c
replaceLeft≤ refl proof = proof

zeroProduct≤ :
  (a b : ℝ) →
  0ℝ ≤ℝ a → 0ℝ ≤ℝ b →
  0ℝ ≤ℝ a *ℝ b
zeroProduct≤ a b a≥0 b≥0 =
  replaceLeft≤
    (mulZeroˡ 0ℝ)
    (mulMonotoneNonnegative
      {a = 0ℝ} {b = a} {c = 0ℝ} {d = b}
      ≤ℝ-refl a≥0 ≤ℝ-refl b≥0)

productNonnegative :
  {A : Set} →
  (f : A → ℝ) →
  (xs : List A) →
  (∀ x → 0ℝ ≤ℝ f x) →
  0ℝ ≤ℝ productℝ f xs
productNonnegative f [] nonnegative = oneNonnegative
productNonnegative f (x ∷ xs) nonnegative =
  zeroProduct≤
    (f x)
    (productℝ f xs)
    (nonnegative x)
    (productNonnegative f xs nonnegative)

productMono :
  {A : Set} →
  (f g : A → ℝ) →
  (xs : List A) →
  (∀ x → 0ℝ ≤ℝ f x) →
  (∀ x → 0ℝ ≤ℝ g x) →
  (∀ x → f x ≤ℝ g x) →
  productℝ f xs ≤ℝ productℝ g xs
productMono f g [] f≥0 g≥0 f≤g = ≤ℝ-refl
productMono f g (x ∷ xs) f≥0 g≥0 f≤g =
  mulMonotoneNonnegative
    (f≥0 x) (f≤g x)
    (productNonnegative f xs f≥0)
    (productMono f g xs f≥0 g≥0 f≤g)

scaleList :
  ℝ → List ℝ → List ℝ
scaleList a [] = []
scaleList a (q ∷ qs) = (a *ℝ q) ∷ scaleList a qs

sumScaleList :
  (a : ℝ) → (qs : List ℝ) →
  sumℝ (λ q → q) (scaleList a qs)
    ≡
  a *ℝ sumℝ (λ q → q) qs
sumScaleList a [] rewrite mulZeroʳ a = refl
sumScaleList a (q ∷ qs)
  rewrite *-distribˡ-+ a q (sumℝ (λ r → r) qs)
  | sumScaleList a qs = refl

-- Replacement terms preserve the prefix from Ω, replace exactly one factor,
-- and retain the Ω′ suffix through the recursive multiplier.  This orientation
-- is the direct recursive form of the finite product telescope.
replacementTerms :
  {A : Set} →
  (f g : A → ℝ) → List A → List ℝ
replacementTerms f g [] = []
replacementTerms f g (x ∷ xs) =
  ((f x -ℝ g x) *ℝ productℝ f xs)
  ∷
  scaleList (g x) (replacementTerms f g xs)

sym :
  {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

productHeadTelescope :
  (a b p q : ℝ) →
  a *ℝ p -ℝ b *ℝ q
    ≡
  (a -ℝ b) *ℝ p +ℝ b *ℝ (p -ℝ q)
productHeadTelescope a b p q =
  sym
    (trans
      (cong (λ z → z +ℝ b *ℝ (p -ℝ q))
        (subMulDistributes a b p))
      (trans
        (cong (λ z → (a *ℝ p -ℝ b *ℝ p) +ℝ z)
          (mulSubDistributes b p q))
        (subAddCancelMiddle (a *ℝ p) (b *ℝ p) (b *ℝ q))))

factorProductDomainTelescope :
  {A : Set} →
  (f g : A → ℝ) → (xs : List A) →
  productℝ f xs -ℝ productℝ g xs
    ≡
  sumℝ (λ q → q) (replacementTerms f g xs)
factorProductDomainTelescope f g [] rewrite subSelf 1ℝ = refl
factorProductDomainTelescope f g (x ∷ xs)
  rewrite productHeadTelescope
      (f x) (g x) (productℝ f xs) (productℝ g xs)
  | factorProductDomainTelescope f g xs
  | sumScaleList (g x) (replacementTerms f g xs) = refl

sumℝ-mono :
  (qs : List ℝ) →
  (m n : ℝ → ℝ) →
  (∀ q → m q ≤ℝ n q) →
  sumℝ m qs ≤ℝ sumℝ n qs
sumℝ-mono [] m n pointwise = ≤ℝ-refl
sumℝ-mono (q ∷ qs) m n pointwise =
  +-mono-≤ (pointwise q) (sumℝ-mono qs m n pointwise)

absFiniteSum≤sumAbs :
  (qs : List ℝ) →
  absℝ (sumℝ (λ q → q) qs)
    ≤ℝ
  sumℝ absℝ qs
absFiniteSum≤sumAbs [] rewrite absZero = ≤ℝ-refl
absFiniteSum≤sumAbs (q ∷ qs) =
  ≤ℝ-trans
    (absAddSubadditive q (sumℝ (λ r → r) qs))
    (+-mono-≤ ≤ℝ-refl (absFiniteSum≤sumAbs qs))

-- The finite factor-replacement majorant.  A concrete CMP 99/CMP 116
-- boundary calculation supplies `replacementBound` separately for every
-- replacement term; this theorem performs only the finite algebra and
-- triangle inequality which turn those termwise estimates into an integrand
-- envelope.
finiteReplacementSumBound :
  {A : Set} →
  (f g : A → ℝ) →
  (xs : List A) →
  (majorant : ℝ → ℝ) →
  (replacementBound :
    ∀ q →
    absℝ q ≤ℝ majorant q) →
  absℝ (productℝ f xs -ℝ productℝ g xs)
    ≤ℝ
  sumℝ majorant (replacementTerms f g xs)
finiteReplacementSumBound f g xs majorant replacementBound
  rewrite factorProductDomainTelescope f g xs =
  ≤ℝ-trans
    (absFiniteSum≤sumAbs (replacementTerms f g xs))
    (sumℝ-mono
      (replacementTerms f g xs)
      absℝ majorant replacementBound)

record DecoupledActivityHessianData : Set₁ where
  field
    DomainSequence Component FieldVariation : Set

    cauchy : FinitePolydiscCauchyAxioms

    -- These are distinct from the field directions below.  A coefficient is
    -- extracted in the finite component's decoupling variables only.
    -- The generic Cauchy index carrier is the decoupling-cube carrier.
    componentIndices : Component → List (Index cauchy)
    DecouplingAssignment : Set
    parameterAt : DecouplingAssignment → Index cauchy → ℂ

    LocalActivityValue HessianValue : Set
    decoupledActivity :
      DomainSequence → Component → DecouplingAssignment → LocalActivityValue
    secondVariation :
      LocalActivityValue → FieldVariation → FieldVariation → HessianValue

    -- The scalar bridge into the existing marked-walk resummation is supplied
    -- only after this source-shaped coefficient has been constructed.
    hessianValue : HessianValue → Value cauchy

    -- The source integrand before the Cauchy coefficient.  `asFunction`
    -- binds it to the generic finite-polydisc coefficient authority.
    asFunction :
      ∀ Ω Y u v →
      Function cauchy (componentIndices Y)

    assignmentFromCauchy :
      ∀ Ω Y →
      Assignment cauchy → DecouplingAssignment

    evaluatesAsHessianIntegrand :
      ∀ Ω Y u v s →
      evaluate cauchy (asFunction Ω Y u v) s
        ≡
      hessianValue
        (secondVariation
          (decoupledActivity Ω Y
            (assignmentFromCauchy Ω Y s))
          u v)

open DecoupledActivityHessianData public

decoupledHessianCoefficient :
  (D : DecoupledActivityHessianData) →
  DomainSequence D → Component D → FieldVariation D → FieldVariation D →
  Value (cauchy D)
decoupledHessianCoefficient D Ω Y u v =
  coefficient (cauchy D) (componentIndices D Y) (asFunction D Ω Y u v)

-- This is an actual construction from the generic finite-polydisc estimate.
-- It does not assert the marked boundary bound: callers must provide it for
-- the concrete generalized-walk boundary integrands that CMP 99/116 define.
markedBoundaryComparisonLiftsToCoefficient :
  (D : DecoupledActivityHessianData) →
  (Ω Ω′ : DomainSequence D) →
  (Y : Component D) →
  (u v : FieldVariation D) →
  (M : ℝ) →
  BoundaryDifferenceBound (cauchy D)
    (asFunction D Ω Y u v)
    (asFunction D Ω′ Y u v)
    M →
  normValue (cauchy D)
    (FinitePolydiscCauchyAxioms._-Value_ (cauchy D)
      (decoupledHessianCoefficient D Ω Y u v)
      (decoupledHessianCoefficient D Ω′ Y u v))
    ≤ℝ
  M
markedBoundaryComparisonLiftsToCoefficient D Ω Ω′ Y u v M boundary =
  coefficientDifferenceBound (cauchy D)
    (asFunction D Ω Y u v)
    (asFunction D Ω′ Y u v)
    M
    boundary

-- Pointwise boundary control is the form produced by the finite generalized
-- factor telescope above.  This theorem constructs the Cauchy-boundary
-- witness and immediately extracts the marked coefficient estimate.
pointwiseMarkedBoundaryLiftsToCoefficient :
  (D : DecoupledActivityHessianData) →
  (Ω Ω′ : DomainSequence D) →
  (Y : Component D) →
  (u v : FieldVariation D) →
  (M : ℝ) →
  (∀ s →
    normValue (cauchy D)
      (FinitePolydiscCauchyAxioms._-Value_ (cauchy D)
        (evaluate (cauchy D) (asFunction D Ω Y u v) s)
        (evaluate (cauchy D) (asFunction D Ω′ Y u v) s))
      ≤ℝ M) →
  normValue (cauchy D)
    (FinitePolydiscCauchyAxioms._-Value_ (cauchy D)
      (decoupledHessianCoefficient D Ω Y u v)
      (decoupledHessianCoefficient D Ω′ Y u v))
    ≤ℝ
  M
pointwiseMarkedBoundaryLiftsToCoefficient D Ω Ω′ Y u v M pointwise =
  markedBoundaryComparisonLiftsToCoefficient D Ω Ω′ Y u v M
    (boundaryEnvelope (cauchy D)
      (asFunction D Ω Y u v)
      (asFunction D Ω′ Y u v)
      M
      pointwise)
