module DASHI.Physics.YangMills.CompactLieAnalyticPackage where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _≤ℝ_; _<ℝ_)
open import DASHI.Physics.YangMills.CompactLieGroupCore
open import DASHI.Physics.YangMills.CompactLieLinearAlgebra
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Explicit standard-analysis theorem surfaces.  Their mathematical existence
-- is classical for finite-dimensional compact Lie groups; the repository marks
-- the imported construction boundary rather than pretending it was rebuilt.
------------------------------------------------------------------------

record QuantitativeInvariantMetric
    {g a : Level}
    {G : Set g} {𝔤 : Set a}
    (H : Group G)
    (L : LieAlgebra 𝔤) : Set (lsuc (g ⊔ a)) where
  field
    inner : 𝔤 → 𝔤 → ℝ
    norm : 𝔤 → ℝ
    distance : G → G → ℝ
    Ad : G → 𝔤 → 𝔤

    innerSymmetric : ∀ X Y → inner X Y ≡ inner Y X
    normNonnegative : ∀ X → 0ℝ ≤ℝ norm X
    adjointIsometry : ∀ g X → norm (Ad g X) ≡ norm X
    distanceLeftInvariant : ∀ g x y →
      distance (multiply H g x) (multiply H g y) ≡ distance x y
    distanceRightInvariant : ∀ g x y →
      distance (multiply H x g) (multiply H y g) ≡ distance x y

open QuantitativeInvariantMetric public

record QuantitativeLieChart
    {g a : Level}
    {G : Set g} {𝔤 : Set a}
    (H : Group G)
    (L : LieAlgebra 𝔤)
    (R : RealLieAlgebra 𝔤 L)
    (M : QuantitativeInvariantMetric H L) : Set (lsuc (g ⊔ a)) where
  field
    exp : 𝔤 → G
    log : G → 𝔤
    radius expLipschitzConstant logLipschitzConstant : ℝ
    lowerChartConstant upperChartConstant : ℝ

    InAlgebraBall : 𝔤 → Set
    InGroupBall : G → Set

    radiusPositive : 0ℝ <ℝ radius
    expMapsBall : ∀ X → InAlgebraBall X → InGroupBall (exp X)
    logMapsBall : ∀ g → InGroupBall g → InAlgebraBall (log g)
    logExp : ∀ X → InAlgebraBall X → log (exp X) ≡ X
    expLog : ∀ g → InGroupBall g → exp (log g) ≡ g

    expLipschitz : ∀ X Y →
      InAlgebraBall X → InAlgebraBall Y →
      distance M (exp X) (exp Y)
      ≤ℝ expLipschitzConstant *ℝ
        norm M (add L X (negate L Y))

    logLipschitz : ∀ x y →
      InGroupBall x → InGroupBall y →
      norm M (add L (log x) (negate L (log y)))
      ≤ℝ logLipschitzConstant *ℝ distance M x y

open QuantitativeLieChart public

record QuantitativeBCH
    {g a : Level}
    {G : Set g} {𝔤 : Set a}
    (H : Group G)
    (L : LieAlgebra 𝔤)
    (R : RealLieAlgebra 𝔤 L)
    (M : QuantitativeInvariantMetric H L)
    (C : QuantitativeLieChart H L R M) : Set (lsuc (g ⊔ a)) where
  field
    half : ℝ
    halfPlusHalf : half +ℝ half ≡ 1ℝ
    bch remainder3 : 𝔤 → 𝔤 → 𝔤
    remainderConstant lipschitzConstant : ℝ

    InBCHDomain : 𝔤 → 𝔤 → Set
    bchRepresentsProduct : ∀ X Y →
      InBCHDomain X Y →
      exp C (bch X Y) ≡ multiply H (exp C X) (exp C Y)

    bchExpansion : ∀ X Y →
      InBCHDomain X Y →
      bch X Y ≡
      add L X
        (add L Y
          (add L
            (scale R half (bracket L X Y))
            (remainder3 X Y)))

    remainderBound : ∀ X Y →
      InBCHDomain X Y →
      norm M (remainder3 X Y)
      ≤ℝ
      remainderConstant *ℝ
        ((norm M X +ℝ norm M Y) *ℝ
          ((norm M X +ℝ norm M Y) *ℝ (norm M X +ℝ norm M Y)))

open QuantitativeBCH public

record NormalizedHaarTheory
    {g : Level}
    {G : Set g}
    (H : Group G) : Set (lsuc g) where
  field
    Integrable : (G → ℝ) → Set
    integral : (f : G → ℝ) → Integrable f → ℝ
    constantOneIntegrable : Integrable (λ _ → 1ℝ)
    normalized : integral (λ _ → 1ℝ) constantOneIntegrable ≡ 1ℝ

    leftTranslate : G → (G → ℝ) → G → ℝ
    rightTranslate : G → (G → ℝ) → G → ℝ
    leftTranslateIntegrable : ∀ g f → Integrable f → Integrable (leftTranslate g f)
    rightTranslateIntegrable : ∀ g f → Integrable f → Integrable (rightTranslate g f)
    leftInvariant : ∀ g f (proof : Integrable f) →
      integral (leftTranslate g f) (leftTranslateIntegrable g f proof)
      ≡ integral f proof
    rightInvariant : ∀ g f (proof : Integrable f) →
      integral (rightTranslate g f) (rightTranslateIntegrable g f proof)
      ≡ integral f proof

open NormalizedHaarTheory public

record PeterWeylCharacterTheory
    {g : Level}
    {G : Set g}
    (H : Group G)
    (haar : NormalizedHaarTheory H) : Set (lsuc g) where
  field
    Representation MatrixIndex : Set
    representationDimension : Representation → Nat
    matrixCoefficient : Representation → MatrixIndex → MatrixIndex → G → ℝ
    character : Representation → G → ℝ
    normalizedCharacter : Representation → G → ℝ

    Orthogonality : Set
    PeterWeylComplete : Set
    WeylIntegrationFormula : Set
    CharacterAbsoluteBound : Set

    orthogonality : Orthogonality
    peterWeylComplete : PeterWeylComplete
    weylIntegrationFormula : WeylIntegrationFormula
    characterAbsoluteBound : CharacterAbsoluteBound

open PeterWeylCharacterTheory public

record StandardCompactLieAnalysis
    {g a : Level}
    {G : Set g} {𝔤 : Set a}
    (H : Group G)
    (L : LieAlgebra 𝔤)
    (R : RealLieAlgebra 𝔤 L) : Set (lsuc (g ⊔ a)) where
  field
    metric : QuantitativeInvariantMetric H L
    chart : QuantitativeLieChart H L R metric
    bch : QuantitativeBCH H L R metric chart
    haar : NormalizedHaarTheory H
    characters : PeterWeylCharacterTheory H haar

open StandardCompactLieAnalysis public

standardCompactLieAnalysisLevel : ProofLevel
standardCompactLieAnalysisLevel = standardImported
