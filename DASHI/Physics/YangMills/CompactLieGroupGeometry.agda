module DASHI.Physics.YangMills.CompactLieGroupGeometry where

-- Quantitative geometric data used by scale-uniform lattice Yang--Mills
-- arguments.  Constants may depend on the compact simple group, but not on the
-- lattice scale, volume, block, or background field.

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieGroupCore

record OrderedScalar {s : Level} (Scalar : Set s) : Set (lsuc s) where
  field
    zeroS oneS : Scalar
    addS multiplyS : Scalar → Scalar → Scalar
    _≤S_ : Scalar → Scalar → Set s
    nonnegativeOne : zeroS ≤S oneS

open OrderedScalar public

record InvariantLieMetric
    {g a s : Level}
    {G : Set g} {𝔤 : Set a} {Scalar : Set s}
    (K : CompactSimpleLieGroup G 𝔤)
    (S : OrderedScalar Scalar) : Set (lsuc (g ⊔ a ⊔ s)) where
  field
    inner : 𝔤 → 𝔤 → Scalar
    norm : 𝔤 → Scalar
    distance : G → G → Scalar

    innerSymmetric : ∀ X Y → inner X Y ≡ inner Y X
    normNonnegative : ∀ X → _≤S_ S (zeroS S) (norm X)
    adjointIsometry : ∀ x X → norm (Ad K x X) ≡ norm X
    distanceLeftInvariant :
      ∀ x y z →
      distance (multiply (group K) x y) (multiply (group K) x z) ≡
      distance y z
    distanceRightInvariant :
      ∀ x y z →
      distance (multiply (group K) y x) (multiply (group K) z x) ≡
      distance y z

open InvariantLieMetric public

record UniformLieChart
    {g a s : Level}
    {G : Set g} {𝔤 : Set a} {Scalar : Set s}
    (K : CompactSimpleLieGroup G 𝔤)
    (S : OrderedScalar Scalar)
    (M : InvariantLieMetric K S) : Set (lsuc (g ⊔ a ⊔ s)) where
  field
    radius : Scalar
    InAlgebraBall : 𝔤 → Set (a ⊔ s)
    InGroupBall : G → Set (g ⊔ s)

    expMapsBall : ∀ X → InAlgebraBall X → InGroupBall (exp K X)
    logMapsBall : ∀ x → InGroupBall x → InAlgebraBall (log K x)
    logExp : ∀ X → InAlgebraBall X → log K (exp K X) ≡ X
    expLog : ∀ x → InGroupBall x → exp K (log K x) ≡ x

    dexpNormBound inverseDexpNormBound : Scalar
    bracketNormConstant adjointLipschitzConstant : Scalar

    DexpBound : Set (a ⊔ s)
    InverseDexpBound : Set (a ⊔ s)
    BracketBound : Set (a ⊔ s)
    AdjointLipschitzBound : Set (g ⊔ a ⊔ s)

    dexpBound : DexpBound
    inverseDexpBound : InverseDexpBound
    bracketBound : BracketBound
    adjointLipschitzBound : AdjointLipschitzBound

open UniformLieChart public

record GroupUniformityBoundary : Set₁ where
  field
    GroupConstant Scale Volume Background : Set
    dependsOnlyOnGroup : GroupConstant
    independentOfScale : Scale
    independentOfVolume : Volume
    independentOfBackground : Background

open GroupUniformityBoundary public
