module DASHI.Physics.YangMills.CompactLieGroupCore where

-- Generic algebraic carrier for the Yang--Mills group parameter.  Nothing in
-- this module assumes quaternions, matrices of a fixed rank, or SU(2).

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)

record Group {g : Level} (G : Set g) : Set (lsuc g) where
  field
    identity : G
    multiply : G → G → G
    inverse : G → G

    multiplyAssociative :
      ∀ x y z → multiply (multiply x y) z ≡ multiply x (multiply y z)
    identityLeft : ∀ x → multiply identity x ≡ x
    identityRight : ∀ x → multiply x identity ≡ x
    inverseLeft : ∀ x → multiply (inverse x) x ≡ identity
    inverseRight : ∀ x → multiply x (inverse x) ≡ identity

open Group public

record LieAlgebra {a : Level} (𝔤 : Set a) : Set (lsuc a) where
  field
    zero : 𝔤
    add : 𝔤 → 𝔤 → 𝔤
    negate : 𝔤 → 𝔤
    bracket : 𝔤 → 𝔤 → 𝔤

    addAssociative : ∀ x y z → add (add x y) z ≡ add x (add y z)
    addCommutative : ∀ x y → add x y ≡ add y x
    zeroLeft : ∀ x → add zero x ≡ x
    additiveInverse : ∀ x → add (negate x) x ≡ zero

    bracketAlternating : ∀ x → bracket x x ≡ zero
    bracketAddLeft :
      ∀ x y z → bracket (add x y) z ≡ add (bracket x z) (bracket y z)
    bracketAddRight :
      ∀ x y z → bracket x (add y z) ≡ add (bracket x y) (bracket x z)
    jacobi :
      ∀ x y z →
      add (bracket x (bracket y z))
        (add (bracket y (bracket z x)) (bracket z (bracket x y))) ≡ zero

open LieAlgebra public

record CompactSimpleLieGroup
    {g a : Level}
    (G : Set g)
    (𝔤 : Set a) : Set (lsuc (g ⊔ a)) where
  field
    group : Group G
    algebra : LieAlgebra 𝔤

    exp : 𝔤 → G
    log : G → 𝔤
    Ad : G → 𝔤 → 𝔤

    adjointIdentity : ∀ X → Ad (identity group) X ≡ X
    adjointProduct :
      ∀ x y X → Ad (multiply group x y) X ≡ Ad x (Ad y X)
    adjointBracket :
      ∀ x X Y →
      Ad x (bracket algebra X Y) ≡
      bracket algebra (Ad x X) (Ad x Y)

    ConjugatesExponentials : Set (g ⊔ a)
    conjugatesExponentials : ConjugatesExponentials

    Compact : Set g
    Connected : Set g
    SimpleLieAlgebra : Set a
    compact : Compact
    connected : Connected
    simpleLieAlgebra : SimpleLieAlgebra

open CompactSimpleLieGroup public

record LieGroupHomomorphism
    {g h : Level}
    {G : Set g} {H : Set h}
    (source : Group G)
    (target : Group H) : Set (lsuc (g ⊔ h)) where
  field
    map : G → H
    preservesIdentity : map (identity source) ≡ identity target
    preservesMultiply :
      ∀ x y → map (multiply source x y) ≡ multiply target (map x) (map y)

open LieGroupHomomorphism public

record LieAlgebraHomomorphism
    {a b : Level}
    {𝔤 : Set a} {𝔥 : Set b}
    (source : LieAlgebra 𝔤)
    (target : LieAlgebra 𝔥) : Set (lsuc (a ⊔ b)) where
  field
    map : 𝔤 → 𝔥
    preservesZero : map (zero source) ≡ zero target
    preservesAdd : ∀ X Y → map (add source X Y) ≡ add target (map X) (map Y)
    preservesBracket :
      ∀ X Y → map (bracket source X Y) ≡ bracket target (map X) (map Y)
