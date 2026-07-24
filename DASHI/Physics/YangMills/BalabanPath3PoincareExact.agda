module DASHI.Physics.YangMills.BalabanPath3PoincareExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; Positive; pos)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; sqDiff; squareNonnegative; baseBelowBasePlusRemainder; zeroSquare)

------------------------------------------------------------------------
-- Exact one-dimensional seed for block side three.
--
-- For the three-vertex path P3,
--
--   3 E(f) + (Σ f)² = 3 ||f||² + (f0 - 2 f1 + f2)².
--
-- Hence mean zero implies ||f||² ≤ E(f).  This is the tensor seed needed by
-- a P3^4 product-box proof and requires neither trigonometric eigenvalues nor
-- floating point arithmetic.
------------------------------------------------------------------------

threeℚ : ℚ
threeℚ = (1ℚ + 1ℚ) + 1ℚ

record Path3 : Set where
  constructor path3
  field
    p0 p1 p2 : ℚ

open Path3 public

pathSum : Path3 → ℚ
pathSum path = p0 path + (p1 path + p2 path)

pathNormSq : Path3 → ℚ
pathNormSq path = sq (p0 path) + (sq (p1 path) + sq (p2 path))

pathEdgeEnergy : Path3 → ℚ
pathEdgeEnergy path =
  sqDiff (p1 path) (p0 path) + sqDiff (p2 path) (p1 path)

pathHighMode : Path3 → ℚ
pathHighMode path = p0 path - ((1ℚ + 1ℚ) * p1 path) + p2 path

pathRemainder : Path3 → ℚ
pathRemainder path = sq (pathHighMode path)

path3SpectralIdentityRaw : ∀ x0 x1 x2 →
  threeℚ * pathEdgeEnergy (path3 x0 x1 x2)
    + sq (pathSum (path3 x0 x1 x2))
  ≡ threeℚ * pathNormSq (path3 x0 x1 x2)
    + pathRemainder (path3 x0 x1 x2)
path3SpectralIdentityRaw = ℚRing.solve-∀

path3SpectralIdentity : ∀ path →
  threeℚ * pathEdgeEnergy path + sq (pathSum path)
  ≡ threeℚ * pathNormSq path + pathRemainder path
path3SpectralIdentity (path3 x0 x1 x2) =
  path3SpectralIdentityRaw x0 x1 x2

pathRemainderNonnegative : ∀ path → 0ℚ ≤ pathRemainder path
pathRemainderNonnegative path = squareNonnegative (pathHighMode path)

meanZeroPathIdentity : ∀ path →
  pathSum path ≡ 0ℚ →
  threeℚ * pathEdgeEnergy path
  ≡ threeℚ * pathNormSq path + pathRemainder path
meanZeroPathIdentity path meanZero =
  trans
    (sym (ℚP.+-identityʳ (threeℚ * pathEdgeEnergy path)))
    (trans
      (cong
        (λ value → threeℚ * pathEdgeEnergy path + value)
        (sym zeroSquare))
      (trans
        (cong
          (λ value → threeℚ * pathEdgeEnergy path + sq value)
          (sym meanZero))
        (path3SpectralIdentity path)))

meanZeroPathScaledGap : ∀ path →
  pathSum path ≡ 0ℚ →
  threeℚ * pathNormSq path ≤ threeℚ * pathEdgeEnergy path
meanZeroPathScaledGap path meanZero =
  subst
    (λ right → threeℚ * pathNormSq path ≤ right)
    (sym (meanZeroPathIdentity path meanZero))
    (baseBelowBasePlusRemainder
      (threeℚ * pathNormSq path)
      (pathRemainder path)
      (pathRemainderNonnegative path))

instance
  onePositive : Positive 1ℚ
  onePositive = pos

  twoPositive : Positive (1ℚ + 1ℚ)
  twoPositive = ℚP.pos+pos⇒pos 1ℚ 1ℚ

  threePositive : Positive threeℚ
  threePositive = ℚP.pos+pos⇒pos (1ℚ + 1ℚ) 1ℚ

path3Poincare : ∀ path →
  pathSum path ≡ 0ℚ →
  pathNormSq path ≤ pathEdgeEnergy path
path3Poincare path meanZero =
  ℚP.*-cancelˡ-≤-pos threeℚ
    (meanZeroPathScaledGap path meanZero)

------------------------------------------------------------------------
-- Four bond components and finite disjoint families.
------------------------------------------------------------------------

record FourPath3 : Set where
  constructor fourPath3
  field
    pathComponent0 pathComponent1 pathComponent2 pathComponent3 : Path3

open FourPath3 public

record FourPath3AverageZero (paths : FourPath3) : Set where
  constructor fourPathAveragesZero
  field
    path0Zero : pathSum (pathComponent0 paths) ≡ 0ℚ
    path1Zero : pathSum (pathComponent1 paths) ≡ 0ℚ
    path2Zero : pathSum (pathComponent2 paths) ≡ 0ℚ
    path3Zero : pathSum (pathComponent3 paths) ≡ 0ℚ

open FourPath3AverageZero public

fourPathNormSq : FourPath3 → ℚ
fourPathNormSq paths =
  pathNormSq (pathComponent0 paths)
  + (pathNormSq (pathComponent1 paths)
  + (pathNormSq (pathComponent2 paths)
  + pathNormSq (pathComponent3 paths)))

fourPathEnergy : FourPath3 → ℚ
fourPathEnergy paths =
  pathEdgeEnergy (pathComponent0 paths)
  + (pathEdgeEnergy (pathComponent1 paths)
  + (pathEdgeEnergy (pathComponent2 paths)
  + pathEdgeEnergy (pathComponent3 paths)))

fourPath3Poincare : ∀ paths →
  FourPath3AverageZero paths →
  fourPathNormSq paths ≤ fourPathEnergy paths
fourPath3Poincare paths zeroes =
  ℚP.+-mono-≤
    (path3Poincare (pathComponent0 paths) (path0Zero zeroes))
    (ℚP.+-mono-≤
      (path3Poincare (pathComponent1 paths) (path1Zero zeroes))
      (ℚP.+-mono-≤
        (path3Poincare (pathComponent2 paths) (path2Zero zeroes))
        (path3Poincare (pathComponent3 paths) (path3Zero zeroes))))

data AllFourPath3AverageZero : List FourPath3 → Set where
  []zero : AllFourPath3AverageZero []
  _∷zero_ : ∀ {paths rest} →
    FourPath3AverageZero paths →
    AllFourPath3AverageZero rest →
    AllFourPath3AverageZero (paths ∷ rest)

pathFamilyNormSq : List FourPath3 → ℚ
pathFamilyNormSq [] = 0ℚ
pathFamilyNormSq (paths ∷ rest) =
  fourPathNormSq paths + pathFamilyNormSq rest

pathFamilyEnergy : List FourPath3 → ℚ
pathFamilyEnergy [] = 0ℚ
pathFamilyEnergy (paths ∷ rest) =
  fourPathEnergy paths + pathFamilyEnergy rest

finiteDisjointPath3Poincare : ∀ family →
  AllFourPath3AverageZero family →
  pathFamilyNormSq family ≤ pathFamilyEnergy family
finiteDisjointPath3Poincare [] []zero = ℚP.≤-refl
finiteDisjointPath3Poincare
    (paths ∷ rest) (pathsZero ∷zero restZero) =
  ℚP.+-mono-≤
    (fourPath3Poincare paths pathsZero)
    (finiteDisjointPath3Poincare rest restZero)

path3SpectralIdentityLevel : ProofLevel
path3SpectralIdentityLevel = computed

path3PoincareLevel : ProofLevel
path3PoincareLevel = machineChecked

path3FourDimensionalTensorizationLevel : ProofLevel
path3FourDimensionalTensorizationLevel = conditional
