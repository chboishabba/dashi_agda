module DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using
  ( ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_
  ; NonNegative; Positive; nonNegative; pos )
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact local Poincare certificate on the literal 2 × 2 × 2 × 2 cell.
--
-- The carrier has all 16 vertices and all 32 unoriented nearest-neighbour
-- edges.  The proof is an exact Walsh sum-of-squares identity over ℚ:
--
--   8 E(f) + (Σ f)² = 16 ||f||² + R(f),    R(f) ≥ 0.
--
-- Hence Σ f = 0 implies 2 ||f||² ≤ E(f).  No floating-point eigenvalue,
-- spectral assumption, or axiom enters the certificate: the polynomial
-- identity below is discharged by the rational ring normalizer.
------------------------------------------------------------------------

twoℚ : ℚ
twoℚ = 1ℚ + 1ℚ

fourℚ : ℚ
fourℚ = 1ℚ + 1ℚ + 1ℚ + 1ℚ

eightℚ : ℚ
eightℚ = 1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ

sixteenℚ : ℚ
sixteenℚ = 1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ
  + 1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ + 1ℚ

sumQ : List ℚ → ℚ
sumQ [] = 0ℚ
sumQ (x ∷ xs) = x + sumQ xs

sq : ℚ → ℚ
sq x = x * x

sqDiff : ℚ → ℚ → ℚ
sqDiff x y = sq (x - y)

mapSquares : List ℚ → List ℚ
mapSquares [] = []
mapSquares (x ∷ xs) = sq x ∷ mapSquares xs

record Cube16 : Set where
  constructor cube16
  field
    x0000 x0001 x0010 x0011 : ℚ
    x0100 x0101 x0110 x0111 : ℚ
    x1000 x1001 x1010 x1011 : ℚ
    x1100 x1101 x1110 x1111 : ℚ

open Cube16 public

blockSum : Cube16 → ℚ
blockSum (cube16 x0000 x0001 x0010 x0011 x0100 x0101 x0110 x0111
                 x1000 x1001 x1010 x1011 x1100 x1101 x1110 x1111) =
  sumQ (x0000 ∷ x0001 ∷ x0010 ∷ x0011 ∷ x0100 ∷ x0101 ∷ x0110 ∷ x0111
      ∷ x1000 ∷ x1001 ∷ x1010 ∷ x1011 ∷ x1100 ∷ x1101 ∷ x1110 ∷ x1111 ∷ [])

normSq : Cube16 → ℚ
normSq (cube16 x0000 x0001 x0010 x0011 x0100 x0101 x0110 x0111
                x1000 x1001 x1010 x1011 x1100 x1101 x1110 x1111) =
  sumQ (sq x0000 ∷ sq x0001 ∷ sq x0010 ∷ sq x0011
      ∷ sq x0100 ∷ sq x0101 ∷ sq x0110 ∷ sq x0111
      ∷ sq x1000 ∷ sq x1001 ∷ sq x1010 ∷ sq x1011
      ∷ sq x1100 ∷ sq x1101 ∷ sq x1110 ∷ sq x1111 ∷ [])

edgeEnergy : Cube16 → ℚ
edgeEnergy (cube16 x0000 x0001 x0010 x0011 x0100 x0101 x0110 x0111
                    x1000 x1001 x1010 x1011 x1100 x1101 x1110 x1111) =
  sumQ
    (sqDiff x0000 x1000 ∷ sqDiff x0000 x0100 ∷ sqDiff x0000 x0010 ∷ sqDiff x0000 x0001
    ∷ sqDiff x0001 x1001 ∷ sqDiff x0001 x0101 ∷ sqDiff x0001 x0011
    ∷ sqDiff x0010 x1010 ∷ sqDiff x0010 x0110 ∷ sqDiff x0010 x0011
    ∷ sqDiff x0011 x1011 ∷ sqDiff x0011 x0111
    ∷ sqDiff x0100 x1100 ∷ sqDiff x0100 x0110 ∷ sqDiff x0100 x0101
    ∷ sqDiff x0101 x1101 ∷ sqDiff x0101 x0111
    ∷ sqDiff x0110 x1110 ∷ sqDiff x0110 x0111
    ∷ sqDiff x0111 x1111
    ∷ sqDiff x1000 x1100 ∷ sqDiff x1000 x1010 ∷ sqDiff x1000 x1001
    ∷ sqDiff x1001 x1101 ∷ sqDiff x1001 x1011
    ∷ sqDiff x1010 x1110 ∷ sqDiff x1010 x1011
    ∷ sqDiff x1011 x1111
    ∷ sqDiff x1100 x1110 ∷ sqDiff x1100 x1101
    ∷ sqDiff x1101 x1111 ∷ sqDiff x1110 x1111 ∷ [])

------------------------------------------------------------------------
-- The only Walsh modes needed by the positive remainder.  These are literal
-- characters of (C2)^4; duplicated terms below encode their eigenvalue
-- multiplicities in 8E + sum² - 16||f||².
------------------------------------------------------------------------

w0011 w0101 w0110 w0111 w1001 w1010 w1011 w1100 w1101 w1110 w1111 :
  Cube16 → ℚ
w0011 (cube16 a b c d e f g h i j k l m n o p) =
  sumQ (a ∷ (- b) ∷ (- c) ∷ d ∷ e ∷ (- f) ∷ (- g) ∷ h
      ∷ i ∷ (- j) ∷ (- k) ∷ l ∷ m ∷ (- n) ∷ (- o) ∷ p ∷ [])
w0101 (cube16 a b c d e f g h i j k l m n o p) =
  sumQ (a ∷ (- b) ∷ c ∷ (- d) ∷ (- e) ∷ f ∷ (- g) ∷ h
      ∷ i ∷ (- j) ∷ k ∷ (- l) ∷ (- m) ∷ n ∷ (- o) ∷ p ∷ [])
w0110 (cube16 a b c d e f g h i j k l m n o p) =
  sumQ (a ∷ b ∷ (- c) ∷ (- d) ∷ (- e) ∷ (- f) ∷ g ∷ h
      ∷ i ∷ j ∷ (- k) ∷ (- l) ∷ (- m) ∷ (- n) ∷ o ∷ p ∷ [])
w0111 (cube16 a b c d e f g h i j k l m n o p) =
  sumQ (a ∷ (- b) ∷ (- c) ∷ d ∷ (- e) ∷ f ∷ g ∷ (- h)
      ∷ i ∷ (- j) ∷ (- k) ∷ l ∷ (- m) ∷ n ∷ o ∷ (- p) ∷ [])
w1001 (cube16 a b c d e f g h i j k l m n o p) =
  sumQ (a ∷ (- b) ∷ c ∷ (- d) ∷ e ∷ (- f) ∷ g ∷ (- h)
      ∷ (- i) ∷ j ∷ (- k) ∷ l ∷ (- m) ∷ n ∷ (- o) ∷ p ∷ [])
w1010 (cube16 a b c d e f g h i j k l m n o p) =
  sumQ (a ∷ b ∷ (- c) ∷ (- d) ∷ e ∷ f ∷ (- g) ∷ (- h)
      ∷ (- i) ∷ (- j) ∷ k ∷ l ∷ (- m) ∷ (- n) ∷ o ∷ p ∷ [])
w1011 (cube16 a b c d e f g h i j k l m n o p) =
  sumQ (a ∷ (- b) ∷ (- c) ∷ d ∷ e ∷ (- f) ∷ (- g) ∷ h
      ∷ (- i) ∷ j ∷ k ∷ (- l) ∷ (- m) ∷ n ∷ o ∷ (- p) ∷ [])
w1100 (cube16 a b c d e f g h i j k l m n o p) =
  sumQ (a ∷ b ∷ c ∷ d ∷ (- e) ∷ (- f) ∷ (- g) ∷ (- h)
      ∷ (- i) ∷ (- j) ∷ (- k) ∷ (- l) ∷ m ∷ n ∷ o ∷ p ∷ [])
w1101 (cube16 a b c d e f g h i j k l m n o p) =
  sumQ (a ∷ (- b) ∷ c ∷ (- d) ∷ (- e) ∷ f ∷ (- g) ∷ h
      ∷ (- i) ∷ j ∷ (- k) ∷ l ∷ m ∷ (- n) ∷ o ∷ (- p) ∷ [])
w1110 (cube16 a b c d e f g h i j k l m n o p) =
  sumQ (a ∷ b ∷ (- c) ∷ (- d) ∷ (- e) ∷ (- f) ∷ g ∷ h
      ∷ (- i) ∷ (- j) ∷ k ∷ l ∷ m ∷ n ∷ (- o) ∷ (- p) ∷ [])
w1111 (cube16 a b c d e f g h i j k l m n o p) =
  sumQ (a ∷ (- b) ∷ (- c) ∷ d ∷ (- e) ∷ f ∷ g ∷ (- h)
      ∷ (- i) ∷ j ∷ k ∷ (- l) ∷ m ∷ (- n) ∷ (- o) ∷ p ∷ [])

walshRemainder : Cube16 → ℚ
walshRemainder f =
  sumQ
    (sq (w0011 f) ∷ sq (w0101 f) ∷ sq (w0110 f)
    ∷ sq (w0111 f) ∷ sq (w0111 f)
    ∷ sq (w1001 f) ∷ sq (w1010 f)
    ∷ sq (w1011 f) ∷ sq (w1011 f)
    ∷ sq (w1100 f)
    ∷ sq (w1101 f) ∷ sq (w1101 f)
    ∷ sq (w1110 f) ∷ sq (w1110 f)
    ∷ sq (w1111 f) ∷ sq (w1111 f) ∷ sq (w1111 f) ∷ [])

------------------------------------------------------------------------
-- Exact polynomial identity.  `solve-∀` unfolds the constructor-specialized
-- definitions above and normalizes the resulting polynomial over ℚ.
------------------------------------------------------------------------

walshSpectralIdentityRaw :
  ∀ x0000 x0001 x0010 x0011 x0100 x0101 x0110 x0111
    x1000 x1001 x1010 x1011 x1100 x1101 x1110 x1111 →
  eightℚ * edgeEnergy
    (cube16 x0000 x0001 x0010 x0011 x0100 x0101 x0110 x0111
            x1000 x1001 x1010 x1011 x1100 x1101 x1110 x1111)
    + sq (blockSum
      (cube16 x0000 x0001 x0010 x0011 x0100 x0101 x0110 x0111
              x1000 x1001 x1010 x1011 x1100 x1101 x1110 x1111))
  ≡ sixteenℚ * normSq
      (cube16 x0000 x0001 x0010 x0011 x0100 x0101 x0110 x0111
              x1000 x1001 x1010 x1011 x1100 x1101 x1110 x1111)
    + walshRemainder
      (cube16 x0000 x0001 x0010 x0011 x0100 x0101 x0110 x0111
              x1000 x1001 x1010 x1011 x1100 x1101 x1110 x1111)
walshSpectralIdentityRaw = ℚRing.solve-∀

walshSpectralIdentity : ∀ f →
  eightℚ * edgeEnergy f + sq (blockSum f)
  ≡ sixteenℚ * normSq f + walshRemainder f
walshSpectralIdentity
  (cube16 x0000 x0001 x0010 x0011 x0100 x0101 x0110 x0111
          x1000 x1001 x1010 x1011 x1100 x1101 x1110 x1111) =
  walshSpectralIdentityRaw
    x0000 x0001 x0010 x0011 x0100 x0101 x0110 x0111
    x1000 x1001 x1010 x1011 x1100 x1101 x1110 x1111

------------------------------------------------------------------------
-- Positivity of the explicit sum-of-squares remainder.
------------------------------------------------------------------------

negSquare : ∀ q → (- q) * (- q) ≡ q * q
negSquare = ℚRing.solve-∀

negZero : - 0ℚ ≡ 0ℚ
negZero = ℚRing.solve-∀

squareNonnegative : ∀ q → 0ℚ ≤ sq q
squareNonnegative q with ℚP.≤-total 0ℚ q
... | inj₁ zero≤q =
  let
    instance
      qNonnegative : NonNegative q
      qNonnegative = nonNegative zero≤q
      qqNonnegative : NonNegative (q * q)
      qqNonnegative = ℚP.nonNeg*nonNeg⇒nonNeg q q
  in ℚP.nonNegative⁻¹ (q * q)
... | inj₂ q≤zero =
  subst (λ value → 0ℚ ≤ value) (negSquare q)
    (let
      zero≤negqRaw = ℚP.neg-antimono-≤ q≤zero
      zero≤negq : 0ℚ ≤ - q
      zero≤negq = subst (λ value → value ≤ - q) negZero zero≤negqRaw
      instance
        negqNonnegative : NonNegative (- q)
        negqNonnegative = nonNegative zero≤negq
        negqSquaredNonnegative : NonNegative ((- q) * (- q))
        negqSquaredNonnegative = ℚP.nonNeg*nonNeg⇒nonNeg (- q) (- q)
     in ℚP.nonNegative⁻¹ ((- q) * (- q)))

sumOfSquaresNonnegative : ∀ xs → 0ℚ ≤ sumQ (mapSquares xs)
sumOfSquaresNonnegative [] = ℚP.≤-refl
sumOfSquaresNonnegative (x ∷ xs) =
  subst (λ value → value ≤ sq x + sumQ (mapSquares xs))
    (ℚP.+-identityˡ 0ℚ)
    (ℚP.+-mono-≤ (squareNonnegative x) (sumOfSquaresNonnegative xs))

remainderTerms : Cube16 → List ℚ
remainderTerms f =
  w0011 f ∷ w0101 f ∷ w0110 f ∷ w0111 f ∷ w0111 f
  ∷ w1001 f ∷ w1010 f ∷ w1011 f ∷ w1011 f
  ∷ w1100 f ∷ w1101 f ∷ w1101 f
  ∷ w1110 f ∷ w1110 f
  ∷ w1111 f ∷ w1111 f ∷ w1111 f ∷ []

walshRemainderAsSquares : ∀ f →
  walshRemainder f ≡ sumQ (mapSquares (remainderTerms f))
walshRemainderAsSquares f = refl

walshRemainderNonnegative : ∀ f → 0ℚ ≤ walshRemainder f
walshRemainderNonnegative f rewrite walshRemainderAsSquares f =
  sumOfSquaresNonnegative (remainderTerms f)

------------------------------------------------------------------------
-- Exact local spectral gap cblock = 2.
------------------------------------------------------------------------

baseBelowBasePlusRemainder : ∀ base remainder →
  0ℚ ≤ remainder → base ≤ base + remainder
baseBelowBasePlusRemainder base remainder zero≤remainder =
  subst (λ value → value ≤ base + remainder)
    (ℚP.+-identityʳ base)
    (ℚP.+-mono-≤ (ℚP.≤-refl {x = base}) zero≤remainder)

zeroSquare : sq 0ℚ ≡ 0ℚ
zeroSquare = ℚRing.solve-∀

meanZeroWalshIdentity : ∀ f →
  blockSum f ≡ 0ℚ →
  eightℚ * edgeEnergy f
  ≡ sixteenℚ * normSq f + walshRemainder f
meanZeroWalshIdentity f meanZero =
  trans
    (sym (ℚP.+-identityʳ (eightℚ * edgeEnergy f)))
    (trans
      (cong (λ value → eightℚ * edgeEnergy f + value) (sym zeroSquare))
      (trans
        (cong (λ value → eightℚ * edgeEnergy f + sq value) (sym meanZero))
        (walshSpectralIdentity f)))

meanZeroScaledGap : ∀ f →
  blockSum f ≡ 0ℚ →
  sixteenℚ * normSq f ≤ eightℚ * edgeEnergy f
meanZeroScaledGap f meanZero =
  subst (λ right → sixteenℚ * normSq f ≤ right)
    (sym (meanZeroWalshIdentity f meanZero))
    (baseBelowBasePlusRemainder
      (sixteenℚ * normSq f) (walshRemainder f)
      (walshRemainderNonnegative f))

eightTimesTwo : ∀ q → eightℚ * (twoℚ * q) ≡ sixteenℚ * q
eightTimesTwo = ℚRing.solve-∀

instance
  onePositive : Positive 1ℚ
  onePositive = pos
  twoPositive : Positive twoℚ
  twoPositive = ℚP.pos+pos⇒pos 1ℚ 1ℚ
  fourPositive : Positive fourℚ
  fourPositive = ℚP.pos+pos⇒pos twoℚ twoℚ
  eightPositive : Positive eightℚ
  eightPositive = ℚP.pos+pos⇒pos fourℚ fourℚ

boolean4BlockPoincare : ∀ f →
  blockSum f ≡ 0ℚ →
  twoℚ * normSq f ≤ edgeEnergy f
boolean4BlockPoincare f meanZero =
  ℚP.*-cancelˡ-≤-pos eightℚ
    (subst (λ left → left ≤ eightℚ * edgeEnergy f)
      (sym (eightTimesTwo (normSq f)))
      (meanZeroScaledGap f meanZero))

------------------------------------------------------------------------
-- Four bond components and finite disjoint block tilings.
------------------------------------------------------------------------

record BondBlock4 : Set where
  constructor bondBlock
  field component0 component1 component2 component3 : Cube16

open BondBlock4 public

record BondBlockAverageZero (block : BondBlock4) : Set where
  constructor averagesZero
  field
    component0Zero : blockSum (component0 block) ≡ 0ℚ
    component1Zero : blockSum (component1 block) ≡ 0ℚ
    component2Zero : blockSum (component2 block) ≡ 0ℚ
    component3Zero : blockSum (component3 block) ≡ 0ℚ

open BondBlockAverageZero public

bondNormSq : BondBlock4 → ℚ
bondNormSq block =
  normSq (component0 block)
  + (normSq (component1 block)
  + (normSq (component2 block) + normSq (component3 block)))

bondEdgeEnergy : BondBlock4 → ℚ
bondEdgeEnergy block =
  edgeEnergy (component0 block)
  + (edgeEnergy (component1 block)
  + (edgeEnergy (component2 block) + edgeEnergy (component3 block)))

twoDistributesFour : ∀ a b c d →
  twoℚ * (a + (b + (c + d)))
  ≡ twoℚ * a + (twoℚ * b + (twoℚ * c + twoℚ * d))
twoDistributesFour = ℚRing.solve-∀

fourComponentBoolean4BlockPoincare :
  ∀ block → BondBlockAverageZero block →
  twoℚ * bondNormSq block ≤ bondEdgeEnergy block
fourComponentBoolean4BlockPoincare block zeroes =
  subst (λ left → left ≤ bondEdgeEnergy block)
    (sym (twoDistributesFour
      (normSq (component0 block)) (normSq (component1 block))
      (normSq (component2 block)) (normSq (component3 block))))
    (ℚP.+-mono-≤
      (boolean4BlockPoincare (component0 block) (component0Zero zeroes))
      (ℚP.+-mono-≤
        (boolean4BlockPoincare (component1 block) (component1Zero zeroes))
        (ℚP.+-mono-≤
          (boolean4BlockPoincare (component2 block) (component2Zero zeroes))
          (boolean4BlockPoincare (component3 block) (component3Zero zeroes)))))

data AllBlockAverageZero : List BondBlock4 → Set where
  []zero : AllBlockAverageZero []
  _∷zero_ : ∀ {block : BondBlock4} {blocks : List BondBlock4} →
    BondBlockAverageZero block → AllBlockAverageZero blocks →
    AllBlockAverageZero (block ∷ blocks)

familyNormSq : List BondBlock4 → ℚ
familyNormSq [] = 0ℚ
familyNormSq (block ∷ blocks) = bondNormSq block + familyNormSq blocks

familyEdgeEnergy : List BondBlock4 → ℚ
familyEdgeEnergy [] = 0ℚ
familyEdgeEnergy (block ∷ blocks) = bondEdgeEnergy block + familyEdgeEnergy blocks

twoDistributesPlus : ∀ a b →
  twoℚ * (a + b) ≡ twoℚ * a + twoℚ * b
twoDistributesPlus = ℚRing.solve-∀

finiteDisjointBoolean4BlockPoincare :
  ∀ blocks → AllBlockAverageZero blocks →
  twoℚ * familyNormSq blocks ≤ familyEdgeEnergy blocks
finiteDisjointBoolean4BlockPoincare [] []zero = ℚP.≤-refl
finiteDisjointBoolean4BlockPoincare
  (block ∷ blocks) (blockZero ∷zero blocksZero) =
  subst (λ left → left ≤ bondEdgeEnergy block + familyEdgeEnergy blocks)
    (sym (twoDistributesPlus (bondNormSq block) (familyNormSq blocks)))
    (ℚP.+-mono-≤
      (fourComponentBoolean4BlockPoincare block blockZero)
      (finiteDisjointBoolean4BlockPoincare blocks blocksZero))

boolean4CellPoincareDefinitionLevel : ProofLevel
boolean4CellPoincareDefinitionLevel = machineChecked

boolean4CellPoincareExactIdentityLevel : ProofLevel
boolean4CellPoincareExactIdentityLevel = computed

boolean4CellPoincareOrderCertificateLevel : ProofLevel
boolean4CellPoincareOrderCertificateLevel = machineChecked

arbitraryPhysicalRGBlockPoincareLevel : ProofLevel
arbitraryPhysicalRGBlockPoincareLevel = conditional
