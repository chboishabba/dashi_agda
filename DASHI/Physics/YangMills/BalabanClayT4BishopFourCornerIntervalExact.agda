module DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Errett Bishop and Douglas Bridges,
-- "Constructive Analysis", Springer, 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant", B.Sc. Honours thesis,
-- Dalhousie University, 2022. arXiv:2205.08354. No DOI assigned.
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721.
--
-- DASHI CONTRIBUTION
--
-- Round55 proved the exact rational four-corner multiplication interval, but
-- physical beta atoms are Bishop reals.  The difficult constructive case is
-- when BOTH intervals straddle zero: one may not split on the unknown sign of
-- a Bishop real.
--
-- We avoid real trichotomy completely.  Every Bishop point in a rational
-- interval has a constructive convex coordinate t in [0,1].  Rational endpoint
-- comparison is decidable; a nondegenerate rational width is a positive Bishop
-- real and hence invertible.  Bilinearity then writes xy as a nested convex
-- combination of ac,ad,bc,bd.  Therefore the EXISTING rational min4/max4 box
-- encloses the actual Bishop product exactly, including straddle/straddle.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Integer.Base using (+_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _≤_; _<_; toℚᵘ)
import Data.Rational.Properties as ℚP
open import Data.Sum.Base using (inj₂)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Real as Bishop
import RealProperties as BishopP
import Inverse as BishopInverse

import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Carrier
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
open import DASHI.Physics.YangMills.CompactLieProofLevel

embed : ℚ → Bishop.ℝ
embed = Carrier.bishopRationalEmbed

embedOrder : ∀ {left right} → left ≤ right → embed left Bishop.≤ embed right
embedOrder = Carrier.bishopEmbedOrder

embedStrictOrder : ∀ {left right} → left < right → embed left Bishop.< embed right
embedStrictOrder {left} {right} strict =
  BishopP.p<q⇒p⋆<q⋆
    (toℚᵘ left) (toℚᵘ right)
    (ℚP.toℚᵘ-mono-< strict)

embedNeg : ∀ value → embed (- value) Bishop.≃ (Bishop.- embed value)
embedNeg value =
  BishopP.≃-trans
    (BishopP.⋆-cong (ℚP.toℚᵘ-homo‿- value))
    (BishopP.⋆-distrib-neg (toℚᵘ value))

embedMul : ∀ left right →
  embed (left * right) Bishop.≃ (embed left Bishop.* embed right)
embedMul left right =
  BishopP.≃-trans
    (BishopP.⋆-cong (ℚP.toℚᵘ-homo-* left right))
    (BishopP.⋆-distrib-* (toℚᵘ left) (toℚᵘ right))

embedZero : embed 0ℚ Bishop.≃ Bishop.0ℝ
embedZero = BishopP.≃-refl

embedOne : embed 1ℚ Bishop.≃ Bishop.1ℝ
embedOne = BishopP.≃-refl

------------------------------------------------------------------------
-- Bishop semantic interval membership.
------------------------------------------------------------------------

record BishopLiesIn (value : Bishop.ℝ) (box : Eval.RationalInterval) : Set where
  constructor bishopLiesIn
  field
    lowerSound : embed (Eval.lower box) Bishop.≤ value
    upperSound : value Bishop.≤ embed (Eval.upper box)
open BishopLiesIn public

------------------------------------------------------------------------
-- Constructive convex coordinates.
------------------------------------------------------------------------

convex : Bishop.ℝ → Bishop.ℝ → Bishop.ℝ → Bishop.ℝ
convex parameter left right =
  ((Bishop.1ℝ Bishop.- parameter) Bishop.* left)
  Bishop.+ (parameter Bishop.* right)

record ConvexCoordinate
    (value : Bishop.ℝ) (box : Eval.RationalInterval) : Set where
  constructor convexCoordinate
  field
    parameter : Bishop.ℝ
    parameterNonnegative : Bishop.0ℝ Bishop.≤ parameter
    parameterBelowOne : parameter Bishop.≤ Bishop.1ℝ
    interpolation : value Bishop.≃
      convex parameter (embed (Eval.lower box)) (embed (Eval.upper box))
open ConvexCoordinate public

zeroBelowOne : Bishop.0ℝ Bishop.≤ Bishop.1ℝ
zeroBelowOne =
  BishopP.≤-respˡ-≃ embedZero
    (BishopP.≤-respʳ-≃ embedOne
      (embedOrder (ℚP.nonNegative⁻¹ 1ℚ)))

oneMinusNonnegative : ∀ {parameter} →
  parameter Bishop.≤ Bishop.1ℝ →
  Bishop.0ℝ Bishop.≤ (Bishop.1ℝ Bishop.- parameter)
oneMinusNonnegative {parameter} parameterBelowOne =
  BishopP.≤-respˡ-≃
    (BishopP.+-inverseʳ Bishop.1ℝ)
    (BishopP.+-monoˡ-≤ Bishop.1ℝ
      (BishopP.neg-mono-≤ parameterBelowOne))

positiveEmbeddedWidth : ∀ {lower upper} → lower < upper →
  Bishop.0ℝ Bishop.< (embed upper Bishop.- embed lower)
positiveEmbeddedWidth {lower} {upper} lowerStrict =
  let
    shifted = BishopP.+-mono-<-≤
      (embedStrictOrder lowerStrict)
      (BishopP.≤-refl {x = Bishop.- embed lower})
  in
  BishopP.<-respˡ-≃
    (BishopP.+-inverseʳ (embed lower))
    shifted

positiveWidthNonzero : ∀ {lower upper} (lowerStrict : lower < upper) →
  (embed upper Bishop.- embed lower) Bishop.≄ Bishop.0ℝ
positiveWidthNonzero lowerStrict = inj₂ (positiveEmbeddedWidth lowerStrict)

strictConvexCoordinate :
  ∀ {value box} →
  BishopLiesIn value box →
  Eval.lower box < Eval.upper box →
  ConvexCoordinate value box
strictConvexCoordinate {value} {box} inside lowerStrict =
  let
    a = embed (Eval.lower box)
    b = embed (Eval.upper box)
    width = b Bishop.- a
    widthNonzero = positiveWidthNonzero lowerStrict
    inverseWidth = BishopInverse._⁻¹ width widthNonzero
    inverseWidthNonnegative =
      BishopP.pos⇒nonNeg
        (BishopInverse.posx⇒posx⁻¹
          widthNonzero (BishopP.0<x⇒posx (positiveEmbeddedWidth lowerStrict)))
    delta = value Bishop.- a
    t = delta Bishop.* inverseWidth

    deltaNonnegative : Bishop.0ℝ Bishop.≤ delta
    deltaNonnegative =
      BishopP.≤-respˡ-≃
        (BishopP.+-inverseʳ a)
        (BishopP.+-mono-≤
          (lowerSound inside)
          (BishopP.≤-refl {x = Bishop.- a}))

    deltaBelowWidth : delta Bishop.≤ width
    deltaBelowWidth =
      BishopP.+-mono-≤
        (upperSound inside)
        (BishopP.≤-refl {x = Bishop.- a})

    tNonnegative : Bishop.0ℝ Bishop.≤ t
    tNonnegative =
      BishopP.nonNegx⇒0≤x
        (BishopP.nonNegx,y⇒nonNegx*y
          (BishopP.0≤x⇒nonNegx deltaNonnegative)
          inverseWidthNonnegative)

    tBelowOne : t Bishop.≤ Bishop.1ℝ
    tBelowOne =
      BishopP.≤-respʳ-≃
        (BishopInverse.*-inverseʳ width widthNonzero)
        (BishopP.*-monoʳ-≤-nonNeg
          deltaBelowWidth inverseWidthNonnegative)

    tTimesWidth : (t Bishop.* width) Bishop.≃ delta
    tTimesWidth =
      BishopP.≃-trans
        (BishopP.*-assoc delta inverseWidth width)
        (BishopP.≃-trans
          (BishopP.*-congˡ
            (BishopInverse.*-inverseˡ width widthNonzero))
          (BishopP.*-identityʳ delta))

    convexToAPlusTWidth :
      convex t a b Bishop.≃ (a Bishop.+ (t Bishop.* width))
    convexToAPlusTWidth =
      let open BishopP.ℝ-Solver
      in solve 3
        (λ t₀ a₀ b₀ →
          ((Κ (+ 1 / 1) ⊖ t₀) ⊗ a₀) ⊕ (t₀ ⊗ b₀)
          ⊜ a₀ ⊕ (t₀ ⊗ (b₀ ⊖ a₀)))
        BishopP.≃-refl t a b

    aPlusDeltaIsValue : (a Bishop.+ delta) Bishop.≃ value
    aPlusDeltaIsValue =
      let open BishopP.ℝ-Solver
      in solve 2
        (λ a₀ x₀ → a₀ ⊕ (x₀ ⊖ a₀) ⊜ x₀)
        BishopP.≃-refl a value

    convexIsValue : convex t a b Bishop.≃ value
    convexIsValue =
      BishopP.≃-trans convexToAPlusTWidth
        (BishopP.≃-trans
          (BishopP.+-congʳ a tTimesWidth)
          aPlusDeltaIsValue)
  in
  convexCoordinate
    t tNonnegative tBelowOne (BishopP.≃-symm convexIsValue)

degenerateConvexCoordinate :
  ∀ {value box} →
  BishopLiesIn value box →
  Eval.lower box ≡ Eval.upper box →
  ConvexCoordinate value box
degenerateConvexCoordinate {value} {box} inside endpointsEqual =
  let
    a = embed (Eval.lower box)
    valueBelowA : value Bishop.≤ a
    valueBelowA =
      subst
        (λ endpoint → value Bishop.≤ embed endpoint)
        (sym endpointsEqual)
        (upperSound inside)
    valueIsA : value Bishop.≃ a
    valueIsA = BishopP.≤-antisym valueBelowA (lowerSound inside)
    zeroConvexIsA : convex Bishop.0ℝ a a Bishop.≃ a
    zeroConvexIsA =
      let open BishopP.ℝ-Solver
      in solve 1
        (λ a₀ →
          ((Κ (+ 1 / 1) ⊖ Κ (+ 0 / 1)) ⊗ a₀)
            ⊕ (Κ (+ 0 / 1) ⊗ a₀)
          ⊜ a₀)
        BishopP.≃-refl a
  in
  convexCoordinate
    Bishop.0ℝ
    BishopP.≤-refl
    zeroBelowOne
    (BishopP.≃-trans valueIsA (BishopP.≃-symm zeroConvexIsA))

constructConvexCoordinate :
  ∀ {value box} → BishopLiesIn value box → ConvexCoordinate value box
constructConvexCoordinate {value} {box} inside
    with ℚP.<-cmp (Eval.lower box) (Eval.upper box)
... | tri< lowerStrict _ _ = strictConvexCoordinate inside lowerStrict
... | tri≈ _ endpointsEqual _ = degenerateConvexCoordinate inside endpointsEqual
... | tri> _ _ upperStrict =
  ⊥-elim
    (ℚP.<-irrefl refl
      (ℚP.<-≤-trans upperStrict (Eval.ordered box)))

------------------------------------------------------------------------
-- Convex combinations preserve common lower/upper bounds.
------------------------------------------------------------------------

convexLower : ∀ parameter left right bound →
  Bishop.0ℝ Bishop.≤ parameter → parameter Bishop.≤ Bishop.1ℝ →
  bound Bishop.≤ left → bound Bishop.≤ right →
  bound Bishop.≤ convex parameter left right
convexLower parameter left right bound parameterNN parameter≤1 bound≤left bound≤right =
  let
    leftWeightNN = oneMinusNonnegative parameter≤1
    leftScaled =
      BishopP.*-monoˡ-≤-nonNeg bound≤left
        (BishopP.0≤x⇒nonNegx leftWeightNN)
    rightScaled =
      BishopP.*-monoˡ-≤-nonNeg bound≤right
        (BishopP.0≤x⇒nonNegx parameterNN)
    summed = BishopP.+-mono-≤ leftScaled rightScaled
    duplicateBound :
      ((Bishop.1ℝ Bishop.- parameter) Bishop.* bound)
        Bishop.+ (parameter Bishop.* bound)
      Bishop.≃ bound
    duplicateBound =
      let open BishopP.ℝ-Solver
      in solve 2
        (λ t b →
          ((Κ (+ 1 / 1) ⊖ t) ⊗ b) ⊕ (t ⊗ b) ⊜ b)
        BishopP.≃-refl parameter bound
  in
  BishopP.≤-respˡ-≃ duplicateBound summed

convexUpper : ∀ parameter left right bound →
  Bishop.0ℝ Bishop.≤ parameter → parameter Bishop.≤ Bishop.1ℝ →
  left Bishop.≤ bound → right Bishop.≤ bound →
  convex parameter left right Bishop.≤ bound
convexUpper parameter left right bound parameterNN parameter≤1 left≤bound right≤bound =
  let
    leftWeightNN = oneMinusNonnegative parameter≤1
    leftScaled =
      BishopP.*-monoˡ-≤-nonNeg left≤bound
        (BishopP.0≤x⇒nonNegx leftWeightNN)
    rightScaled =
      BishopP.*-monoˡ-≤-nonNeg right≤bound
        (BishopP.0≤x⇒nonNegx parameterNN)
    summed = BishopP.+-mono-≤ leftScaled rightScaled
    duplicateBound :
      ((Bishop.1ℝ Bishop.- parameter) Bishop.* bound)
        Bishop.+ (parameter Bishop.* bound)
      Bishop.≃ bound
    duplicateBound =
      let open BishopP.ℝ-Solver
      in solve 2
        (λ t b →
          ((Κ (+ 1 / 1) ⊖ t) ⊗ b) ⊕ (t ⊗ b) ⊜ b)
        BishopP.≃-refl parameter bound
  in
  BishopP.≤-respʳ-≃ duplicateBound summed

------------------------------------------------------------------------
-- Exact four-corner product enclosure in the Bishop carrier.
------------------------------------------------------------------------

cornerLower : ∀ p q r s →
  let minimum = Typed.min4 (p * r) (p * s) (q * r) (q * s)
  in
  ( embed minimum Bishop.≤ (embed p Bishop.* embed r))
  × ( embed minimum Bishop.≤ (embed p Bishop.* embed s))
  × ( embed minimum Bishop.≤ (embed q Bishop.* embed r))
  × ( embed minimum Bishop.≤ (embed q Bishop.* embed s))
cornerLower p q r s =
  let
    ll = p * r; lu = p * s; ul = q * r; uu = q * s
    minimum = Typed.min4 ll lu ul uu
  in
  BishopP.≤-respʳ-≃ (embedMul p r)
    (embedOrder (Typed.min4BelowFirst ll lu ul uu))
  , BishopP.≤-respʳ-≃ (embedMul p s)
    (embedOrder (Typed.min4BelowSecond ll lu ul uu))
  , BishopP.≤-respʳ-≃ (embedMul q r)
    (embedOrder (Typed.min4BelowThird ll lu ul uu))
  , BishopP.≤-respʳ-≃ (embedMul q s)
    (embedOrder (Typed.min4BelowFourth ll lu ul uu))

cornerUpper : ∀ p q r s →
  let maximum = Typed.max4 (p * r) (p * s) (q * r) (q * s)
  in
  ( (embed p Bishop.* embed r) Bishop.≤ embed maximum)
  × ( (embed p Bishop.* embed s) Bishop.≤ embed maximum)
  × ( (embed q Bishop.* embed r) Bishop.≤ embed maximum)
  × ( (embed q Bishop.* embed s) Bishop.≤ embed maximum)
cornerUpper p q r s =
  let
    ll = p * r; lu = p * s; ul = q * r; uu = q * s
    maximum = Typed.max4 ll lu ul uu
  in
  BishopP.≤-respˡ-≃ (embedMul p r)
    (embedOrder (Typed.firstBelowMax4 ll lu ul uu))
  , BishopP.≤-respˡ-≃ (embedMul p s)
    (embedOrder (Typed.secondBelowMax4 ll lu ul uu))
  , BishopP.≤-respˡ-≃ (embedMul q r)
    (embedOrder (Typed.thirdBelowMax4 ll lu ul uu))
  , BishopP.≤-respˡ-≃ (embedMul q s)
    (embedOrder (Typed.fourthBelowMax4 ll lu ul uu))

multiplyIntervalBishopSound :
  ∀ {x y left right} →
  BishopLiesIn x left → BishopLiesIn y right →
  BishopLiesIn (x Bishop.* y) (Typed.multiplyInterval left right)
multiplyIntervalBishopSound {x} {y} {left} {right} xIn yIn =
  let
    xCoordinate = constructConvexCoordinate xIn
    yCoordinate = constructConvexCoordinate yIn
    tx = parameter xCoordinate
    ty = parameter yCoordinate
    a = embed (Eval.lower left)
    b = embed (Eval.upper left)
    c = embed (Eval.lower right)
    d = embed (Eval.upper right)
    ll = Eval.lower left * Eval.lower right
    lu = Eval.lower left * Eval.upper right
    ul = Eval.upper left * Eval.lower right
    uu = Eval.upper left * Eval.upper right
    minimum = Typed.min4 ll lu ul uu
    maximum = Typed.max4 ll lu ul uu
    lowerCorners = cornerLower
      (Eval.lower left) (Eval.upper left)
      (Eval.lower right) (Eval.upper right)
    upperCorners = cornerUpper
      (Eval.lower left) (Eval.upper left)
      (Eval.lower right) (Eval.upper right)

    aYIsConvex : (a Bishop.* y) Bishop.≃
      convex ty (a Bishop.* c) (a Bishop.* d)
    aYIsConvex =
      BishopP.≃-trans
        (BishopP.*-congˡ (interpolation yCoordinate))
        (let open BishopP.ℝ-Solver
         in solve 4
           (λ t a₀ c₀ d₀ →
             a₀ ⊗ (((Κ (+ 1 / 1) ⊖ t) ⊗ c₀) ⊕ (t ⊗ d₀))
             ⊜ ((Κ (+ 1 / 1) ⊖ t) ⊗ (a₀ ⊗ c₀))
               ⊕ (t ⊗ (a₀ ⊗ d₀)))
           BishopP.≃-refl ty a c d)

    bYIsConvex : (b Bishop.* y) Bishop.≃
      convex ty (b Bishop.* c) (b Bishop.* d)
    bYIsConvex =
      BishopP.≃-trans
        (BishopP.*-congˡ (interpolation yCoordinate))
        (let open BishopP.ℝ-Solver
         in solve 4
           (λ t b₀ c₀ d₀ →
             b₀ ⊗ (((Κ (+ 1 / 1) ⊖ t) ⊗ c₀) ⊕ (t ⊗ d₀))
             ⊜ ((Κ (+ 1 / 1) ⊖ t) ⊗ (b₀ ⊗ c₀))
               ⊕ (t ⊗ (b₀ ⊗ d₀)))
           BishopP.≃-refl ty b c d)

    lowerA : embed minimum Bishop.≤ (a Bishop.* y)
    lowerA =
      BishopP.≤-respʳ-≃ (BishopP.≃-symm aYIsConvex)
        (convexLower ty (a Bishop.* c) (a Bishop.* d) (embed minimum)
          (parameterNonnegative yCoordinate)
          (parameterBelowOne yCoordinate)
          (proj₁ lowerCorners)
          (proj₁ (proj₂ lowerCorners)))

    lowerB : embed minimum Bishop.≤ (b Bishop.* y)
    lowerB =
      BishopP.≤-respʳ-≃ (BishopP.≃-symm bYIsConvex)
        (convexLower ty (b Bishop.* c) (b Bishop.* d) (embed minimum)
          (parameterNonnegative yCoordinate)
          (parameterBelowOne yCoordinate)
          (proj₁ (proj₂ (proj₂ lowerCorners)))
          (proj₂ (proj₂ (proj₂ lowerCorners))))

    productIsConvex : (x Bishop.* y) Bishop.≃
      convex tx (a Bishop.* y) (b Bishop.* y)
    productIsConvex =
      BishopP.≃-trans
        (BishopP.*-congʳ (interpolation xCoordinate))
        (let open BishopP.ℝ-Solver
         in solve 4
           (λ t a₀ b₀ y₀ →
             ((((Κ (+ 1 / 1) ⊖ t) ⊗ a₀) ⊕ (t ⊗ b₀)) ⊗ y₀)
             ⊜ ((Κ (+ 1 / 1) ⊖ t) ⊗ (a₀ ⊗ y₀))
               ⊕ (t ⊗ (b₀ ⊗ y₀)))
           BishopP.≃-refl tx a b y)

    lowerProduct : embed minimum Bishop.≤ (x Bishop.* y)
    lowerProduct =
      BishopP.≤-respʳ-≃ (BishopP.≃-symm productIsConvex)
        (convexLower tx (a Bishop.* y) (b Bishop.* y) (embed minimum)
          (parameterNonnegative xCoordinate)
          (parameterBelowOne xCoordinate)
          lowerA lowerB)

    upperA : (a Bishop.* y) Bishop.≤ embed maximum
    upperA =
      BishopP.≤-respˡ-≃ (BishopP.≃-symm aYIsConvex)
        (convexUpper ty (a Bishop.* c) (a Bishop.* d) (embed maximum)
          (parameterNonnegative yCoordinate)
          (parameterBelowOne yCoordinate)
          (proj₁ upperCorners)
          (proj₁ (proj₂ upperCorners)))

    upperB : (b Bishop.* y) Bishop.≤ embed maximum
    upperB =
      BishopP.≤-respˡ-≃ (BishopP.≃-symm bYIsConvex)
        (convexUpper ty (b Bishop.* c) (b Bishop.* d) (embed maximum)
          (parameterNonnegative yCoordinate)
          (parameterBelowOne yCoordinate)
          (proj₁ (proj₂ (proj₂ upperCorners)))
          (proj₂ (proj₂ (proj₂ upperCorners))))

    upperProduct : (x Bishop.* y) Bishop.≤ embed maximum
    upperProduct =
      BishopP.≤-respˡ-≃ productIsConvex
        (convexUpper tx (a Bishop.* y) (b Bishop.* y) (embed maximum)
          (parameterNonnegative xCoordinate)
          (parameterBelowOne xCoordinate)
          upperA upperB)
  in
  bishopLiesIn lowerProduct upperProduct

bishopRationalIntervalConvexCoordinateLevel : ProofLevel
bishopRationalIntervalConvexCoordinateLevel = machineChecked

bishopFourCornerMultiplyWithoutTrichotomyLevel : ProofLevel
bishopFourCornerMultiplyWithoutTrichotomyLevel = machineChecked
