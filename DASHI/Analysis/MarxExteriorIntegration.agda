module DASHI.Analysis.MarxExteriorIntegration where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Set; Set₁)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxHigherCalculus

------------------------------------------------------------------------
-- Elementary list and degree operations.

_+N_ : Nat → Nat → Nat
zero +N n = n
suc m +N n = suc (m +N n)

_++L_ :
  {X : Set} →
  List X → List X → List X
[] ++L right = right
(x ∷ left) ++L right = x ∷ (left ++L right)

plugVector :
  {A : MarxAlgebra} →
  {V : Module A} →
  List (Vector V) →
  Vector V →
  List (Vector V) →
  List (Vector V)
plugVector prefix value suffix = prefix ++L (value ∷ suffix)

plugAdjacent :
  {A : MarxAlgebra} →
  {V : Module A} →
  List (Vector V) →
  Vector V →
  Vector V →
  List (Vector V) →
  List (Vector V)
plugAdjacent prefix left right suffix =
  prefix ++L (left ∷ right ∷ suffix)

------------------------------------------------------------------------
-- Alternating multilinear forms and a genuine graded differential complex.

record AlternatingMultilinearMap
  (A : MarxAlgebra)
  (V : Module A)
  (degree : Nat)
  : Set₁ where
  field
    evaluate : List (Vector V) → Carrier A
    acceptedArity : List (Vector V) → Set

    multilinearAdd :
      ∀ prefix suffix u v →
      acceptedArity (plugVector prefix (_+V_ V u v) suffix) →
      evaluate (plugVector prefix (_+V_ V u v) suffix)
      ≡ _+_ A
          (evaluate (plugVector prefix u suffix))
          (evaluate (plugVector prefix v suffix))

    multilinearScale :
      ∀ prefix suffix scalar v →
      acceptedArity (plugVector prefix (_•_ V scalar v) suffix) →
      evaluate (plugVector prefix (_•_ V scalar v) suffix)
      ≡ _*_ A scalar
          (evaluate (plugVector prefix v suffix))

    alternatingAdjacent :
      ∀ prefix suffix v →
      acceptedArity (plugAdjacent prefix v v suffix) →
      evaluate (plugAdjacent prefix v v suffix) ≡ zero A

open AlternatingMultilinearMap public

record GradedDifferentialForms
  (A : MarxAlgebra)
  (V : Module A)
  : Set₁ where
  field
    Form : Nat → Set
    zeroForm : ∀ degree → Form degree
    asAlternatingMap :
      ∀ {degree} →
      Form degree →
      AlternatingMultilinearMap A V degree

open GradedDifferentialForms public

record ExteriorAlgebra
  {A : MarxAlgebra}
  {V : Module A}
  (G : GradedDifferentialForms A V)
  : Set₁ where
  field
    wedge :
      ∀ {p q} →
      Form G p → Form G q → Form G (p +N q)

    wedgeZeroLeft :
      ∀ {p q} (omega : Form G q) →
      wedge (zeroForm G p) omega ≡ zeroForm G (p +N q)

    wedgeZeroRight :
      ∀ {p q} (omega : Form G p) →
      wedge omega (zeroForm G q) ≡ zeroForm G (p +N q)

record ExteriorDerivative
  {A : MarxAlgebra}
  {V : Module A}
  (G : GradedDifferentialForms A V)
  : Set₁ where
  field
    d : ∀ {degree} → Form G degree → Form G (suc degree)

    exteriorDerivativeSquaredZero :
      ∀ {degree} (omega : Form G degree) →
      d (d omega) ≡ zeroForm G (suc (suc degree))

open ExteriorDerivative public

zeroExteriorDerivative :
  {A : MarxAlgebra} →
  {V : Module A} →
  (G : GradedDifferentialForms A V) →
  ExteriorDerivative G
zeroExteriorDerivative G =
  record
    { d = λ {degree} _ → zeroForm G (suc degree)
    ; exteriorDerivativeSquaredZero = λ _ → refl
    }

------------------------------------------------------------------------
-- Literal finite Riemann sums.

record Interval
  (A : MarxAlgebra)
  : Set where
  constructor interval
  field
    leftEndpoint : Carrier A
    rightEndpoint : Carrier A

open Interval public

intervalLength :
  {A : MarxAlgebra} →
  Interval A → Carrier A
intervalLength {A} I = _-_ A (rightEndpoint I) (leftEndpoint I)

record RiemannCell
  (A : MarxAlgebra)
  : Set where
  constructor riemannCell
  field
    cellInterval : Interval A
    tag : Carrier A

open RiemannCell public

cellTerm :
  {A : MarxAlgebra} →
  Function A → RiemannCell A → Carrier A
cellTerm {A} f cell =
  _*_ A
    (f (tag cell))
    (intervalLength (cellInterval cell))

sumCarrierList :
  {A : MarxAlgebra} →
  List (Carrier A) → Carrier A
sumCarrierList {A} [] = zero A
sumCarrierList {A} (x ∷ xs) = _+_ A x (sumCarrierList xs)

record TaggedPartition
  (A : MarxAlgebra)
  : Set₁ where
  constructor taggedPartition
  field
    support : Interval A
    cells : List (RiemannCell A)
    orderedReceipt : Set
    contiguousReceipt : Set
    tagsInsideCellsReceipt : Set
    coversSupportReceipt : Set

open TaggedPartition public

riemannSum :
  {A : MarxAlgebra} →
  Function A → TaggedPartition A → Carrier A
riemannSum {A} f partition =
  sumCarrierList (mapCells (cells partition))
  where
    mapCells : List (RiemannCell A) → List (Carrier A)
    mapCells [] = []
    mapCells (cell ∷ rest) = cellTerm f cell ∷ mapCells rest

------------------------------------------------------------------------
-- Constructive Riemann integration laws.

record RiemannIntegralStructure
  (A : MarxAlgebra)
  : Set₁ where
  field
    _≤I_ : Carrier A → Carrier A → Set
    IntegrableOn : Interval A → Function A → Set
    integral : Interval A → Function A → Carrier A

    integralConstant :
      ∀ I c →
      integral I (constantFunction c)
      ≡ _*_ A c (intervalLength I)

    integralAdd :
      ∀ I f g →
      IntegrableOn I f →
      IntegrableOn I g →
      integral I (addFunctions f g)
      ≡ _+_ A (integral I f) (integral I g)

    integralScale :
      ∀ I scalar f →
      IntegrableOn I f →
      integral I (λ x → _*_ A scalar (f x))
      ≡ _*_ A scalar (integral I f)

    integralOrder :
      ∀ I f g →
      IntegrableOn I f →
      IntegrableOn I g →
      (∀ x → _≤I_ (f x) (g x)) →
      _≤I_ (integral I f) (integral I g)

    intervalAdditivity :
      ∀ a b c f →
      IntegrableOn (interval a b) f →
      IntegrableOn (interval b c) f →
      IntegrableOn (interval a c) f →
      integral (interval a c) f
      ≡ _+_ A
          (integral (interval a b) f)
          (integral (interval b c) f)

open RiemannIntegralStructure public

------------------------------------------------------------------------
-- Fundamental theorem cutset.

record FundamentalTheoremBridge
  {A : MarxAlgebra}
  (I : RiemannIntegralStructure A)
  : Set₁ where
  field
    accumulated :
      Interval A → Function A → Function A

    derivativeOfIntegral :
      ∀ intervalData f →
      IntegrableOn I intervalData f →
      MarxFactorisation A (accumulated intervalData f)

    integralOfDerivative :
      ∀ intervalData f →
      (F : MarxFactorisation A f) →
      IntegrableOn I intervalData (marxDerivative F) →
      integral I intervalData (marxDerivative F)
      ≡ _-_ A
          (f (rightEndpoint intervalData))
          (f (leftEndpoint intervalData))

open FundamentalTheoremBridge public

------------------------------------------------------------------------
-- Cumulative harm integration surface.

record CumulativeHarmIntegral
  {A : MarxAlgebra}
  (I : RiemannIntegralStructure A)
  : Set₁ where
  field
    observationWindow : Interval A
    harmRate : Function A
    harmRateIntegrable : IntegrableOn I observationWindow harmRate
    cumulativeHarm : Carrier A
    cumulativeHarmIsIntegral :
      cumulativeHarm ≡ integral I observationWindow harmRate
