module DASHI.Analysis.BlockSchurCoercivity where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

------------------------------------------------------------------------
-- Domain-neutral quantitative Schur-complement theorem.
--
-- For
--
--   S = D - C A⁻¹ B,
--
-- the only analytic content needed for a lower bound is:
--
--   D >= δ,
--   C A⁻¹ B <= η,
--   η <= δ.
--
-- The scalar/order socket below deliberately does not assume ℝ.  Concrete
-- NS/YM lanes may instantiate it with exact rationals, intervals, reals, or
-- another ordered scalar carrier.
------------------------------------------------------------------------

record SchurOrderLaws {s : Level} (Scalar : Set s) : Set (lsuc s) where
  field
    _≤_ : Scalar → Scalar → Set s
    _⊖_ : Scalar → Scalar → Scalar

    subtractLowerBound :
      ∀ {δ d correction η} →
      δ ≤ d →
      correction ≤ η →
      η ≤ δ →
      (δ ⊖ η) ≤ (d ⊖ correction)

open SchurOrderLaws public

record QuantitativeBlockSchur
    {v s : Level}
    (Vector : Set v)
    (Scalar : Set s)
    (O : SchurOrderLaws Scalar) : Set (lsuc (v ⊔ s)) where
  field
    dBlock : Vector → Vector
    crossCorrection : Vector → Vector
    schurComplement : Vector → Vector

    inner : Vector → Vector → Scalar

    highGap : Scalar
    crossBudget : Scalar

    schurQuadraticIdentity :
      ∀ x →
      inner x (schurComplement x) ≡
      _⊖_ O
        (inner x (dBlock x))
        (inner x (crossCorrection x))

    highBlockCoercive :
      ∀ x → _≤_ O highGap (inner x (dBlock x))

    crossCorrectionBounded :
      ∀ x → _≤_ O (inner x (crossCorrection x)) crossBudget

    crossBelowHighGap :
      _≤_ O crossBudget highGap

open QuantitativeBlockSchur public

schurCoercive :
  ∀ {v s}
    {Vector : Set v}
    {Scalar : Set s}
    (O : SchurOrderLaws Scalar)
    (Q : QuantitativeBlockSchur Vector Scalar O)
    (x : Vector) →
  _≤_ O
    (_⊖_ O (highGap Q) (crossBudget Q))
    (inner Q x (schurComplement Q x))
schurCoercive O Q x =
  subst
    (λ value →
      _≤_ O
        (_⊖_ O (highGap Q) (crossBudget Q))
        value)
    (sym (schurQuadraticIdentity Q x))
    (subtractLowerBound O
      (highBlockCoercive Q x)
      (crossCorrectionBounded Q x)
      (crossBelowHighGap Q))

record StrictSchurGap
    {v s : Level}
    {Vector : Set v}
    {Scalar : Set s}
    (O : SchurOrderLaws Scalar)
    (Q : QuantitativeBlockSchur Vector Scalar O) : Set (v ⊔ s) where
  field
    StrictlyPositive : Scalar → Set s
    residualGapPositive :
      StrictlyPositive (_⊖_ O (highGap Q) (crossBudget Q))

open StrictSchurGap public

record QuantitativeSchurCertificate
    {v s : Level}
    {Vector : Set v}
    {Scalar : Set s}
    (O : SchurOrderLaws Scalar)
    (Q : QuantitativeBlockSchur Vector Scalar O) : Set (lsuc (v ⊔ s)) where
  field
    strictGap : StrictSchurGap O Q
    lowerBound :
      ∀ x →
      _≤_ O
        (_⊖_ O (highGap Q) (crossBudget Q))
        (inner Q x (schurComplement Q x))

open QuantitativeSchurCertificate public

certifyQuantitativeSchur :
  ∀ {v s}
    {Vector : Set v}
    {Scalar : Set s}
    (O : SchurOrderLaws Scalar)
    (Q : QuantitativeBlockSchur Vector Scalar O) →
  StrictSchurGap O Q →
  QuantitativeSchurCertificate O Q
certifyQuantitativeSchur O Q gap = record
  { strictGap = gap
  ; lowerBound = schurCoercive O Q
  }
