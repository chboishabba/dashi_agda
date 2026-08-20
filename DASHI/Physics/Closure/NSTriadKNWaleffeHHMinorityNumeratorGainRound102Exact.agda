module DASHI.Physics.Closure.NSTriadKNWaleffeHHMinorityNumeratorGainRound102Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND102 / DIVISION-FREE HH->LOW HELICAL GEOMETRY GAIN
--
-- Waleffe's geometric factor can be written (up to a unit phase/sign) as
--
--   g = Q (s_k k + s_p p + s_q q) / (4 k p q),
--
-- where
--
--   Q^2 = 2(k^2p^2+p^2q^2+q^2k^2)-k^4-p^4-q^4
--       = 16 Area(k,p,q)^2.
--
-- Round102's minority-leg normal form multiplies this by the majority-radius
-- difference.  The useful estimates can be proved BEFORE division.
--
-- Low-output minority k (assume q is the larger high leg):
--
--   Q <= 2 k p,
--   d = q-p <= k,
--   s = p+q-k <= 2q
--
-- imply
--
--   Q d s <= (2kp)(2kq) = 4 k^2 p q.
--
-- After division by the positive Waleffe denominator 2pq this is the O(k^2)
-- critical coefficient.
--
-- High-input minority p with low output k:
--
--   Q <= 2 k q,
--   d = q-k <= q,
--   s = k+q-p <= 2k
--
-- imply
--
--   Q d s <= (2kq)^2 = 4 k^2 q^2.
--
-- After division by 2kq this is the O(k q) coefficient: one full low/high
-- ratio better than the naive O(q^2) high-high cost.  The q-minority case is
-- cyclic.  This file proves the ordered multiplicative step exactly; the
-- Euclidean triangle/cross-product builder supplying these geometric premises
-- is standard geometry and remains a separate source-native bridge.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore as Order

one two : ℚ
one = Data.Rational.Base.1ℚ
two = one + one

twoNonnegative : 0ℚ ≤ two
twoNonnegative = toWitness {a? = 0ℚ ≤? two} _

productNonnegative :
  ∀ {a b : ℚ} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a * b
productNonnegative {a} {b} aNN bNN =
  let
    instance
      aNonnegative = ℚ.nonNegative aNN
      bNonnegative = ℚ.nonNegative bNN
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg a b
  in
  ℚP.nonNegative⁻¹ (a * b)

twiceProductNonnegative :
  ∀ {a b : ℚ} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ two * a * b
twiceProductNonnegative aNN bNN =
  productNonnegative
    (productNonnegative twoNonnegative aNN)
    bNN

threeFactorMonotone :
  ∀ {a b c A B C : ℚ} →
  0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ c →
  0ℚ ≤ A → 0ℚ ≤ B → 0ℚ ≤ C →
  a ≤ A → b ≤ B → c ≤ C →
  a * (b * c) ≤ A * (B * C)
threeFactorMonotone aNN bNN cNN ANN BNN CNN a≤A b≤B c≤C =
  let
    bcNN = productNonnegative bNN cNN
    BCNN = productNonnegative BNN CNN
    bc≤BC = Order.nonnegativeProductMonotone bNN cNN BNN CNN b≤B c≤C
  in
  Order.nonnegativeProductMonotone aNN bcNN ANN BCNN a≤A bc≤BC

record LowMinorityHHGeometry : Set where
  constructor low-minority-hh-geometry
  field
    k p q Q difference defect : ℚ
    kNN pNN qNN QNN differenceNN defectNN :
      0ℚ ≤ k × 0ℚ ≤ p × 0ℚ ≤ q × 0ℚ ≤ Q ×
      0ℚ ≤ difference × 0ℚ ≤ defect
    differenceMeaning : difference ≡ q + (- p)
    defectMeaning : defect ≡ p + q + (- k)
    areaBound : Q ≤ two * k * p
    reverseTriangleDifference : difference ≤ k
    triangleDefectUpper : defect ≤ two * q

open LowMinorityHHGeometry public

lowMinorityWaleffeNumeratorBound :
  (G : LowMinorityHHGeometry) →
  Q G * (difference G * defect G)
  ≤ (two * k G * p G) * (two * k G * q G)
lowMinorityWaleffeNumeratorBound G =
  threeFactorMonotone
    (proj₁ (proj₂ (proj₂ (proj₂ (kNN G)))))
    (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (kNN G))))))
    (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (kNN G))))))
    (twiceProductNonnegative
      (proj₁ (kNN G))
      (proj₁ (proj₂ (kNN G))))
    (proj₁ (kNN G))
    (twiceProductNonnegative
      (proj₁ (kNN G))
      (proj₁ (proj₂ (proj₂ (kNN G)))))
    (areaBound G)
    (reverseTriangleDifference G)
    (triangleDefectUpper G)

record HighPMinorityHHGeometry : Set where
  constructor high-p-minority-hh-geometry
  field
    k p q Q difference defect : ℚ
    kNonnegative pNonnegative qNonnegative QNonnegative : ℚ
    kNN' : 0ℚ ≤ k
    pNN' : 0ℚ ≤ p
    qNN' : 0ℚ ≤ q
    QNN' : 0ℚ ≤ Q
    differenceNN' : 0ℚ ≤ difference
    defectNN' : 0ℚ ≤ defect
    differenceMeaning' : difference ≡ q + (- k)
    defectMeaning' : defect ≡ k + q + (- p)
    areaBound' : Q ≤ two * k * q
    differenceUpper' : difference ≤ q
    triangleDefectUpper' : defect ≤ two * k

open HighPMinorityHHGeometry public

highPMinorityWaleffeNumeratorBound :
  (G : HighPMinorityHHGeometry) →
  Q G * (difference G * defect G)
  ≤ (two * k G * q G) * (q G * (two * k G))
highPMinorityWaleffeNumeratorBound G =
  threeFactorMonotone
    (QNN' G)
    (differenceNN' G)
    (defectNN' G)
    (twiceProductNonnegative (kNN' G) (qNN' G))
    (qNN' G)
    (productNonnegative twoNonnegative (kNN' G))
    (areaBound' G)
    (differenceUpper' G)
    (triangleDefectUpper' G)

round102LowMinorityHHWaleffeNumeratorGainClosed : Bool
round102LowMinorityHHWaleffeNumeratorGainClosed = true

round102HighMinorityHHWaleffeNumeratorGainClosed : Bool
round102HighMinorityHHWaleffeNumeratorGainClosed = true

round102LowMinorityHHWaleffeNumeratorGainClosedIsTrue :
  round102LowMinorityHHWaleffeNumeratorGainClosed ≡ true
round102LowMinorityHHWaleffeNumeratorGainClosedIsTrue = refl

round102HighMinorityHHWaleffeNumeratorGainClosedIsTrue :
  round102HighMinorityHHWaleffeNumeratorGainClosed ≡ true
round102HighMinorityHHWaleffeNumeratorGainClosedIsTrue = refl
