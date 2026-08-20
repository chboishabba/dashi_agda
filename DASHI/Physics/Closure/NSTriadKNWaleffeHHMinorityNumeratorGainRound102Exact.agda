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
-- Waleffe's geometric factor can be written, up to a unit phase/sign, as
--
--   g = Q (s_k k + s_p p + s_q q) / (4 k p q),
--
-- with Q=4*Area(k,p,q).  Round102's minority-leg normal form multiplies this
-- by a majority-radius difference.  The useful scale bounds can be proved
-- before division.
--
-- Low-output minority k (q the larger high leg):
--
--   Q <= 2 k p,   d=q-p <= k,   s=p+q-k <= 2q
--
-- gives
--
--   Q d s <= (2kp) (k * 2q) = 4 k^2 p q.
--
-- After the positive Waleffe denominator this is O(k^2).
--
-- High-input minority p with low output k:
--
--   Q <= 2 k q,   d=q-k <= q,   s=k+q-p <= 2k
--
-- gives
--
--   Q d s <= (2kq) (q * 2k) = 4 k^2 q^2.
--
-- After the positive Waleffe denominator this is O(k q): one full low/high
-- ratio better than a naive O(q^2) high-high coefficient.  The q-minority
-- case is cyclic.
--
-- This module proves exactly the ordered multiplicative step.  The ordinary
-- Euclidean triangle/cross-product facts supplying these premises are kept as
-- a separate source-native geometric bridge rather than hidden in the scalar
-- estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore as Order

one two : ℚ
one = 1ℚ
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
    kL pL qL QL dL sL : ℚ
    kLNN : 0ℚ ≤ kL
    pLNN : 0ℚ ≤ pL
    qLNN : 0ℚ ≤ qL
    QLNN : 0ℚ ≤ QL
    dLNN : 0ℚ ≤ dL
    sLNN : 0ℚ ≤ sL
    dLMeaning : dL ≡ qL + (- pL)
    sLMeaning : sL ≡ pL + qL + (- kL)
    areaLUpper : QL ≤ two * kL * pL
    differenceLUpper : dL ≤ kL
    defectLUpper : sL ≤ two * qL

open LowMinorityHHGeometry public

lowMinorityWaleffeNumeratorBound :
  (G : LowMinorityHHGeometry) →
  QL G * (dL G * sL G)
  ≤ (two * kL G * pL G) * (kL G * (two * qL G))
lowMinorityWaleffeNumeratorBound G =
  threeFactorMonotone
    (QLNN G)
    (dLNN G)
    (sLNN G)
    (twiceProductNonnegative (kLNN G) (pLNN G))
    (kLNN G)
    (productNonnegative twoNonnegative (qLNN G))
    (areaLUpper G)
    (differenceLUpper G)
    (defectLUpper G)

record HighPMinorityHHGeometry : Set where
  constructor high-p-minority-hh-geometry
  field
    kP pP qP QP dP sP : ℚ
    kPNN : 0ℚ ≤ kP
    pPNN : 0ℚ ≤ pP
    qPNN : 0ℚ ≤ qP
    QPNN : 0ℚ ≤ QP
    dPNN : 0ℚ ≤ dP
    sPNN : 0ℚ ≤ sP
    dPMeaning : dP ≡ qP + (- kP)
    sPMeaning : sP ≡ kP + qP + (- pP)
    areaPUpper : QP ≤ two * kP * qP
    differencePUpper : dP ≤ qP
    defectPUpper : sP ≤ two * kP

open HighPMinorityHHGeometry public

highPMinorityWaleffeNumeratorBound :
  (G : HighPMinorityHHGeometry) →
  QP G * (dP G * sP G)
  ≤ (two * kP G * qP G) * (qP G * (two * kP G))
highPMinorityWaleffeNumeratorBound G =
  threeFactorMonotone
    (QPNN G)
    (dPNN G)
    (sPNN G)
    (twiceProductNonnegative (kPNN G) (qPNN G))
    (qPNN G)
    (productNonnegative twoNonnegative (kPNN G))
    (areaPUpper G)
    (differencePUpper G)
    (defectPUpper G)

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
