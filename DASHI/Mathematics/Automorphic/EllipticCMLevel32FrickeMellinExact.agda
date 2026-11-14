module DASHI.Mathematics.Automorphic.EllipticCMLevel32FrickeMellinExact where

------------------------------------------------------------------------
-- ORIGINAL E:y²=x³-x, f_32(z)=eta(4z)² eta(8z)².
--
-- At t>0, Dedekind eta inversion yields
--   eta(i/(8t))² = (8t) eta(8it)²
--   eta(i/(4t))² = (4t) eta(4it)²,
-- hence the EXACT level-32 Fricke identity
--   f_32(i/(32t)) = 32 t² f_32(it).
--
-- The theorem below pays the square-root-FREE RATIONAL ALGEBRA
-- on the original eta 4/8 scale factors. The actual analytic
-- eta-inversion equalities are explicit premises, NOT invented
-- Bishop eta theorems or abstract status receipts.
--
-- At the central point s=1, the original MellinSplitData compiler
-- also implies LOWER PIECE = UPPER PIECE when epsilon=+1 and
-- the reflection fixes 1. This is the exact finite algebra
-- behind the reduced POSITIVE TAIL integral:
--   L(E,1) = 4*pi * integral_{1/sqrt(32)}^infinity f_32(it) dt.
--
-- The actual Bishop Mellin integral and its strict positivity
-- are outstanding analytic source producers; no new abstract
-- "integral" defined here is misrepresented as the genuine one.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Automorphic.MellinSplitFunctionalEquationExact as Mellin
import DASHI.Mathematics.Arithmetic.EllipticCurveSmallPrimeFrobeniusExact as Rows
import DASHI.Mathematics.Automorphic.EllipticCMLevel32EtaNewmanArithmeticExact as Newman

square : ℚ → ℚ
square x = x * x

etaScaleFourRational : ℚ
etaScaleFourRational = Rows.natToRational Newman.etaScaleFour

etaScaleEightRational : ℚ
etaScaleEightRational = Rows.natToRational Newman.etaScaleEight

frickeScaleRational : ℚ
frickeScaleRational = Rows.natToRational Newman.level

-- This is the literal original level-32 factor product
-- after squaring both eta factors.
level32EtaSquaredProduct : ℚ → ℚ → ℚ
level32EtaSquaredProduct eta4 eta8 =
  square eta4 * square eta8

-- The actual eta transformations must be proved on the
-- Bishop/complex upper-half-plane carrier independently.
-- Given those two exact source identities, NO sqrt identities
-- are required for the level-32 Fricke step.
level32FrickeFromTwoEtaInversions :
  (t eta4 eta8 eta4Inverted eta8Inverted : ℚ) →
  square eta4Inverted
    ≡ (etaScaleEightRational * t) * square eta8 →
  square eta8Inverted
    ≡ (etaScaleFourRational * t) * square eta4 →
  level32EtaSquaredProduct eta4Inverted eta8Inverted
    ≡ (frickeScaleRational * square t)
       * level32EtaSquaredProduct eta4 eta8
level32FrickeFromTwoEtaInversions
    t eta4 eta8 eta4Inverted eta8Inverted h4 h8
    rewrite h4 | h8 =
  solve (t ∷ eta4 ∷ eta8 ∷ [])

-- Reuse the existing original Mellin split proof, NOT a
-- new "Mellin" wrapper with unconnected carriers.
mellinCentralLowerEqualsUpper :
  (data : Mellin.MellinSplitData) →
  (central : Mellin.Parameter data) →
  Mellin.epsilon data ≡ 1ℚ →
  Mellin.reflectParameter data central ≡ central →
  Mellin.lowerPiece data central
    ≡ Mellin.upperPiece data central
mellinCentralLowerEqualsUpper data central eps fixed
  rewrite eps | fixed =
  trans
    (Mellin.lowerSubstitution data central)
    (solve (Mellin.upperPiece data central ∷ []))

mellinCentralValueIsTwiceTail :
  (data : Mellin.MellinSplitData) →
  (central : Mellin.Parameter data) →
  Mellin.epsilon data ≡ 1ℚ →
  Mellin.reflectParameter data central ≡ central →
  Mellin.completedTransform data central
    ≡ (1ℚ + 1ℚ) * Mellin.upperPiece data central
mellinCentralValueIsTwiceTail data central eps fixed =
  trans
    (congLower
      (mellinCentralLowerEqualsUpper data central eps fixed))
    (solve (Mellin.upperPiece data central ∷ []))
  where
    congLower :
      Mellin.lowerPiece data central
        ≡ Mellin.upperPiece data central →
      Mellin.completedTransform data central
        ≡ Mellin.upperPiece data central
          + Mellin.upperPiece data central
    congLower refl = refl
