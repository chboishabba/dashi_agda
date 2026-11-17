module DASHI.Physics.YangMills.YMClayBishopSU2WilsonDeficitPositiveExact where

------------------------------------------------------------------------
-- ACTUAL Bishop SU2 quaternion Wilson trace deficit >= 0.
-- Source-first: unit q => ||q-(1,0,0,0)||² = 2(1-q0).
-- Four squared Bishop reals are nonnegative on the original real
-- carrier. This proves 1-q0 >= 0 constructively with no numerical
-- trace bound and NO preassumed Wilson-action positivity.
--
-- Consequence: any finite nonnegative-beta sum of these deficits is
-- a nonnegative Bishop real. Feed to the SAME Bishop exponential
-- source YMClayBishopWilsonGibbsPositiveExact for a positive Gibbs
-- density at each finite quaternion-plaquette configuration.
--
-- Remaining original physical weld: actual 4D plaquette holonomies,
-- certified quaternion-vs-original SUN group, finite product Haar,
-- periodic cylinder law; those are not constructed here.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)

import Real as B
import RealProperties as P
import DASHI.Foundations.BishopSquareNonnegativeExact as Square
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Physics.YangMills.YMClayBishopSU2QuaternionTraceWeldExact as Q
import DASHI.Physics.YangMills.YMClayBishopSU2DeterminantExact as D
import DASHI.Physics.YangMills.YMClayBishopWilsonGibbsPositiveExact as Gibbs

square : B.ℝ → B.ℝ
square x = B._*_ x x

chordSquare : Q.BishopQuaternion → B.ℝ
chordSquare q =
  B._+_
    (square (B._-_ (Q.q0 q) B.1ℝ))
    (B._+_
      (square (Q.q1 q))
      (B._+_
        (square (Q.q2 q))
        (square (Q.q3 q))))

wilsonTraceDeficit : Q.BishopQuaternion → B.ℝ
wilsonTraceDeficit q = B._-_ B.1ℝ (Q.q0 q)

chordSquareNonnegative :
  ∀ q → B.NonNegative (chordSquare q)
chordSquareNonnegative q =
  P.nonNegx,y⇒nonNegx+y
    (Square.bishopSquareNonnegative
      (B._-_ (Q.q0 q) B.1ℝ))
    (P.nonNegx,y⇒nonNegx+y
      (Square.bishopSquareNonnegative (Q.q1 q))
      (P.nonNegx,y⇒nonNegx+y
        (Square.bishopSquareNonnegative (Q.q2 q))
        (Square.bishopSquareNonnegative (Q.q3 q))))

half : B.ℝ
half = B._⋆ (+ 1 / 2)

halfNonnegative : B.NonNegative half
halfNonnegative =
  P.pos⇒nonNeg (P.0<x⇒posx Exp.halfPositive)

-- Exact polynomial identity before using any unit-norm information.
chordHalfPolynomialIdentity :
  ∀ q →
  B._≃_
    (B._*_ half (chordSquare q))
    (B._+_
      (wilsonTraceDeficit q)
      (B._*_ half (B._-_ (D.normSq q) B.1ℝ)))
chordHalfPolynomialIdentity q =
  let open P.ℝ-Solver in
  solve 4
    (λ a b c d →
      (Κ (+ 1 / 2) ⊗
        (((a ⊖ Κ 1ℚᵘ) ⊗ (a ⊖ Κ 1ℚᵘ))
         ⊕ ((b ⊗ b) ⊕ ((c ⊗ c) ⊕ (d ⊗ d)))))
      ⊜
      ((Κ 1ℚᵘ ⊖ a)
       ⊕ (Κ (+ 1 / 2) ⊗
           (((a ⊗ a)
             ⊕ ((b ⊗ b) ⊕ ((c ⊗ c) ⊕ (d ⊗ d))))
            ⊖ Κ 1ℚᵘ))))
    P.≃-refl
    (Q.q0 q) (Q.q1 q) (Q.q2 q) (Q.q3 q)

unitQuaternionHalfChordIsDeficit :
  ∀ u →
  B._≃_
    (B._*_ half (chordSquare (D.quaternion u)))
    (wilsonTraceDeficit (D.quaternion u))
unitQuaternionHalfChordIsDeficit u =
  P.≃-trans
    (chordHalfPolynomialIdentity (D.quaternion u))
    (P.≃-trans
      (P.+-congʳ
        (P.*-congʳ
          (P.-cong (D.unitNorm u) P.≃-refl)))
      (let open P.ℝ-Solver in
       solve 1
         (λ a →
           ((Κ 1ℚᵘ ⊖ a)
            ⊕ (Κ (+ 1 / 2) ⊗ (Κ 1ℚᵘ ⊖ Κ 1ℚᵘ)))
           ⊜ (Κ 1ℚᵘ ⊖ a))
         P.≃-refl (Q.q0 (D.quaternion u))))

unitQuaternionWilsonDeficitNonnegative :
  ∀ u → B.NonNegative
    (wilsonTraceDeficit (D.quaternion u))
unitQuaternionWilsonDeficitNonnegative u =
  P.0≤x⇒nonNegx
    (P.≤-respʳ-≃
      (unitQuaternionHalfChordIsDeficit u)
      (P.nonNegx⇒0≤x
        (P.nonNegx,y⇒nonNegx*y
          halfNonnegative
          (chordSquareNonnegative (D.quaternion u)))))

finiteSU2ActionDeficits :
  List D.UnitQuaternion → B.ℝ
finiteSU2ActionDeficits [] = B.0ℝ
finiteSU2ActionDeficits (u ∷ us) =
  B._+_
    (wilsonTraceDeficit (D.quaternion u))
    (finiteSU2ActionDeficits us)

finiteSU2ActionDeficitsNonnegative :
  ∀ plaquettes → B.NonNegative (finiteSU2ActionDeficits plaquettes)
finiteSU2ActionDeficitsNonnegative [] =
  P.0≤x⇒nonNegx (P.≤-refl B.0ℝ)
finiteSU2ActionDeficitsNonnegative (u ∷ us) =
  P.nonNegx,y⇒nonNegx+y
    (unitQuaternionWilsonDeficitNonnegative u)
    (finiteSU2ActionDeficitsNonnegative us)

finiteSU2WilsonAction :
  B.ℝ → List D.UnitQuaternion → B.ℝ
finiteSU2WilsonAction beta plaquettes =
  B._*_ beta (finiteSU2ActionDeficits plaquettes)

finiteSU2WilsonActionNonnegative :
  ∀ beta →
  B.NonNegative beta →
  ∀ plaquettes →
  B.NonNegative (finiteSU2WilsonAction beta plaquettes)
finiteSU2WilsonActionNonnegative beta betaNN plaquettes =
  P.nonNegx,y⇒nonNegx*y
    betaNN
    (finiteSU2ActionDeficitsNonnegative plaquettes)

finiteSU2WilsonGibbsWeightPositive :
  ∀ beta →
  (betaNN : B.NonNegative beta) →
  ∀ plaquettes →
  B._<_ B.0ℝ
    (Exp.bishopExp (B.- (finiteSU2WilsonAction beta plaquettes)))
finiteSU2WilsonGibbsWeightPositive beta betaNN plaquettes =
  Gibbs.bishopWilsonExpNegativeStrictPositive
    (finiteSU2WilsonActionNonnegative beta betaNN plaquettes)
