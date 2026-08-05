module DASHI.Physics.Closure.NSTriadKNLuoFiniteWavevectorProjectiveLoopExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Torah Sanni.
-- Title: "A Topological Obstruction to Persistent Vorticity Alignment via
-- the Angular Strain Symbol".
-- protocols.io preprint/protocol, version 1, 2025.
-- DOI: 10.17504/protocols.io.j8nlk15m5g5r/v1.
--
-- PURPOSE
-- Provide a mathematically valid finite prototype of the claimed eigenline
-- monodromy, independently of the displayed-symbol audit.  Five rational
-- signed lifts trace a half-turn in R^2:
--
--   (1,0), (1,1), (0,1), (-1,1), (-1,0).
--
-- Their rank-one projectors form a closed projective loop: the first and last
-- projector are equal.  The chosen signed lift nevertheless ends at the
-- negative of its start.  The trace-free symbols S=2P-I have the selected
-- line as the +1 eigenspace at every sample.
--
-- This is an explicit RP^1/Möbius model.  It is not identified with the
-- genuine Navier--Stokes angular strain symbol; that identification is blocked
-- until a nontrivial corrected symbol is supplied and analysed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

record Vector2 : Set where
  constructor v2
  field x y : ℚ

open Vector2 public

vector2Ext :
  ∀ {a b : Vector2} →
  x a ≡ x b → y a ≡ y b → a ≡ b
vector2Ext {v2 ax ay} {v2 .ax .ay} refl refl = refl

negateVector : Vector2 → Vector2
negateVector (v2 vx vy) = v2 (- vx) (- vy)

record Matrix2 : Set where
  constructor matrix2
  field m11 m12 m21 m22 : ℚ

open Matrix2 public

apply : Matrix2 → Vector2 → Vector2
apply (matrix2 a11 a12 a21 a22) (v2 vx vy) =
  v2 (a11 * vx + a12 * vy) (a21 * vx + a22 * vy)

half two : ℚ
half = Int.+ 1 / 2
two = Int.+ 2 / 1

strainFromProjector : Matrix2 → Matrix2
strainFromProjector (matrix2 p11 p12 p21 p22) =
  matrix2
    (two * p11 + (- 1ℚ))
    (two * p12)
    (two * p21)
    (two * p22 + (- 1ℚ))

lift0 lift1 lift2 lift3 lift4 : Vector2
lift0 = v2 1ℚ 0ℚ
lift1 = v2 1ℚ 1ℚ
lift2 = v2 0ℚ 1ℚ
lift3 = v2 (- 1ℚ) 1ℚ
lift4 = v2 (- 1ℚ) 0ℚ

projector0 projector1 projector2 projector3 projector4 : Matrix2
projector0 = matrix2 1ℚ 0ℚ 0ℚ 0ℚ
projector1 = matrix2 half half half half
projector2 = matrix2 0ℚ 0ℚ 0ℚ 1ℚ
projector3 = matrix2 half (- half) (- half) half
projector4 = matrix2 1ℚ 0ℚ 0ℚ 0ℚ

projectiveLoopCloses : projector4 ≡ projector0
projectiveLoopCloses = refl

signedLiftFlips : lift4 ≡ negateVector lift0
signedLiftFlips = refl

symbol0 symbol1 symbol2 symbol3 symbol4 : Matrix2
symbol0 = strainFromProjector projector0
symbol1 = strainFromProjector projector1
symbol2 = strainFromProjector projector2
symbol3 = strainFromProjector projector3
symbol4 = strainFromProjector projector4

symbolLoopCloses : symbol4 ≡ symbol0
symbolLoopCloses = refl

lift0MaximalEigenvector : apply symbol0 lift0 ≡ lift0
lift0MaximalEigenvector =
  vector2Ext (solve []) (solve [])

lift1MaximalEigenvector : apply symbol1 lift1 ≡ lift1
lift1MaximalEigenvector =
  vector2Ext (solve []) (solve [])

lift2MaximalEigenvector : apply symbol2 lift2 ≡ lift2
lift2MaximalEigenvector =
  vector2Ext (solve []) (solve [])

lift3MaximalEigenvector : apply symbol3 lift3 ≡ lift3
lift3MaximalEigenvector =
  vector2Ext (solve []) (solve [])

lift4MaximalEigenvector : apply symbol4 lift4 ≡ lift4
lift4MaximalEigenvector =
  vector2Ext (solve []) (solve [])
