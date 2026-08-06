module DASHI.Physics.YangMills.BalabanP33SymmetricTwoByTwoInverseExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition.
-- DOI: 10.1017/CBO9781139020411.
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schroedinger
-- Operators".
-- DOI: 10.1007/BF01646473.
--
-- DASHI CONTRIBUTION
--
-- Construct and verify the inverse of a literal symmetric 2x2 rational matrix.
-- For H=[[a,b],[b,c]], determinant d=ac-b^2 and invD*d=1, the candidate
--
--             invD [[c,-b],[-b,a]]
--
-- is proved to be both a left and right inverse entry by entry.  This is the
-- smallest exact regression for the Gate-II plan
--
--   coercivity -> injectivity -> finite inverse -> Combes--Thomas.
--
-- The physical 3072-coordinate inverse still requires the actual Hessian
-- matrix and a constructive finite elimination or equivalent certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

record Matrix2 : Set where
  constructor matrix2
  field
    m00 m01 m10 m11 : ℚ

open Matrix2 public

multiplyMatrix2 : Matrix2 → Matrix2 → Matrix2
multiplyMatrix2 left right =
  matrix2
    (m00 left * m00 right + m01 left * m10 right)
    (m00 left * m01 right + m01 left * m11 right)
    (m10 left * m00 right + m11 left * m10 right)
    (m10 left * m01 right + m11 left * m11 right)

identityMatrix2 : Matrix2
identityMatrix2 = matrix2 1ℚ 0ℚ 0ℚ 1ℚ

symmetricMatrix : ℚ → ℚ → ℚ → Matrix2
symmetricMatrix a b c = matrix2 a b b c

determinantSymmetric : ℚ → ℚ → ℚ → ℚ
determinantSymmetric a b c = a * c - b * b

symmetricInverseCandidate : ℚ → ℚ → ℚ → ℚ → Matrix2
symmetricInverseCandidate a b c inverseDeterminant =
  matrix2
    (inverseDeterminant * c)
    (- (inverseDeterminant * b))
    (- (inverseDeterminant * b))
    (inverseDeterminant * a)

leftInverse00 :
  ∀ a b c inverseDeterminant →
  inverseDeterminant * determinantSymmetric a b c ≡ 1ℚ →
  m00
    (multiplyMatrix2
      (symmetricInverseCandidate a b c inverseDeterminant)
      (symmetricMatrix a b c))
  ≡ 1ℚ
leftInverse00 a b c inverseDeterminant inverseLaw
  rewrite inverseLaw = solve (a ∷ b ∷ c ∷ inverseDeterminant ∷ [])

leftInverse01 :
  ∀ a b c inverseDeterminant →
  m01
    (multiplyMatrix2
      (symmetricInverseCandidate a b c inverseDeterminant)
      (symmetricMatrix a b c))
  ≡ 0ℚ
leftInverse01 a b c inverseDeterminant =
  solve (a ∷ b ∷ c ∷ inverseDeterminant ∷ [])

leftInverse10 :
  ∀ a b c inverseDeterminant →
  m10
    (multiplyMatrix2
      (symmetricInverseCandidate a b c inverseDeterminant)
      (symmetricMatrix a b c))
  ≡ 0ℚ
leftInverse10 a b c inverseDeterminant =
  solve (a ∷ b ∷ c ∷ inverseDeterminant ∷ [])

leftInverse11 :
  ∀ a b c inverseDeterminant →
  inverseDeterminant * determinantSymmetric a b c ≡ 1ℚ →
  m11
    (multiplyMatrix2
      (symmetricInverseCandidate a b c inverseDeterminant)
      (symmetricMatrix a b c))
  ≡ 1ℚ
leftInverse11 a b c inverseDeterminant inverseLaw
  rewrite inverseLaw = solve (a ∷ b ∷ c ∷ inverseDeterminant ∷ [])

rightInverse00 :
  ∀ a b c inverseDeterminant →
  inverseDeterminant * determinantSymmetric a b c ≡ 1ℚ →
  m00
    (multiplyMatrix2
      (symmetricMatrix a b c)
      (symmetricInverseCandidate a b c inverseDeterminant))
  ≡ 1ℚ
rightInverse00 a b c inverseDeterminant inverseLaw
  rewrite inverseLaw = solve (a ∷ b ∷ c ∷ inverseDeterminant ∷ [])

rightInverse01 :
  ∀ a b c inverseDeterminant →
  m01
    (multiplyMatrix2
      (symmetricMatrix a b c)
      (symmetricInverseCandidate a b c inverseDeterminant))
  ≡ 0ℚ
rightInverse01 a b c inverseDeterminant =
  solve (a ∷ b ∷ c ∷ inverseDeterminant ∷ [])

rightInverse10 :
  ∀ a b c inverseDeterminant →
  m10
    (multiplyMatrix2
      (symmetricMatrix a b c)
      (symmetricInverseCandidate a b c inverseDeterminant))
  ≡ 0ℚ
rightInverse10 a b c inverseDeterminant =
  solve (a ∷ b ∷ c ∷ inverseDeterminant ∷ [])

rightInverse11 :
  ∀ a b c inverseDeterminant →
  inverseDeterminant * determinantSymmetric a b c ≡ 1ℚ →
  m11
    (multiplyMatrix2
      (symmetricMatrix a b c)
      (symmetricInverseCandidate a b c inverseDeterminant))
  ≡ 1ℚ
rightInverse11 a b c inverseDeterminant inverseLaw
  rewrite inverseLaw = solve (a ∷ b ∷ c ∷ inverseDeterminant ∷ [])
