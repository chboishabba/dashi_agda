module DASHI.Physics.Closure.NSWall1CanonicalFiniteSchur where

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+≤+)
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; *≤*)

open import DASHI.Analysis.FiniteWeightedKernelSums

------------------------------------------------------------------------
-- Exact 3 x 3 canonical transfer matrices.
--
-- The nonzero K01 entries are the L1-majorants of the three normalized
-- linearized triad vectors:
--
--   (1,-1,0), (-1,0,1), (0,1,-1),
--
-- hence every nonzero entry is exactly 2.  K10 is the transpose.
------------------------------------------------------------------------

data LowMode : Set where
  low100 low010 low001 : LowMode

data HighMode : Set where
  high110 high101 high011 : HighMode

lowModes : List LowMode
lowModes = low100 ∷ low010 ∷ low001 ∷ []

highModes : List HighMode
highModes = high110 ∷ high101 ∷ high011 ∷ []

two four : ℚ
two = 1ℚ + 1ℚ
four = two + two

oneWeightLow : LowMode → ℚ
oneWeightLow _ = 1ℚ

oneWeightHigh : HighMode → ℚ
oneWeightHigh _ = 1ℚ

canonicalK01 : HighMode → LowMode → ℚ
canonicalK01 high110 low010 = two
canonicalK01 high101 low001 = two
canonicalK01 high011 low001 = two
canonicalK01 _ _ = 0ℚ

canonicalK10 : LowMode → HighMode → ℚ
canonicalK10 low high = canonicalK01 high low

canonicalK01Finite : FiniteWeightedKernel HighMode LowMode ℚ
canonicalK01Finite = record
  { rows = highModes
  ; columns = lowModes
  ; zero = 0ℚ
  ; add = _+_
  ; multiply = _*_
  ; _≤_ = _≤_
  ; kernel = canonicalK01
  ; rowWeight = oneWeightHigh
  ; colWeight = oneWeightLow
  }

canonicalK10Finite : FiniteWeightedKernel LowMode HighMode ℚ
canonicalK10Finite = record
  { rows = lowModes
  ; columns = highModes
  ; zero = 0ℚ
  ; add = _+_
  ; multiply = _*_
  ; _≤_ = _≤_
  ; kernel = canonicalK10
  ; rowWeight = oneWeightLow
  ; colWeight = oneWeightHigh
  }

rational≤refl : ∀ q → q ≤ q
rational≤refl q = *≤* (+≤+ (s≤s z≤n))

zero≤two : 0ℚ ≤ two
zero≤two = *≤* (+≤+ z≤n)

two≤four : two ≤ four
two≤four = *≤* (+≤+ (s≤s (s≤s z≤n)))

zero≤four : 0ℚ ≤ four
zero≤four = *≤* (+≤+ z≤n)

k01RowBound :
  ∀ row →
  rowWeightedSum canonicalK01Finite row ≤ two * oneWeightHigh row
k01RowBound high110 = rational≤refl two
k01RowBound high101 = rational≤refl two
k01RowBound high011 = rational≤refl two

k01ColumnBound :
  ∀ col →
  columnWeightedSum canonicalK01Finite col ≤ four * oneWeightLow col
k01ColumnBound low100 = zero≤four
k01ColumnBound low010 = two≤four
k01ColumnBound low001 = rational≤refl four

canonicalK01Certificate :
  FiniteWeightedSchurCertificate canonicalK01Finite
canonicalK01Certificate = record
  { rowConstant = two
  ; columnConstant = four
  ; rowBound = k01RowBound
  ; columnBound = k01ColumnBound
  }

k10RowBound :
  ∀ row →
  rowWeightedSum canonicalK10Finite row ≤ four * oneWeightLow row
k10RowBound low100 = zero≤four
k10RowBound low010 = two≤four
k10RowBound low001 = rational≤refl four

k10ColumnBound :
  ∀ col →
  columnWeightedSum canonicalK10Finite col ≤ two * oneWeightHigh col
k10ColumnBound high110 = rational≤refl two
k10ColumnBound high101 = rational≤refl two
k10ColumnBound high011 = rational≤refl two

canonicalK10Certificate :
  FiniteWeightedSchurCertificate canonicalK10Finite
canonicalK10Certificate = record
  { rowConstant = four
  ; columnConstant = two
  ; rowBound = k10RowBound
  ; columnBound = k10ColumnBound
  }
