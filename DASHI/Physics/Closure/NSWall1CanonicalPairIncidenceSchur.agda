module DASHI.Physics.Closure.NSWall1CanonicalPairIncidenceSchur where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; _+_; _*_; _≤_)

open import DASHI.Analysis.FiniteWeightedKernelSums
open import DASHI.Physics.Closure.NSPairIncidenceKernel
open import DASHI.Physics.Closure.NSWall1CanonicalFiniteSchur

------------------------------------------------------------------------
-- Exact pair-incidence realization of the canonical 3 x 3 matrices.
--
-- This removes a finite representation ambiguity: the canonical Schur matrix
-- is not merely a hand-written coarse matrix, but the fold of three declared
-- resonant pair atoms.  The remaining promotion theorem is the identification
-- of these six enumerated modes with the corresponding Fourier carrier at each
-- physical shell/cutoff.
------------------------------------------------------------------------

data CanonicalPair01 : Set where
  pair110010 pair101001 pair011001 : CanonicalPair01

canonicalPairs01 : List CanonicalPair01
canonicalPairs01 = pair110010 ∷ pair101001 ∷ pair011001 ∷ []

pair01Contribution :
  CanonicalPair01 → HighMode → LowMode → ℚ
pair01Contribution pair110010 high110 low010 = two
pair01Contribution pair101001 high101 low001 = two
pair01Contribution pair011001 high011 low001 = two
pair01Contribution _ _ _ = 0ℚ

canonicalPair01Data :
  PairIncidenceData CanonicalPair01 HighMode LowMode ℚ
canonicalPair01Data = record
  { pairs = canonicalPairs01
  ; rows = highModes
  ; columns = lowModes
  ; zero = 0ℚ
  ; add = _+_
  ; multiply = _*_
  ; _≤_ = _≤_
  ; pairContribution = pair01Contribution
  ; rowWeight = oneWeightHigh
  ; colWeight = oneWeightLow
  }

pair01KernelMatchesCanonical :
  ∀ row col →
  pairKernelEntry canonicalPair01Data row col ≡ canonicalK01 row col
pair01KernelMatchesCanonical high110 low100 = refl
pair01KernelMatchesCanonical high110 low010 = refl
pair01KernelMatchesCanonical high110 low001 = refl
pair01KernelMatchesCanonical high101 low100 = refl
pair01KernelMatchesCanonical high101 low010 = refl
pair01KernelMatchesCanonical high101 low001 = refl
pair01KernelMatchesCanonical high011 low100 = refl
pair01KernelMatchesCanonical high011 low010 = refl
pair01KernelMatchesCanonical high011 low001 = refl

pair01RowBound :
  ∀ row →
  _≤_ (asFiniteWeightedKernel canonicalPair01Data)
    (rowWeightedSum (asFiniteWeightedKernel canonicalPair01Data) row)
    (multiply (asFiniteWeightedKernel canonicalPair01Data)
      two
      (rowWeight canonicalPair01Data row))
pair01RowBound high110 = rational≤refl two
pair01RowBound high101 = rational≤refl two
pair01RowBound high011 = rational≤refl two

pair01ColumnBound :
  ∀ col →
  _≤_ (asFiniteWeightedKernel canonicalPair01Data)
    (columnWeightedSum (asFiniteWeightedKernel canonicalPair01Data) col)
    (multiply (asFiniteWeightedKernel canonicalPair01Data)
      four
      (colWeight canonicalPair01Data col))
pair01ColumnBound low100 = zero≤four
pair01ColumnBound low010 = two≤four
pair01ColumnBound low001 = rational≤refl four

canonicalPair01Certificate :
  PairIncidenceWeightedCertificate canonicalPair01Data
canonicalPair01Certificate = record
  { finiteCertificate = record
      { rowConstant = two
      ; columnConstant = four
      ; rowBound = pair01RowBound
      ; columnBound = pair01ColumnBound
      }
  }

------------------------------------------------------------------------
-- Reverse direction.
------------------------------------------------------------------------

data CanonicalPair10 : Set where
  pair010110 pair001101 pair001011 : CanonicalPair10

canonicalPairs10 : List CanonicalPair10
canonicalPairs10 = pair010110 ∷ pair001101 ∷ pair001011 ∷ []

pair10Contribution :
  CanonicalPair10 → LowMode → HighMode → ℚ
pair10Contribution pair010110 low010 high110 = two
pair10Contribution pair001101 low001 high101 = two
pair10Contribution pair001011 low001 high011 = two
pair10Contribution _ _ _ = 0ℚ

canonicalPair10Data :
  PairIncidenceData CanonicalPair10 LowMode HighMode ℚ
canonicalPair10Data = record
  { pairs = canonicalPairs10
  ; rows = lowModes
  ; columns = highModes
  ; zero = 0ℚ
  ; add = _+_
  ; multiply = _*_
  ; _≤_ = _≤_
  ; pairContribution = pair10Contribution
  ; rowWeight = oneWeightLow
  ; colWeight = oneWeightHigh
  }

pair10KernelMatchesCanonical :
  ∀ row col →
  pairKernelEntry canonicalPair10Data row col ≡ canonicalK10 row col
pair10KernelMatchesCanonical low100 high110 = refl
pair10KernelMatchesCanonical low100 high101 = refl
pair10KernelMatchesCanonical low100 high011 = refl
pair10KernelMatchesCanonical low010 high110 = refl
pair10KernelMatchesCanonical low010 high101 = refl
pair10KernelMatchesCanonical low010 high011 = refl
pair10KernelMatchesCanonical low001 high110 = refl
pair10KernelMatchesCanonical low001 high101 = refl
pair10KernelMatchesCanonical low001 high011 = refl

pair10RowBound :
  ∀ row →
  _≤_ (asFiniteWeightedKernel canonicalPair10Data)
    (rowWeightedSum (asFiniteWeightedKernel canonicalPair10Data) row)
    (multiply (asFiniteWeightedKernel canonicalPair10Data)
      four
      (rowWeight canonicalPair10Data row))
pair10RowBound low100 = zero≤four
pair10RowBound low010 = two≤four
pair10RowBound low001 = rational≤refl four

pair10ColumnBound :
  ∀ col →
  _≤_ (asFiniteWeightedKernel canonicalPair10Data)
    (columnWeightedSum (asFiniteWeightedKernel canonicalPair10Data) col)
    (multiply (asFiniteWeightedKernel canonicalPair10Data)
      two
      (colWeight canonicalPair10Data col))
pair10ColumnBound high110 = rational≤refl two
pair10ColumnBound high101 = rational≤refl two
pair10ColumnBound high011 = rational≤refl two

canonicalPair10Certificate :
  PairIncidenceWeightedCertificate canonicalPair10Data
canonicalPair10Certificate = record
  { finiteCertificate = record
      { rowConstant = four
      ; columnConstant = two
      ; rowBound = pair10RowBound
      ; columnBound = pair10ColumnBound
      }
  }
