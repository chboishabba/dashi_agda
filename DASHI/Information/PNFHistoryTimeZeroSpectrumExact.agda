module DASHI.Information.PNFHistoryTimeZeroSpectrumExact where

-- Original DASHI same-source zero-eigenmode transfer.
-- Source of the rank theorem: PNFFiniteRankNullityBridgeExact.
-- Source of the actual varying (history,time) covariance:
-- PNFHistoryTimeVariableDimensionExact.
-- No independent random-matrix or general spectral theorem is asserted.

open import Agda.Builtin.Nat using (Nat; suc; _∸_)
open import Data.Nat.Base using (_≤_)

import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFHistoryTimeVariableDimensionExact as Native
import DASHI.Information.PNFFiniteRankNullityBridgeExact as Rank

record HistoryTimeZeroSpectrum
  (K : Ring.ExactOrderedCommutativeRing)
  (O : Rank.FiniteFieldRankNullityOwner K)
  {depth : Nat}
  (F : Native.HistoryTimeVariableDimensionFibre K depth) : Set₂ where
  field
    zeroSpectrumAt :
      (h : Native.History F) (t : Native.Time F) →
      Rank.CovarianceZeroSpectrum K O
        (Native.actualWindowAt F h t)
        (Native.scaleAt F h t)

open HistoryTimeZeroSpectrum public

-- This is a pointwise spectral consequence for the *actual selected
-- source covariance*, and not a factorisation of some other Gram matrix.
forcedZeroModesForActualWindow :
  (K : Ring.ExactOrderedCommutativeRing) →
  (O : Rank.FiniteFieldRankNullityOwner K) →
  {depth : Nat} →
  (F : Native.HistoryTimeVariableDimensionFibre K depth) →
  (E : HistoryTimeZeroSpectrum K O F) →
  (h : Native.History F) (t : Native.Time F) →
  (Native.pAt F h t) ∸ suc (Native.kAt F h t)
    ≤ Rank.zeroEigenvalueMultiplicity (zeroSpectrumAt E h t)
forcedZeroModesForActualWindow K O F E h t =
  Rank.forcedZeroEigenvalueMultiplicityLowerBound
    K O (Native.actualWindowAt F h t)
    (Native.scaleAt F h t) (zeroSpectrumAt E h t)

-- The actual field/spectral backend must supply a non-vacuous E:
-- a raw p-dimensional eigenvalue list alone, without the same-matrix
-- zero-multiplicity=kernel-dimension identity, cannot close this gate.
