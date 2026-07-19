module DASHI.Analysis.RiemannPrimePowerArithmetic where

-- Concrete finite arithmetic for the prime-power side of the Riemann explicit
-- formula.  This module computes only over DASHI's canonical 15 tracked prime
-- lanes and a finite exponent cutoff.  It does not identify that truncation
-- with the full von-Mangoldt sum.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Nat using (_*_)
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
open import DASHI.TrackedPrimes using
  ( SSP
  ; toNat
  ; mapTrackedPrimes15
  )
open import DASHI.Analysis.WeilTestSpace

------------------------------------------------------------------------
-- Exact tracked prime powers
------------------------------------------------------------------------

natPow : Nat → Nat → Nat
natPow base zero = 1
natPow base (suc exponent) = base * natPow base exponent

-- The exponent index is zero based: index zero denotes p¹, index one p², etc.
trackedPrimePowerValue : SSP → Nat → Nat
trackedPrimePowerValue p exponentIndex =
  natPow (toNat p) (suc exponentIndex)

------------------------------------------------------------------------
-- Scalar/test kernel used by the explicit-formula prime side
------------------------------------------------------------------------

record PrimePowerKernel (space : WeilTestSpace) : Set₁ where
  open WeilTestSpace space
  field
    _*S_ : Scalar → Scalar → Scalar
    logPrimeWeight : SSP → Scalar
    sampleAtNat : Test → Nat → Scalar

weightedPrimePowerTerm :
  (space : WeilTestSpace) →
  PrimePowerKernel space →
  WeilTestSpace.Test space →
  SSP →
  Nat →
  WeilTestSpace.Scalar space
weightedPrimePowerTerm space kernel f p exponentIndex =
  PrimePowerKernel._*S_ kernel
    (PrimePowerKernel.logPrimeWeight kernel p)
    (PrimePowerKernel.sampleAtNat kernel f
      (trackedPrimePowerValue p exponentIndex))

------------------------------------------------------------------------
-- Finite exponent and tracked-prime sums
------------------------------------------------------------------------

sumExponentTerms :
  (space : WeilTestSpace) →
  PrimePowerKernel space →
  Nat →
  WeilTestSpace.Test space →
  SSP →
  WeilTestSpace.Scalar space
sumExponentTerms space kernel zero f p =
  WeilTestSpace.zeroS space
sumExponentTerms space kernel (suc cutoff) f p =
  WeilTestSpace._+S_ space
    (weightedPrimePowerTerm space kernel f p cutoff)
    (sumExponentTerms space kernel cutoff f p)

sum15Scalar :
  (space : WeilTestSpace) →
  Vec15 (WeilTestSpace.Scalar space) →
  WeilTestSpace.Scalar space
sum15Scalar space
  (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  WeilTestSpace._+S_ space a2
    (WeilTestSpace._+S_ space a3
      (WeilTestSpace._+S_ space a5
        (WeilTestSpace._+S_ space a7
          (WeilTestSpace._+S_ space a11
            (WeilTestSpace._+S_ space a13
              (WeilTestSpace._+S_ space a17
                (WeilTestSpace._+S_ space a19
                  (WeilTestSpace._+S_ space a23
                    (WeilTestSpace._+S_ space a29
                      (WeilTestSpace._+S_ space a31
                        (WeilTestSpace._+S_ space a41
                          (WeilTestSpace._+S_ space a47
                            (WeilTestSpace._+S_ space a59 a71)))))))))))))

trackedPrimePowerLanes :
  (space : WeilTestSpace) →
  PrimePowerKernel space →
  Nat →
  WeilTestSpace.Test space →
  Vec15 (WeilTestSpace.Scalar space)
trackedPrimePowerLanes space kernel cutoff f =
  mapTrackedPrimes15 (λ p → sumExponentTerms space kernel cutoff f p)

trackedPrimePowerTerm :
  (space : WeilTestSpace) →
  PrimePowerKernel space →
  Nat →
  WeilTestSpace.Test space →
  WeilTestSpace.Scalar space
trackedPrimePowerTerm space kernel cutoff f =
  sum15Scalar space (trackedPrimePowerLanes space kernel cutoff f)

------------------------------------------------------------------------
-- Scope receipt
------------------------------------------------------------------------

record TrackedPrimePowerBoundary : Set where
  field
    finitePrimeSupportOnly : ⊤
    finiteExponentCutoffOnly : ⊤
    noFullVonMangoldtSumClaim : ⊤
    noEulerProductCompletionClaim : ⊤
    noRiemannHypothesisPromotion : ⊤

trackedPrimePowerBoundary : TrackedPrimePowerBoundary
trackedPrimePowerBoundary = record
  { finitePrimeSupportOnly = tt
  ; finiteExponentCutoffOnly = tt
  ; noFullVonMangoldtSumClaim = tt
  ; noEulerProductCompletionClaim = tt
  ; noRiemannHypothesisPromotion = tt
  }
