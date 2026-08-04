module DASHI.Physics.Closure.NSTriadKNLuoPeriodicComplexMultiplierCancellationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions
-- of Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- PURPOSE
-- Use the exact Z^3 additive laws and the exact complex ring to prove the
-- canonical periodic increment multiplier is symmetric and vanishes whenever
-- either input mode is zero.  These are derived properties of
--
--   m(k,l)=hatPhi(k+l)-hatPhi(k)-hatPhi(l)+hatPhi(0),
--
-- not fields of the periodic character data.  The same cancellation is then
-- transported to the literal weighted-increment integral coefficient.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNIntegerFourierModeAddExact as Z3Alg
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicComplexCharacterMultiplierExact as Periodic

periodicPairMultiplier :
  ∀ {r} {F : C3.RealField r} →
  Periodic.PeriodicComplexCharacterData F →
  Z3.FourierMode → Z3.FourierMode → C3.Complex F
periodicPairMultiplier data left right =
  C3.complexAdd
    (C3.complexSubtract
      (C3.complexSubtract
        (Periodic.periodicKernelTransform data (Z3.addMode left right))
        (Periodic.periodicKernelTransform data left))
      (Periodic.periodicKernelTransform data right))
    (Periodic.periodicKernelTransform data Z3.zeroMode)

periodicPairMultiplierMeaning :
  ∀ {r} {F : C3.RealField r}
    (data : Periodic.PeriodicComplexCharacterData F)
    (left right : Z3.FourierMode) →
  Periodic.periodicWeightedIncrement data left right
  ≡ periodicPairMultiplier data left right
periodicPairMultiplierMeaning =
  Periodic.periodicWeightedIncrementMultiplierIdentity

periodicPairMultiplierSymmetric :
  ∀ {r} {F : C3.RealField r}
    (data : Periodic.PeriodicComplexCharacterData F)
    (left right : Z3.FourierMode) →
  periodicPairMultiplier data left right
  ≡ periodicPairMultiplier data right left
periodicPairMultiplierSymmetric {F = F} data left right
  rewrite Z3Alg.addCommutative left right =
  R.solve 4
    (λ outputTransform leftTransform rightTransform zeroTransform →
      (((outputTransform R.⊕ (R.⊝ leftTransform))
          R.⊕ (R.⊝ rightTransform))
          R.⊕ zeroTransform)
      R.⊜
      (((outputTransform R.⊕ (R.⊝ rightTransform))
          R.⊕ (R.⊝ leftTransform))
          R.⊕ zeroTransform))
    refl
    (Periodic.periodicKernelTransform data (Z3.addMode right left))
    (Periodic.periodicKernelTransform data left)
    (Periodic.periodicKernelTransform data right)
    (Periodic.periodicKernelTransform data Z3.zeroMode)
  where module R = Ring.Solver F

periodicPairMultiplierLeftZero :
  ∀ {r} {F : C3.RealField r}
    (data : Periodic.PeriodicComplexCharacterData F)
    (right : Z3.FourierMode) →
  periodicPairMultiplier data Z3.zeroMode right
  ≡ C3.complexZero F
periodicPairMultiplierLeftZero {F = F} data right
  rewrite Z3Alg.addZeroLeft right =
  R.solve 2
    (λ rightTransform zeroTransform →
      (((rightTransform R.⊕ (R.⊝ zeroTransform))
          R.⊕ (R.⊝ rightTransform))
          R.⊕ zeroTransform)
      R.⊜ R.Κ (C3.complexZero F))
    refl
    (Periodic.periodicKernelTransform data right)
    (Periodic.periodicKernelTransform data Z3.zeroMode)
  where module R = Ring.Solver F

periodicPairMultiplierRightZero :
  ∀ {r} {F : C3.RealField r}
    (data : Periodic.PeriodicComplexCharacterData F)
    (left : Z3.FourierMode) →
  periodicPairMultiplier data left Z3.zeroMode
  ≡ C3.complexZero F
periodicPairMultiplierRightZero {F = F} data left
  rewrite Z3Alg.addZeroRight left =
  R.solve 2
    (λ leftTransform zeroTransform →
      (((leftTransform R.⊕ (R.⊝ leftTransform))
          R.⊕ (R.⊝ zeroTransform))
          R.⊕ zeroTransform)
      R.⊜ R.Κ (C3.complexZero F))
    refl
    (Periodic.periodicKernelTransform data left)
    (Periodic.periodicKernelTransform data Z3.zeroMode)
  where module R = Ring.Solver F

periodicWeightedIncrementSymmetric :
  ∀ {r} {F : C3.RealField r}
    (data : Periodic.PeriodicComplexCharacterData F)
    (left right : Z3.FourierMode) →
  Periodic.periodicWeightedIncrement data left right
  ≡ Periodic.periodicWeightedIncrement data right left
periodicWeightedIncrementSymmetric data left right =
  trans
    (periodicPairMultiplierMeaning data left right)
    (trans
      (periodicPairMultiplierSymmetric data left right)
      (sym (periodicPairMultiplierMeaning data right left)))

periodicWeightedIncrementLeftZero :
  ∀ {r} {F : C3.RealField r}
    (data : Periodic.PeriodicComplexCharacterData F)
    (right : Z3.FourierMode) →
  Periodic.periodicWeightedIncrement data Z3.zeroMode right
  ≡ C3.complexZero F
periodicWeightedIncrementLeftZero data right =
  trans
    (periodicPairMultiplierMeaning data Z3.zeroMode right)
    (periodicPairMultiplierLeftZero data right)

periodicWeightedIncrementRightZero :
  ∀ {r} {F : C3.RealField r}
    (data : Periodic.PeriodicComplexCharacterData F)
    (left : Z3.FourierMode) →
  Periodic.periodicWeightedIncrement data left Z3.zeroMode
  ≡ C3.complexZero F
periodicWeightedIncrementRightZero data left =
  trans
    (periodicPairMultiplierMeaning data left Z3.zeroMode)
    (periodicPairMultiplierRightZero data left)

periodicComplexMultiplierSymmetryClosed : Bool
periodicComplexMultiplierSymmetryClosed = true

periodicComplexZeroModeCancellationClosed : Bool
periodicComplexZeroModeCancellationClosed = true

periodicComplexMultiplierSymmetryClosedIsTrue :
  periodicComplexMultiplierSymmetryClosed ≡ true
periodicComplexMultiplierSymmetryClosedIsTrue = refl

periodicComplexZeroModeCancellationClosedIsTrue :
  periodicComplexZeroModeCancellationClosed ≡ true
periodicComplexZeroModeCancellationClosedIsTrue = refl
