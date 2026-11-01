module DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorSwapPairingRound122Exact where

------------------------------------------------------------------------
-- ROUND122 / EXACT SWAP-PAIR DOUBLING IDENTITY
--
-- Round120 identifies the physical shared-output partner a |-> k-a with the
-- ordered-incidence p/q swap and proves that each paired ordered Galerkin
-- vector is a pure multiplier-difference commutator.  Round121 preserves the
-- signed sum through the four-way Bony partition.
--
-- For every complex-valued incidence functional V on the COMPLETE physical
-- cutoff enumeration X,
--
--   sum_X V + sum_X V = sum_X (V tau + V (swap tau)).
--
-- This uses only the Round38 exact swap permutation.  No division, free-action
-- assumption, or orbit-cardinality theorem is needed.  Specialising V to a
-- fixed-test quartic cell and using Round120 gives the exact pure-commutator
-- fold required before the remaining critical Bony-class estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorPartnerRound120Exact as R120

foldComplex :
  ∀ {r} {F : C3.RealField r} →
  (Physical.PhysicalTriadIncidence → C3.Complex F) →
  List Physical.PhysicalTriadIncidence → C3.Complex F
foldComplex {F = F} value [] = C3.complexZero F
foldComplex value (tau ∷ rest) =
  C3.complexAdd (value tau) (foldComplex value rest)

foldMap :
  ∀ {r} {F : C3.RealField r}
    (value : Physical.PhysicalTriadIncidence → C3.Complex F)
    (reindex : Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence)
    (items : List Physical.PhysicalTriadIncidence) →
  foldComplex value (map reindex items)
  ≡ foldComplex (λ tau → value (reindex tau)) items
foldMap value reindex [] = refl
foldMap value reindex (tau ∷ rest) =
  cong (C3.complexAdd (value (reindex tau)))
    (foldMap value reindex rest)

foldPermutationInvariant :
  ∀ {r} {F : C3.RealField r}
    (value : Physical.PhysicalTriadIncidence → C3.Complex F) →
  ∀ {left right} → left Perm.↭ right →
  foldComplex value left ≡ foldComplex value right
foldPermutationInvariant value Perm.refl = refl
foldPermutationInvariant value (Perm.prep x permutation) =
  cong (C3.complexAdd (value x))
    (foldPermutationInvariant value permutation)
foldPermutationInvariant {F = F} value
    (Perm.swap {ys = ys} x y permutation) =
  trans
    (cong
      (λ tail → C3.complexAdd (value x) (C3.complexAdd (value y) tail))
      (foldPermutationInvariant value permutation))
    (R.solve 3
      (λ x y tail →
        (x R.⊕ (y R.⊕ tail)) R.⊜ (y R.⊕ (x R.⊕ tail)))
      refl (value x) (value y) (foldComplex value ys))
  where module R = Ring.Solver F
foldPermutationInvariant value (Perm.trans first second) =
  trans
    (foldPermutationInvariant value first)
    (foldPermutationInvariant value second)

foldPointwiseAdd :
  ∀ {r} {F : C3.RealField r}
    (left right : Physical.PhysicalTriadIncidence → C3.Complex F)
    (items : List Physical.PhysicalTriadIncidence) →
  foldComplex (λ tau → C3.complexAdd (left tau) (right tau)) items
  ≡ C3.complexAdd (foldComplex left items) (foldComplex right items)
foldPointwiseAdd {F = F} left right [] =
  R.solve 0
    (R.Κ (C3.complexZero F)
      R.⊜ (R.Κ (C3.complexZero F) R.⊕ R.Κ (C3.complexZero F)))
    refl
  where module R = Ring.Solver F
foldPointwiseAdd {F = F} left right (tau ∷ rest) =
  trans
    (cong (C3.complexAdd (C3.complexAdd (left tau) (right tau)))
      (foldPointwiseAdd left right rest))
    (R.solve 4
      (λ l r ls rs →
        ((l R.⊕ r) R.⊕ (ls R.⊕ rs))
        R.⊜ ((l R.⊕ ls) R.⊕ (r R.⊕ rs)))
      refl
      (left tau) (right tau)
      (foldComplex left rest) (foldComplex right rest))
  where module R = Ring.Solver F

fullPhysicalSwapFoldInvariant :
  ∀ {r} {F : C3.RealField r}
    (value : Physical.PhysicalTriadIncidence → C3.Complex F)
    (cutoff : Nat) →
  foldComplex (λ tau → value (Symmetry.swapTriad tau))
    (Physical.physicalTriadEnumeration cutoff)
  ≡ foldComplex value (Physical.physicalTriadEnumeration cutoff)
fullPhysicalSwapFoldInvariant value cutoff =
  trans
    (sym
      (foldMap value Symmetry.swapTriad
        (Physical.physicalTriadEnumeration cutoff)))
    (foldPermutationInvariant value
      (R38.swapTriadEnumerationPermutation cutoff))

pairedValue :
  ∀ {r} {F : C3.RealField r} →
  (Physical.PhysicalTriadIncidence → C3.Complex F) →
  Physical.PhysicalTriadIncidence → C3.Complex F
pairedValue value tau =
  C3.complexAdd (value tau) (value (Symmetry.swapTriad tau))

twiceFullPhysicalFoldEqualsSwapPairedFold :
  ∀ {r} {F : C3.RealField r}
    (value : Physical.PhysicalTriadIncidence → C3.Complex F)
    (cutoff : Nat) →
  C3.complexAdd
    (foldComplex value (Physical.physicalTriadEnumeration cutoff))
    (foldComplex value (Physical.physicalTriadEnumeration cutoff))
  ≡ foldComplex (pairedValue value)
      (Physical.physicalTriadEnumeration cutoff)
twiceFullPhysicalFoldEqualsSwapPairedFold value cutoff =
  trans
    (cong
      (C3.complexAdd
        (foldComplex value (Physical.physicalTriadEnumeration cutoff)))
      (sym (fullPhysicalSwapFoldInvariant value cutoff)))
    (sym
      (foldPointwiseAdd value
        (λ tau → value (Symmetry.swapTriad tau))
        (Physical.physicalTriadEnumeration cutoff)))

quarticValue :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  C3.Complex3 F →
  Physical.PhysicalTriadIncidence → C3.Complex F
quarticValue system testCross tau = R120.quarticCell system tau testCross

pairedPureCommutatorValue :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (helical : ∀ tau → R120.PhysicalHelicalOutputPair system tau)
    (testCross : C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex F
pairedPureCommutatorValue system helical testCross tau =
  C3.hermitianPairing3
    (R120.pureCommutatorVector system tau (helical tau)) testCross

pairedQuarticValueIsPureCommutatorValue :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (helical : ∀ tau → R120.PhysicalHelicalOutputPair system tau)
    (testCross : C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  pairedValue (quarticValue system testCross) tau
  ≡ pairedPureCommutatorValue system helical testCross tau
pairedQuarticValueIsPureCommutatorValue system helical testCross tau =
  R120.partnerQuarticCellSumIsPureCommutatorPairing
    system tau (helical tau) testCross

foldPointwiseCong :
  ∀ {r} {F : C3.RealField r}
    {left right : Physical.PhysicalTriadIncidence → C3.Complex F} →
  (∀ tau → left tau ≡ right tau) →
  (items : List Physical.PhysicalTriadIncidence) →
  foldComplex left items ≡ foldComplex right items
foldPointwiseCong pointwise [] = refl
foldPointwiseCong pointwise (tau ∷ rest) =
  cong₂ C3.complexAdd
    (pointwise tau)
    (foldPointwiseCong pointwise rest)

twiceFullQuarticFoldEqualsPureCommutatorFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (helical : ∀ tau → R120.PhysicalHelicalOutputPair system tau)
    (testCross : C3.Complex3 F)
    (cutoff : Nat) →
  C3.complexAdd
    (foldComplex (quarticValue system testCross)
      (Physical.physicalTriadEnumeration cutoff))
    (foldComplex (quarticValue system testCross)
      (Physical.physicalTriadEnumeration cutoff))
  ≡ foldComplex
      (pairedPureCommutatorValue system helical testCross)
      (Physical.physicalTriadEnumeration cutoff)
twiceFullQuarticFoldEqualsPureCommutatorFold system helical testCross cutoff =
  trans
    (twiceFullPhysicalFoldEqualsSwapPairedFold
      (quarticValue system testCross) cutoff)
    (foldPointwiseCong
      (pairedQuarticValueIsPureCommutatorValue system helical testCross)
      (Physical.physicalTriadEnumeration cutoff))

round122SwapPermutationPairingIdentityClosed : Bool
round122SwapPermutationPairingIdentityClosed = true

round122NoFreeActionOrOrbitCardinalityNeeded : Bool
round122NoFreeActionOrOrbitCardinalityNeeded = true

round122FullQuarticPureCommutatorFoldClosed : Bool
round122FullQuarticPureCommutatorFoldClosed = true

round122CriticalBonyClassPaymentClosed : Bool
round122CriticalBonyClassPaymentClosed = false

round122SwapPermutationPairingIdentityClosedIsTrue :
  round122SwapPermutationPairingIdentityClosed ≡ true
round122SwapPermutationPairingIdentityClosedIsTrue = refl

round122FullQuarticPureCommutatorFoldClosedIsTrue :
  round122FullQuarticPureCommutatorFoldClosed ≡ true
round122FullQuarticPureCommutatorFoldClosedIsTrue = refl

round122CriticalBonyClassPaymentClosedIsFalse :
  round122CriticalBonyClassPaymentClosed ≡ false
round122CriticalBonyClassPaymentClosedIsFalse = refl
