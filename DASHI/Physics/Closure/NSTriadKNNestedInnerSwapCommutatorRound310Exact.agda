module DASHI.Physics.Closure.NSTriadKNNestedInnerSwapCommutatorRound310Exact where

------------------------------------------------------------------------
-- ROUND310 / INNER OUTPUT-FIBRE SWAP TURNS N_p INTO A PAIRED COMMUTATOR
--
-- R309 exposes the nested carrier a+b=p, p+q=k before norms.  The physical
-- output-p fibre is exactly closed under a/b swap (R224), while R120 proves
-- that the sum of the two ordered Galerkin vectors is the pure helical
-- multiplier-difference commutator.
--
-- Therefore no orbit quotient or division by two is required.  We keep the
-- exact doubling identity
--
--   N_p + N_p
--     = fold_{a+b=p} [ N_ab + N_ba ]
--     = fold_{a+b=p} pureCommutator_ab.
--
-- This gives the nested R301 object two distinct exact geometric structures:
-- an INNER helical multiplier difference and the OUTER R307 slot/null kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorPartnerRound120Exact as R120

foldPointwiseAddVector :
  ∀ {r} {F : C3.RealField r}
    (left right : Physical.PhysicalTriadIncidence → C3.Complex3 F)
    (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector (λ tau → C3.complex3Add (left tau) (right tau)) items
  ≡ C3.complex3Add (R224.foldVector left items) (R224.foldVector right items)
foldPointwiseAddVector {F = F} left right [] =
  sym (zeroPlusZero F)
  where
  zeroPlusZero : ∀ {r} (G : C3.RealField r) →
    C3.complex3Add (C3.complex3Zero G) (C3.complex3Zero G)
    ≡ C3.complex3Zero G
  zeroPlusZero G =
    Algebra.complex3Ext
      (Algebra.complexAddZeroLeft (C3.complexZero G))
      (Algebra.complexAddZeroLeft (C3.complexZero G))
      (Algebra.complexAddZeroLeft (C3.complexZero G))
foldPointwiseAddVector left right (tau ∷ rest) =
  trans
    (cong (C3.complex3Add (C3.complex3Add (left tau) (right tau)))
      (foldPointwiseAddVector left right rest))
    (shuffle
      (left tau) (right tau)
      (R224.foldVector left rest) (R224.foldVector right rest))
  where
  shuffle : ∀ {r} {F : C3.RealField r}
    (a b c d : C3.Complex3 F) →
    C3.complex3Add (C3.complex3Add a b) (C3.complex3Add c d)
    ≡ C3.complex3Add (C3.complex3Add a c) (C3.complex3Add b d)
  shuffle {F = G} a b c d =
    trans
      (sym (Algebra.complex3AddAssociative a b (C3.complex3Add c d)))
      (trans
        (cong (C3.complex3Add a)
          (trans
            (Algebra.complex3AddAssociative b c d)
            (trans
              (cong (λ x → C3.complex3Add x d)
                (commute b c))
              (sym (Algebra.complex3AddAssociative c b d)))))
        (Algebra.complex3AddAssociative a c (C3.complex3Add b d)))
    where
    commute : ∀ (x y : C3.Complex3 G) →
      C3.complex3Add x y ≡ C3.complex3Add y x
    commute (C3.complex3 x₁ x₂ x₃) (C3.complex3 y₁ y₂ y₃) =
      Algebra.complex3Ext
        (Algebra.complexAddCommutative x₁ y₁)
        (Algebra.complexAddCommutative x₂ y₂)
        (Algebra.complexAddCommutative x₃ y₃)

projectedNonlinearityAsFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (p : Z3.FourierMode) →
  Audit.projectedNonlinearity system p
  ≡ R224.foldVector (Audit.projectedOrderedTerm system)
      (Output.physicalOutputFiber (Audit.cutoff system) p)
projectedNonlinearityAsFold system p = pointwise
  (Output.physicalOutputFiber (Audit.cutoff system) p)
  where
  pointwise :
    (items : List Physical.PhysicalTriadIncidence) →
    Audit.sumVectors (Audit.mapTriadTerms system items)
    ≡ R224.foldVector (Audit.projectedOrderedTerm system) items
  pointwise [] = refl
  pointwise (tau ∷ rest) =
    cong₂ C3.complex3Add refl (pointwise rest)

fixedOutputSwapFoldInvariant :
  ∀ {r} {F : C3.RealField r}
    (value : Physical.PhysicalTriadIncidence → C3.Complex3 F)
    (cutoff : Nat) (output : Z3.FourierMode) →
  R224.foldVector (λ tau → value (Symmetry.swapTriad tau))
    (Output.physicalOutputFiber cutoff output)
  ≡ R224.foldVector value (Output.physicalOutputFiber cutoff output)
fixedOutputSwapFoldInvariant value cutoff output =
  trans
    (sym
      (R224.foldMap value Symmetry.swapTriad
        (Output.physicalOutputFiber cutoff output)))
    (R224.foldPermutationInvariant value
      (R224.swapOutputFibrePermutation cutoff output))

pairedInnerVector :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
pairedInnerVector system tau =
  C3.complex3Add
    (Audit.projectedOrderedTerm system tau)
    (Audit.projectedOrderedTerm system (Symmetry.swapTriad tau))

twiceProjectedNonlinearityIsPairedInnerFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (p : Z3.FourierMode) →
  C3.complex3Add
    (Audit.projectedNonlinearity system p)
    (Audit.projectedNonlinearity system p)
  ≡
  R224.foldVector (pairedInnerVector system)
    (Output.physicalOutputFiber (Audit.cutoff system) p)
twiceProjectedNonlinearityIsPairedInnerFold system p =
  let
    items = Output.physicalOutputFiber (Audit.cutoff system) p
    value = Audit.projectedOrderedTerm system
  in
  trans
    (cong₂ C3.complex3Add
      (projectedNonlinearityAsFold system p)
      (projectedNonlinearityAsFold system p))
    (trans
      (cong (C3.complex3Add (R224.foldVector value items))
        (sym (fixedOutputSwapFoldInvariant value (Audit.cutoff system) p)))
      (sym
        (foldPointwiseAddVector value
          (λ tau → value (Symmetry.swapTriad tau)) items)))

innerPureCommutatorVector :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (helical : ∀ tau → R120.PhysicalHelicalOutputPair system tau) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
innerPureCommutatorVector system helical tau =
  R120.pureCommutatorVector system tau (helical tau)

pairedInnerVectorIsPureCommutator :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (helical : ∀ tau → R120.PhysicalHelicalOutputPair system tau)
    (tau : Physical.PhysicalTriadIncidence) →
  pairedInnerVector system tau
  ≡ innerPureCommutatorVector system helical tau
pairedInnerVectorIsPureCommutator system helical tau =
  R120.sharedOutputPartnerSumIsPureMultiplierDifference
    system tau (helical tau)

foldPointwiseCongVector :
  ∀ {r} {F : C3.RealField r}
    {left right : Physical.PhysicalTriadIncidence → C3.Complex3 F} →
  (∀ tau → left tau ≡ right tau) →
  (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector left items ≡ R224.foldVector right items
foldPointwiseCongVector pointwise [] = refl
foldPointwiseCongVector pointwise (tau ∷ rest) =
  cong₂ C3.complex3Add
    (pointwise tau)
    (foldPointwiseCongVector pointwise rest)

twiceProjectedNonlinearityIsInnerPureCommutatorFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (helical : ∀ tau → R120.PhysicalHelicalOutputPair system tau)
    (p : Z3.FourierMode) →
  C3.complex3Add
    (Audit.projectedNonlinearity system p)
    (Audit.projectedNonlinearity system p)
  ≡
  R224.foldVector (innerPureCommutatorVector system helical)
    (Output.physicalOutputFiber (Audit.cutoff system) p)
twiceProjectedNonlinearityIsInnerPureCommutatorFold system helical p =
  trans
    (twiceProjectedNonlinearityIsPairedInnerFold system p)
    (foldPointwiseCongVector
      (pairedInnerVectorIsPureCommutator system helical)
      (Output.physicalOutputFiber (Audit.cutoff system) p))

round310InnerFixedOutputSwapPairingClosed : Bool
round310InnerFixedOutputSwapPairingClosed = true

round310NoOrbitDivisionOrCardinalityUsed : Bool
round310NoOrbitDivisionOrCardinalityUsed = true

round310InnerPureMultiplierDifferenceExposed : Bool
round310InnerPureMultiplierDifferenceExposed = true

round310NestedDoubleDefectEstimateClosed : Bool
round310NestedDoubleDefectEstimateClosed = false

round310PackageAClosed : Bool
round310PackageAClosed = false

round310ClayPromotion : Bool
round310ClayPromotion = false
