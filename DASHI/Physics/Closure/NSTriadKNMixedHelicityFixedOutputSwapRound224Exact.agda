module DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact where

------------------------------------------------------------------------
-- ROUND224 / FIXED-OUTPUT SWAP REINDEXING OF THE TWO MIXED HELICITY CHANNELS
--
-- Round223 proves pairwise
--
--   i K_pq = 2 (u_p+ x u_q- - u_p- x u_q+).
--
-- The physical output fibre is closed under p/q swap.  This file upgrades that
-- closure to an exact list permutation and proves that the (-,+) mixed channel
-- on the swapped incidence is the negative of the (+,-) channel on the source.
-- No shell count, orbit cardinality, or analytic estimate is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberConjugationRound35Exact as Fibre35
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as KFree
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeSelectedSwapAntisymmetryRound118Exact as R118

swapOutputFibreMemberCube :
  ∀ {cutoff output tau} →
  tau Cube.∈ Output.physicalOutputFiber cutoff output →
  Symmetry.swapTriad tau Cube.∈ Output.physicalOutputFiber cutoff output
swapOutputFibreMemberCube {cutoff} {output} {tau} member =
  Output.physicalOutputFiberComplete
    (KFree.stdMemberToCube
      (R38.swapTriadMember
        (KFree.cubeMemberToStd
          (Fibre35.physicalOutputFiberMemberEnumeration member))))
    (trans (Symmetry.swapTriadK tau) (Output.physicalOutputFiberSound member))

swapOutputFibreMember :
  ∀ {cutoff output tau} →
  tau ∈ Output.physicalOutputFiber cutoff output →
  Symmetry.swapTriad tau ∈ Output.physicalOutputFiber cutoff output
swapOutputFibreMember member =
  KFree.cubeMemberToStd
    (swapOutputFibreMemberCube (KFree.stdMemberToCube member))

mappedSwapForward :
  ∀ {cutoff output tau} →
  tau ∈ map Symmetry.swapTriad (Output.physicalOutputFiber cutoff output) →
  tau ∈ Output.physicalOutputFiber cutoff output
mappedSwapForward member with ∈-map⁻ Symmetry.swapTriad member
... | source , sourceMember , sourceMaps =
  subst
    (λ selected → selected ∈ Output.physicalOutputFiber _ _)
    sourceMaps
    (swapOutputFibreMember sourceMember)

mappedSwapBackward :
  ∀ {cutoff output tau} →
  tau ∈ Output.physicalOutputFiber cutoff output →
  tau ∈ map Symmetry.swapTriad (Output.physicalOutputFiber cutoff output)
mappedSwapBackward {tau = tau} member =
  subst
    (λ selected → selected ∈ map Symmetry.swapTriad (Output.physicalOutputFiber _ _))
    (R38.swapTriadInvolutiveExact tau)
    (∈-map⁺ Symmetry.swapTriad (swapOutputFibreMember member))

swapOutputFibrePermutation :
  (cutoff : Nat) (output : Z3.FourierMode) →
  map Symmetry.swapTriad (Output.physicalOutputFiber cutoff output)
  Perm.↭ Output.physicalOutputFiber cutoff output
swapOutputFibrePermutation cutoff output =
  KFree.uniqueMembershipEquivalenceToPermutation
    (UniqueP.map⁺ R38.swapTriadInjective (KFree.physicalOutputFiberUnique cutoff output))
    (KFree.physicalOutputFiberUnique cutoff output)
    mappedSwapForward
    mappedSwapBackward

mixedPlusMinus :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
mixedPlusMinus {E = E} {I = I} S velocity tau =
  Cross.complex3Cross
    (Helical.helicalProjectorPlus E I S (Physical.p tau) (velocity (Physical.p tau)))
    (Helical.helicalProjectorMinus E I S (Physical.q tau) (velocity (Physical.q tau)))

mixedMinusPlus :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
mixedMinusPlus {E = E} {I = I} S velocity tau =
  Cross.complex3Cross
    (Helical.helicalProjectorMinus E I S (Physical.p tau) (velocity (Physical.p tau)))
    (Helical.helicalProjectorPlus E I S (Physical.q tau) (velocity (Physical.q tau)))

mixedMinusPlusAfterSwapIsNegativePlusMinus :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  mixedMinusPlus S velocity (Symmetry.swapTriad tau)
  ≡ C3.complex3Negate (mixedPlusMinus S velocity tau)
mixedMinusPlusAfterSwapIsNegativePlusMinus S velocity tau =
  R118.crossAnticommutative
    (Helical.helicalProjectorPlus _ _ S (Physical.p tau) (velocity (Physical.p tau)))
    (Helical.helicalProjectorMinus _ _ S (Physical.q tau) (velocity (Physical.q tau)))

foldVector :
  ∀ {r} {F : C3.RealField r} →
  (Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → C3.Complex3 F
foldVector {F = F} value [] = C3.complex3Zero F
foldVector value (tau ∷ rest) =
  C3.complex3Add (value tau) (foldVector value rest)

foldMap :
  ∀ {r} {F : C3.RealField r}
    (value : Physical.PhysicalTriadIncidence → C3.Complex3 F)
    (reindex : Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence)
    (items : List Physical.PhysicalTriadIncidence) →
  foldVector value (map reindex items)
  ≡ foldVector (λ tau → value (reindex tau)) items
foldMap value reindex [] = refl
foldMap value reindex (tau ∷ rest) =
  cong (C3.complex3Add (value (reindex tau))) (foldMap value reindex rest)

foldPermutationInvariant :
  ∀ {r} {F : C3.RealField r}
    (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  ∀ {left right} → left Perm.↭ right →
  foldVector value left ≡ foldVector value right
foldPermutationInvariant value Perm.refl = refl
foldPermutationInvariant value (Perm.prep x permutation) =
  cong (C3.complex3Add (value x))
    (foldPermutationInvariant value permutation)
foldPermutationInvariant {F = F} value
    (Perm.swap {ys = ys} x y permutation) =
  trans
    (cong
      (λ tail → C3.complex3Add (value x) (C3.complex3Add (value y) tail))
      (foldPermutationInvariant value permutation))
    (trans
      (sym (Algebra.complex3AddAssociative
        (value x) (value y) (foldVector value ys)))
      (trans
        (cong
          (λ head → C3.complex3Add head (foldVector value ys))
          (swapAdd (value x) (value y)))
        (Algebra.complex3AddAssociative
          (value y) (value x) (foldVector value ys))))
  where
  swapAdd : ∀ (a b : C3.Complex3 F) → C3.complex3Add a b ≡ C3.complex3Add b a
  swapAdd (C3.complex3 ax ay az) (C3.complex3 bx by bz) =
    Algebra.complex3Ext
      (Algebra.complexAddCommutative ax bx)
      (Algebra.complexAddCommutative ay by)
      (Algebra.complexAddCommutative az bz)
foldPermutationInvariant value (Perm.trans first second) =
  trans
    (foldPermutationInvariant value first)
    (foldPermutationInvariant value second)

fixedOutputMinusPlusReindexesToNegativePlusMinus :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat) (output : Z3.FourierMode) →
  foldVector (mixedMinusPlus S velocity)
    (Output.physicalOutputFiber cutoff output)
  ≡
  foldVector (λ tau → C3.complex3Negate (mixedPlusMinus S velocity tau))
    (Output.physicalOutputFiber cutoff output)
fixedOutputMinusPlusReindexesToNegativePlusMinus
    S velocity cutoff output =
  trans
    (sym
      (foldPermutationInvariant (mixedMinusPlus S velocity)
        (swapOutputFibrePermutation cutoff output)))
    (trans
      (foldMap (mixedMinusPlus S velocity) Symmetry.swapTriad
        (Output.physicalOutputFiber cutoff output))
      (foldPointwise
        (Output.physicalOutputFiber cutoff output)))
  where
  foldPointwise :
    (items : List Physical.PhysicalTriadIncidence) →
    foldVector (λ tau → mixedMinusPlus S velocity (Symmetry.swapTriad tau)) items
    ≡ foldVector (λ tau → C3.complex3Negate (mixedPlusMinus S velocity tau)) items
  foldPointwise [] = refl
  foldPointwise (tau ∷ rest) =
    cong₂ C3.complex3Add
      (mixedMinusPlusAfterSwapIsNegativePlusMinus S velocity tau)
      (foldPointwise rest)

round224FixedOutputSwapPermutationClosed : Bool
round224FixedOutputSwapPermutationClosed = true

round224MixedChannelsExactlyReindexed : Bool
round224MixedChannelsExactlyReindexed = true

round224MixedHelicityIntegratedBudgetClosed : Bool
round224MixedHelicityIntegratedBudgetClosed = false

round224PackageAClosed : Bool
round224PackageAClosed = false

round224ClayPromotion : Bool
round224ClayPromotion = false

round224FixedOutputSwapPermutationClosedIsTrue :
  round224FixedOutputSwapPermutationClosed ≡ true
round224FixedOutputSwapPermutationClosedIsTrue = refl

round224MixedChannelsExactlyReindexedIsTrue :
  round224MixedChannelsExactlyReindexed ≡ true
round224MixedChannelsExactlyReindexedIsTrue = refl

round224MixedHelicityIntegratedBudgetClosedIsFalse :
  round224MixedHelicityIntegratedBudgetClosed ≡ false
round224MixedHelicityIntegratedBudgetClosedIsFalse = refl

round224PackageAClosedIsFalse : round224PackageAClosed ≡ false
round224PackageAClosedIsFalse = refl

round224ClayPromotionIsFalse : round224ClayPromotion ≡ false
round224ClayPromotionIsFalse = refl
