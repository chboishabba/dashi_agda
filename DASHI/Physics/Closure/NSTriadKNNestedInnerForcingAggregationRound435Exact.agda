module DASHI.Physics.Closure.NSTriadKNNestedInnerForcingAggregationRound435Exact where

------------------------------------------------------------------------
-- ROUND435 / COLLAPSE THE INNER PURE-COMMUTATOR FIBRE THROUGH THE OUTER SLOT
--
-- R309 proves that the authoritative R145 slot kernel is additive in its first
-- amplitude. R310 proves, on one complete physical output-p fibre and under the
-- SAME all-inner-helical witness already required there,
--
--   N_p + N_p
--     = fold_{a+b=p} pureCommutator_ab.
--
-- Therefore the inner dependent sum may be pushed through the SAME outer slot
-- before norms:
--
--   K(P,Q,N_p+N_p,v)
--     = fold_{a+b=p} K(P,Q,pureCommutator_ab,v).
--
-- This closes a structural bridge between the mode-indexed forcing formulation
-- used by R307/R294 and the nested inner-fibre formulation used downstream.
-- It does NOT manufacture the all-inner-helical witness on an arbitrary
-- physical trajectory, does NOT identify the complete R329 selected-cell family
-- with the full R310 fibre, and does NOT pay the R423 signed heat cross.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorPartnerRound120Exact as R120
import DASHI.Physics.Closure.NSTriadKNNestedProjectedForcingSlotExpansionRound309Exact as R309
import DASHI.Physics.Closure.NSTriadKNNestedInnerSwapCommutatorRound310Exact as R310

foldVectorAsSumMap :
  ∀ {r} {F : C3.RealField r}
    (value : Physical.PhysicalTriadIncidence → C3.Complex3 F)
    (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector value items ≡ Audit.sumVectors (map value items)
foldVectorAsSumMap value [] = refl
foldVectorAsSumMap value (tau ∷ rest) =
  cong (C3.complex3Add (value tau)) (foldVectorAsSumMap value rest)

mapSlotAfterInner :
  ∀ {r} {F : C3.RealField r}
    (P Q v : C3.Complex3 F)
    (inner : Physical.PhysicalTriadIncidence → C3.Complex3 F)
    (items : List Physical.PhysicalTriadIncidence) →
  map (λ item → R145.slotKernel P Q item v) (map inner items)
  ≡ map (λ tau → R145.slotKernel P Q (inner tau) v) items
mapSlotAfterInner P Q v inner [] = refl
mapSlotAfterInner P Q v inner (tau ∷ rest) =
  cong
    (λ tail → R145.slotKernel P Q (inner tau) v ∷ tail)
    (mapSlotAfterInner P Q v inner rest)

doubledProjectedForcingSlotIsInnerPureCommutatorSlotFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (helical : ∀ tau → R120.PhysicalHelicalOutputPair system tau)
    (P Q v : C3.Complex3 F)
    (p : Z3.FourierMode) →
  R145.slotKernel P Q
    (C3.complex3Add
      (Audit.projectedNonlinearity system p)
      (Audit.projectedNonlinearity system p))
    v
  ≡
  R224.foldVector
    (λ tau →
      R145.slotKernel P Q
        (R310.innerPureCommutatorVector system helical tau)
        v)
    (Output.physicalOutputFiber (Audit.cutoff system) p)
doubledProjectedForcingSlotIsInnerPureCommutatorSlotFold
    system helical P Q v p =
  let
    items = Output.physicalOutputFiber (Audit.cutoff system) p
    inner = R310.innerPureCommutatorVector system helical
  in
  trans
    (cong
      (λ forcing → R145.slotKernel P Q forcing v)
      (R310.twiceProjectedNonlinearityIsInnerPureCommutatorFold
        system helical p))
    (trans
      (cong
        (λ forcing → R145.slotKernel P Q forcing v)
        (foldVectorAsSumMap inner items))
      (trans
        (R309.slotKernelFoldFirstAmplitude P Q v (map inner items))
        (trans
          (cong Audit.sumVectors (mapSlotAfterInner P Q v inner items))
          (sym
            (foldVectorAsSumMap
              (λ tau → R145.slotKernel P Q (inner tau) v)
              items)))))

round435InnerPureCommutatorAggregationThroughOuterSlotClosed : Bool
round435InnerPureCommutatorAggregationThroughOuterSlotClosed = true

round435NoOrbitDivisionOrCardinalityFactorIntroduced : Bool
round435NoOrbitDivisionOrCardinalityFactorIntroduced = true

round435UsesR310AllInnerHelicalWitness : Bool
round435UsesR310AllInnerHelicalWitness = true

round435ArbitraryPhysicalTrajectoryAllInnerHelicalWeldClosed : Bool
round435ArbitraryPhysicalTrajectoryAllInnerHelicalWeldClosed = false

round435FullR329SelectedFamilyEqualsR310CompleteInnerFibre : Bool
round435FullR329SelectedFamilyEqualsR310CompleteInnerFibre = false

round435R294WeightedCommutatorSameObjectWeldClosed : Bool
round435R294WeightedCommutatorSameObjectWeldClosed = false

round435R423SignedCompanionBudgetClosed : Bool
round435R423SignedCompanionBudgetClosed = false

round435PackageAClosed : Bool
round435PackageAClosed = false

round435ClayPromotion : Bool
round435ClayPromotion = false

round435InnerPureCommutatorAggregationThroughOuterSlotClosedIsTrue :
  round435InnerPureCommutatorAggregationThroughOuterSlotClosed ≡ true
round435InnerPureCommutatorAggregationThroughOuterSlotClosedIsTrue = refl

round435NoOrbitDivisionOrCardinalityFactorIntroducedIsTrue :
  round435NoOrbitDivisionOrCardinalityFactorIntroduced ≡ true
round435NoOrbitDivisionOrCardinalityFactorIntroducedIsTrue = refl

round435ArbitraryPhysicalTrajectoryAllInnerHelicalWeldClosedIsFalse :
  round435ArbitraryPhysicalTrajectoryAllInnerHelicalWeldClosed ≡ false
round435ArbitraryPhysicalTrajectoryAllInnerHelicalWeldClosedIsFalse = refl

round435R294WeightedCommutatorSameObjectWeldClosedIsFalse :
  round435R294WeightedCommutatorSameObjectWeldClosed ≡ false
round435R294WeightedCommutatorSameObjectWeldClosedIsFalse = refl

round435R423SignedCompanionBudgetClosedIsFalse :
  round435R423SignedCompanionBudgetClosed ≡ false
round435R423SignedCompanionBudgetClosedIsFalse = refl
