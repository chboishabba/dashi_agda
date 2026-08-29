module DASHI.Physics.YangMills.YangMillsLocalCoreChargeLinearityExact where

------------------------------------------------------------------------
-- ROUND86: EVENTUALLY CONSTANT CUTOFF CHARGES -> ADDITIVE LOCAL-CORE OPERATOR
--
-- PRIMARY CALIBRATION
--
-- Manfred Requardt,
-- "Symmetry Conservation and Integrals over Local Charge Densities in Quantum
-- Field Theory", Communications in Mathematical Physics 50 (1976), 259--263.
-- DOI: 10.1007/BF01609406.
--
-- Giovanni Morchio and Franco Strocchi,
-- "Charge density and electric charge in quantum electrodynamics",
-- Journal of Mathematical Physics 44 (2003), 5569--5587.
-- DOI: 10.1063/1.1623928.  arXiv: hep-th/0301111.
--
-- PURPOSE
--
-- Round85 defines the local-core charge by eventual cutoff stabilization.  A
-- generator, however, must at minimum be an operator respecting the linear/core
-- structure.  No new Yang--Mills estimate is needed for ADDITIVITY once:
--
--   * every finite-cutoff charge is additive;
--   * any two local vectors and their sum fit inside one common cutoff;
--   * cutoff stabilization holds beyond support.
--
-- Evaluate all three vectors at that common cutoff, use finite-cutoff additivity,
-- and transport back to the limiting local-core actions.  This file proves that
-- compiler exactly.  Thus L6 should not retain "prove the limiting charge is
-- linear" as a separate analytic theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong; sym; trans)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsStressChargeLocalCoreCutoffStabilizationExact as Core

record AdditiveLocalCoreCutoffCharge
    {LocalVector Target : Set}
    (dataSet : Core.LocalCoreCutoffCharge LocalVector Target) : Set₁ where
  field
    zeroVector : LocalVector
    _+v_ : LocalVector → LocalVector → LocalVector

    zeroTarget : Target
    _+t_ : Target → Target → Target

    finiteChargeZero : ∀ cutoff →
      Core.cutoffChargeAction dataSet cutoff zeroVector ≡ zeroTarget

    finiteChargeAdditive : ∀ cutoff left right →
      Core.cutoffChargeAction dataSet cutoff (left +v right)
      ≡ Core.cutoffChargeAction dataSet cutoff left
        +t Core.cutoffChargeAction dataSet cutoff right

    -- A common finite region containing left, right and left+right.  In the
    -- physical local algebra this should come from finite support geometry.
    commonCutoff : LocalVector → LocalVector → Nat
    leftInsideCommon : ∀ left right →
      Core.supportRadius dataSet left ≤ commonCutoff left right
    rightInsideCommon : ∀ left right →
      Core.supportRadius dataSet right ≤ commonCutoff left right
    sumInsideCommon : ∀ left right →
      Core.supportRadius dataSet (left +v right) ≤ commonCutoff left right

open AdditiveLocalCoreCutoffCharge public

limitingChargeZero :
  ∀ {LocalVector Target}
    {dataSet : Core.LocalCoreCutoffCharge LocalVector Target}
    (additive : AdditiveLocalCoreCutoffCharge dataSet) →
  Core.localCoreChargeAction dataSet (zeroVector additive)
  ≡ zeroTarget additive
limitingChargeZero {dataSet = dataSet} additive =
  finiteChargeZero additive (Core.supportRadius dataSet (zeroVector additive))

limitingChargeAdditive :
  ∀ {LocalVector Target}
    {dataSet : Core.LocalCoreCutoffCharge LocalVector Target}
    (additive : AdditiveLocalCoreCutoffCharge dataSet)
    left right →
  Core.localCoreChargeAction dataSet (_+v_ additive left right)
  ≡ _+t_ additive
      (Core.localCoreChargeAction dataSet left)
      (Core.localCoreChargeAction dataSet right)
limitingChargeAdditive {dataSet = dataSet} additive left right =
  let
    cutoff = commonCutoff additive left right

    sumAtCommonEqualsLimit :
      Core.cutoffChargeAction dataSet cutoff (_+v_ additive left right)
      ≡ Core.localCoreChargeAction dataSet (_+v_ additive left right)
    sumAtCommonEqualsLimit =
      Core.cutoffChargeEqualsLocalCoreChargeBeyondSupport dataSet
        (_+v_ additive left right) cutoff
        (sumInsideCommon additive left right)

    leftAtCommonEqualsLimit :
      Core.cutoffChargeAction dataSet cutoff left
      ≡ Core.localCoreChargeAction dataSet left
    leftAtCommonEqualsLimit =
      Core.cutoffChargeEqualsLocalCoreChargeBeyondSupport dataSet left cutoff
        (leftInsideCommon additive left right)

    rightAtCommonEqualsLimit :
      Core.cutoffChargeAction dataSet cutoff right
      ≡ Core.localCoreChargeAction dataSet right
    rightAtCommonEqualsLimit =
      Core.cutoffChargeEqualsLocalCoreChargeBeyondSupport dataSet right cutoff
        (rightInsideCommon additive left right)

    finiteAdd = finiteChargeAdditive additive cutoff left right
  in
  trans
    (sym sumAtCommonEqualsLimit)
    (trans
      finiteAdd
      (trans
        (cong
          (λ value → _+t_ additive value
            (Core.cutoffChargeAction dataSet cutoff right))
          leftAtCommonEqualsLimit)
        (cong
          (λ value → _+t_ additive
            (Core.localCoreChargeAction dataSet left) value)
          rightAtCommonEqualsLimit)))

record AdditiveLocalCoreChargeOperator
    {LocalVector Target : Set}
    {dataSet : Core.LocalCoreCutoffCharge LocalVector Target}
    (additive : AdditiveLocalCoreCutoffCharge dataSet) : Set₁ where
  field
    action : LocalVector → Target
    actionIsLimit : ∀ vector →
      action vector ≡ Core.localCoreChargeAction dataSet vector
    preservesZero : action (zeroVector additive) ≡ zeroTarget additive
    preservesAddition : ∀ left right →
      action (_+v_ additive left right)
      ≡ _+t_ additive (action left) (action right)

open AdditiveLocalCoreChargeOperator public

additiveLocalCoreChargeOperator :
  ∀ {LocalVector Target}
    {dataSet : Core.LocalCoreCutoffCharge LocalVector Target}
    (additive : AdditiveLocalCoreCutoffCharge dataSet) →
  AdditiveLocalCoreChargeOperator additive
additiveLocalCoreChargeOperator {dataSet = dataSet} additive = record
  { action = Core.localCoreChargeAction dataSet
  ; actionIsLimit = λ vector → refl
  ; preservesZero = limitingChargeZero additive
  ; preservesAddition = limitingChargeAdditive additive
  }

stabilizedChargeAdditivityCompilerLevel : ProofLevel
stabilizedChargeAdditivityCompilerLevel = machineChecked

-- Remaining physical input for this compiler is finite-cutoff charge additivity
-- and finite-support closure of the chosen local core.  Those are structurally
-- much weaker than a new continuum operator-limit estimate.
physicalFiniteCutoffChargeAdditivityAndCoreSupportLevel : ProofLevel
physicalFiniteCutoffChargeAdditivityAndCoreSupportLevel = conditional
