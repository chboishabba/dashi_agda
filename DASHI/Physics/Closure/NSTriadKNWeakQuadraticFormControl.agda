module DASHI.Physics.Closure.NSTriadKNWeakQuadraticFormControl where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (+-identityʳ)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceCNTheorem as CNTheorem
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNWeakOperatorErrorModel as WeakError

------------------------------------------------------------------------
-- Weak quadratic-form control surface.
--
-- This makes the remaining Blocker 2 theorem explicit:
--
--   PairIncidence C/N
--     => N * weakQuadraticForm_N(x) <= C * weakNormSquared_N(x)
--
-- The weak operator error model should be derived from an actual quadratic
-- form or from a proved model bound dominating that form.
--
-- Current honest frontier:
--   1. identify `actualWeakQuadraticForm` with the pair-incidence quadratic
--      form (or prove it is bounded by that form);
--   2. prove the operator norm controls that quadratic form;
--   3. feed the result into the existing weak->strong N^-2 composition lane.

record PairIncidenceQuadraticFormData
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkPairIncidenceQuadraticFormData
  field
    pairIncidenceOperator :
      ResidueNorm.Carrier residueNormModel shellIndex →
      ResidueNorm.Carrier residueNormModel shellIndex

    absWeakPairing :
      ResidueNorm.Carrier residueNormModel shellIndex →
      ResidueNorm.Carrier residueNormModel shellIndex →
      Nat

    AbsPairIncidenceQuadraticForm :
      ResidueNorm.Carrier residueNormModel shellIndex → Nat

    weakQuadraticFormConstant : Nat

    quadraticFormDefinition :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) →
      AbsPairIncidenceQuadraticForm x
        ≡
        absWeakPairing (pairIncidenceOperator x) x

    operatorNormQuadraticFormBound :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) →
      AbsPairIncidenceQuadraticForm x
        ≤
        weakQuadraticFormConstant
          * ResidueNorm.weakNormSquared residueNormModel shellIndex x

open PairIncidenceQuadraticFormData public
  renaming
    ( pairIncidenceOperator to pairIncidenceOperatorData
    ; absWeakPairing to absWeakPairingData
    ; AbsPairIncidenceQuadraticForm to AbsPairIncidenceQuadraticFormData
    ; weakQuadraticFormConstant to weakQuadraticFormConstantData
    ; quadraticFormDefinition to quadraticFormDefinitionData
    ; operatorNormQuadraticFormBound to operatorNormQuadraticFormBoundData
    )

fromPairIncidenceOperatorWitness :
  {residueNormModel : ResidueNorm.ResidueNormModel} →
  {shellIndex : Nat} →
  CNTheorem.PairIncidenceOperatorWitness residueNormModel shellIndex →
  PairIncidenceQuadraticFormData residueNormModel shellIndex
fromPairIncidenceOperatorWitness witness =
  mkPairIncidenceQuadraticFormData
    (CNTheorem.PairIncidenceOperatorWitness.pairIncidenceOperator witness)
    (CNTheorem.PairIncidenceOperatorWitness.absWeakPairing witness)
    (CNTheorem.PairIncidenceOperatorWitness.absQuadraticForm witness)
    (CNTheorem.PairIncidenceOperatorWitness.weakQuadraticFormConstant witness)
    (CNTheorem.PairIncidenceOperatorWitness.absQuadraticFormDef witness)
    (CNTheorem.PairIncidenceOperatorWitness.operatorNormControlsQuadratic witness)

fromStage3PairIncidenceOperatorWitness :
  {residueNormModel : ResidueNorm.ResidueNormModel} →
  {shellIndex : Nat} →
  CNTheorem.Stage3PairIncidenceOperatorWitness residueNormModel shellIndex →
  PairIncidenceQuadraticFormData residueNormModel shellIndex
fromStage3PairIncidenceOperatorWitness witness =
  fromPairIncidenceOperatorWitness
    (CNTheorem.stage3ToPairIncidenceOperatorWitness witness)

record WeakQuadraticFormControlTarget : Set₁ where
  constructor mkWeakQuadraticFormControlTarget
  field
    residueNormModel : ResidueNorm.ResidueNormModel
    shellIndex : Nat

    pairIncidenceCNWitness :
      CNTheorem.pairIncidenceCNTheoremClosed ≡ true

    actualWeakQuadraticForm :
      ResidueNorm.Carrier residueNormModel shellIndex → Nat

    AbsPairIncidenceQuadraticForm :
      ResidueNorm.Carrier residueNormModel shellIndex → Nat

    weakQuadraticFormConstant : Nat

    actualWeakQuadraticFormIsPairIncidenceForm :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) →
      actualWeakQuadraticForm x ≡ AbsPairIncidenceQuadraticForm x

    operatorNormQuadraticFormBound :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) →
      AbsPairIncidenceQuadraticForm x
        ≤
        weakQuadraticFormConstant
          * ResidueNorm.weakNormSquared residueNormModel shellIndex x

    pairIncidenceCNToWeakQuadraticCN :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) →
      shellIndex * actualWeakQuadraticForm x
        ≤
        weakQuadraticFormConstant
          * ResidueNorm.weakNormSquared residueNormModel shellIndex x

    targetClosed : Bool

weakQuadraticFormCarrier :
  (target : WeakQuadraticFormControlTarget) → Set
weakQuadraticFormCarrier target =
  ResidueNorm.Carrier
    (WeakQuadraticFormControlTarget.residueNormModel target)
    (WeakQuadraticFormControlTarget.shellIndex target)

operatorNormControlsWeakQuadraticFormTarget :
  (target : WeakQuadraticFormControlTarget) → Set
operatorNormControlsWeakQuadraticFormTarget target =
  (x : weakQuadraticFormCarrier target) →
  WeakQuadraticFormControlTarget.shellIndex target
    * WeakQuadraticFormControlTarget.actualWeakQuadraticForm target x
    ≤
    WeakQuadraticFormControlTarget.weakQuadraticFormConstant target
      *
      ResidueNorm.weakNormSquared
        (WeakQuadraticFormControlTarget.residueNormModel target)
        (WeakQuadraticFormControlTarget.shellIndex target)
        x

operatorNormControlsWeakQuadraticForm :
  (target : WeakQuadraticFormControlTarget) → Set
operatorNormControlsWeakQuadraticForm =
  operatorNormControlsWeakQuadraticFormTarget

actualWeakQuadraticFormIsPairIncidenceForm :
  (target : WeakQuadraticFormControlTarget) → Set
actualWeakQuadraticFormIsPairIncidenceForm target =
  (x : weakQuadraticFormCarrier target) →
  WeakQuadraticFormControlTarget.actualWeakQuadraticForm target x
    ≡
    WeakQuadraticFormControlTarget.AbsPairIncidenceQuadraticForm target x

operatorNormQuadraticFormBound :
  (target : WeakQuadraticFormControlTarget) → Set
operatorNormQuadraticFormBound target =
  (x : weakQuadraticFormCarrier target) →
  WeakQuadraticFormControlTarget.AbsPairIncidenceQuadraticForm target x
    ≤
    WeakQuadraticFormControlTarget.weakQuadraticFormConstant target
      *
      ResidueNorm.weakNormSquared
        (WeakQuadraticFormControlTarget.residueNormModel target)
        (WeakQuadraticFormControlTarget.shellIndex target)
        x

pairIncidenceCNToWeakQuadraticCN :
  (target : WeakQuadraticFormControlTarget) → Set
pairIncidenceCNToWeakQuadraticCN target =
  (x : weakQuadraticFormCarrier target) →
  WeakQuadraticFormControlTarget.shellIndex target
    * WeakQuadraticFormControlTarget.actualWeakQuadraticForm target x
    ≤
    WeakQuadraticFormControlTarget.weakQuadraticFormConstant target
      *
      ResidueNorm.weakNormSquared
        (WeakQuadraticFormControlTarget.residueNormModel target)
        (WeakQuadraticFormControlTarget.shellIndex target)
        x

toWeakOperatorErrorModelTarget :
  (target : WeakQuadraticFormControlTarget) →
  WeakError.WeakOperatorErrorModelTarget
toWeakOperatorErrorModelTarget target =
  WeakError.mkWeakOperatorErrorModelTarget
    (WeakQuadraticFormControlTarget.residueNormModel target)
    (WeakQuadraticFormControlTarget.shellIndex target)
    (WeakQuadraticFormControlTarget.pairIncidenceCNWitness target)
    (WeakQuadraticFormControlTarget.actualWeakQuadraticForm target)
    (WeakQuadraticFormControlTarget.weakQuadraticFormConstant target)
    (WeakQuadraticFormControlTarget.targetClosed target)

actualWeakQuadraticFormIsPairIncidenceFormFromData :
  {residueNormModel : ResidueNorm.ResidueNormModel} →
  {shellIndex : Nat} →
  (dataWitness :
    PairIncidenceQuadraticFormData residueNormModel shellIndex) →
  (actualWeakQuadraticForm :
    ResidueNorm.Carrier residueNormModel shellIndex → Nat) →
  ((x : ResidueNorm.Carrier residueNormModel shellIndex) →
    actualWeakQuadraticForm x
      ≡
      AbsPairIncidenceQuadraticFormData dataWitness x) →
  (x : ResidueNorm.Carrier residueNormModel shellIndex) →
  actualWeakQuadraticForm x
    ≡
    AbsPairIncidenceQuadraticFormData dataWitness x
actualWeakQuadraticFormIsPairIncidenceFormFromData
  dataWitness actualWeakQuadraticForm actualWeakQuadraticFormDefinition x =
  actualWeakQuadraticFormDefinition x

operatorNormQuadraticFormBoundFromData :
  {residueNormModel : ResidueNorm.ResidueNormModel} →
  {shellIndex : Nat} →
  (dataWitness :
    PairIncidenceQuadraticFormData residueNormModel shellIndex) →
  (x : ResidueNorm.Carrier residueNormModel shellIndex) →
  AbsPairIncidenceQuadraticFormData dataWitness x
    ≤
    weakQuadraticFormConstantData dataWitness
      * ResidueNorm.weakNormSquared residueNormModel shellIndex x
operatorNormQuadraticFormBoundFromData dataWitness =
  PairIncidenceQuadraticFormData.operatorNormQuadraticFormBound dataWitness

------------------------------------------------------------------------
-- Strict inhabitation helper at the live shell frontier.
--
-- The active NS consumer currently uses shellIndex = 1. At that shell, once
-- the actual weak quadratic form is identified with the pair-incidence form,
-- the operator-norm quadratic-form bound already has the exact CN shape. This
-- helper removes the last purely formal duplication: the remaining live proof
-- is the operator-norm quadratic-form bound itself, not a separate shell-1
-- arithmetic step.

pairIncidenceCNToWeakQuadraticCNAtUnitShell :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (actualWeakQuadraticForm
    AbsPairIncidenceQuadraticForm :
      ResidueNorm.Carrier residueNormModel (suc zero) → Nat) →
  (weakQuadraticFormConstant : Nat) →
  ((x : ResidueNorm.Carrier residueNormModel (suc zero)) →
    actualWeakQuadraticForm x ≡ AbsPairIncidenceQuadraticForm x) →
  ((x : ResidueNorm.Carrier residueNormModel (suc zero)) →
    AbsPairIncidenceQuadraticForm x
      ≤
      weakQuadraticFormConstant
        * ResidueNorm.weakNormSquared residueNormModel (suc zero) x) →
  (x : ResidueNorm.Carrier residueNormModel (suc zero)) →
  suc zero * actualWeakQuadraticForm x
    ≤
    weakQuadraticFormConstant
      * ResidueNorm.weakNormSquared residueNormModel (suc zero) x
pairIncidenceCNToWeakQuadraticCNAtUnitShell
  residueNormModel
  actualWeakQuadraticForm
  AbsPairIncidenceQuadraticForm
  weakQuadraticFormConstant
  actualWeakQuadraticFormIsPairIncidenceForm'
  operatorNormQuadraticFormBound'
  x
  rewrite actualWeakQuadraticFormIsPairIncidenceForm' x
        | +-identityʳ (AbsPairIncidenceQuadraticForm x) =
    operatorNormQuadraticFormBound' x

mkUnitShellWeakQuadraticFormControlTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (pairIncidenceCNWitness :
    CNTheorem.pairIncidenceCNTheoremClosed ≡ true) →
  (actualWeakQuadraticForm
    AbsPairIncidenceQuadraticForm :
      ResidueNorm.Carrier residueNormModel (suc zero) → Nat) →
  (weakQuadraticFormConstant : Nat) →
  ((x : ResidueNorm.Carrier residueNormModel (suc zero)) →
    actualWeakQuadraticForm x ≡ AbsPairIncidenceQuadraticForm x) →
  ((x : ResidueNorm.Carrier residueNormModel (suc zero)) →
    AbsPairIncidenceQuadraticForm x
      ≤
      weakQuadraticFormConstant
        * ResidueNorm.weakNormSquared residueNormModel (suc zero) x) →
  (targetClosed : Bool) →
  WeakQuadraticFormControlTarget
mkUnitShellWeakQuadraticFormControlTarget
  residueNormModel
  pairIncidenceCNWitness
  actualWeakQuadraticForm
  AbsPairIncidenceQuadraticForm
  weakQuadraticFormConstant
  actualWeakQuadraticFormIsPairIncidenceForm'
  operatorNormQuadraticFormBound'
  targetClosed =
  mkWeakQuadraticFormControlTarget
    residueNormModel
    (suc zero)
    pairIncidenceCNWitness
    actualWeakQuadraticForm
    AbsPairIncidenceQuadraticForm
    weakQuadraticFormConstant
    actualWeakQuadraticFormIsPairIncidenceForm'
    operatorNormQuadraticFormBound'
    (pairIncidenceCNToWeakQuadraticCNAtUnitShell
      residueNormModel
      actualWeakQuadraticForm
      AbsPairIncidenceQuadraticForm
      weakQuadraticFormConstant
      actualWeakQuadraticFormIsPairIncidenceForm'
      operatorNormQuadraticFormBound')
    targetClosed

mkUnitShellWeakQuadraticFormControlTargetFromData :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (pairIncidenceCNWitness :
    CNTheorem.pairIncidenceCNTheoremClosed ≡ true) →
  (dataWitness :
    PairIncidenceQuadraticFormData residueNormModel (suc zero)) →
  (actualWeakQuadraticForm :
    ResidueNorm.Carrier residueNormModel (suc zero) → Nat) →
  ((x : ResidueNorm.Carrier residueNormModel (suc zero)) →
    actualWeakQuadraticForm x
      ≡
      AbsPairIncidenceQuadraticFormData dataWitness x) →
  (targetClosed : Bool) →
  WeakQuadraticFormControlTarget
mkUnitShellWeakQuadraticFormControlTargetFromData
  residueNormModel
  pairIncidenceCNWitness
  dataWitness
  actualWeakQuadraticForm
  actualWeakQuadraticFormDefinition
  targetClosed =
  mkUnitShellWeakQuadraticFormControlTarget
    residueNormModel
    pairIncidenceCNWitness
    actualWeakQuadraticForm
    (AbsPairIncidenceQuadraticFormData dataWitness)
    (weakQuadraticFormConstantData dataWitness)
    (actualWeakQuadraticFormIsPairIncidenceFormFromData
      dataWitness
      actualWeakQuadraticForm
      actualWeakQuadraticFormDefinition)
    (operatorNormQuadraticFormBoundFromData dataWitness)
    targetClosed

mkUnitShellWeakQuadraticFormControlTargetFromWitness :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (operatorWitness :
    CNTheorem.PairIncidenceOperatorWitness residueNormModel (suc zero)) →
  (actualWeakQuadraticForm :
    ResidueNorm.Carrier residueNormModel (suc zero) → Nat) →
  ((x : ResidueNorm.Carrier residueNormModel (suc zero)) →
    actualWeakQuadraticForm x
      ≡
      CNTheorem.PairIncidenceOperatorWitness.absQuadraticForm operatorWitness x) →
  WeakQuadraticFormControlTarget
mkUnitShellWeakQuadraticFormControlTargetFromWitness
  residueNormModel
  operatorWitness
  actualWeakQuadraticForm
  actualWeakQuadraticFormDefinition =
  mkUnitShellWeakQuadraticFormControlTargetFromData
    residueNormModel
    (CNTheorem.PairIncidenceOperatorWitness.pairIncidenceCNWitness
      operatorWitness)
    (fromPairIncidenceOperatorWitness operatorWitness)
    actualWeakQuadraticForm
    actualWeakQuadraticFormDefinition
    (CNTheorem.PairIncidenceOperatorWitness.witnessClosed operatorWitness)

mkUnitShellWeakQuadraticFormControlTargetFromStage3Witness :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (operatorWitness :
    CNTheorem.Stage3PairIncidenceOperatorWitness residueNormModel (suc zero)) →
  (actualWeakQuadraticForm :
    ResidueNorm.Carrier residueNormModel (suc zero) → Nat) →
  ((x : ResidueNorm.Carrier residueNormModel (suc zero)) →
    actualWeakQuadraticForm x
      ≡
      CNTheorem.PairIncidenceOperatorWitness.absQuadraticForm
        (CNTheorem.stage3ToPairIncidenceOperatorWitness operatorWitness)
        x) →
  WeakQuadraticFormControlTarget
mkUnitShellWeakQuadraticFormControlTargetFromStage3Witness
  residueNormModel
  operatorWitness
  actualWeakQuadraticForm
  actualWeakQuadraticFormDefinition =
  mkUnitShellWeakQuadraticFormControlTargetFromWitness
    residueNormModel
    (CNTheorem.stage3ToPairIncidenceOperatorWitness operatorWitness)
    actualWeakQuadraticForm
    actualWeakQuadraticFormDefinition
