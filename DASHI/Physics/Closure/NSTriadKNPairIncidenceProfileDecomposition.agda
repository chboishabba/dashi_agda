module DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; zero)

import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula as KernelFormula

------------------------------------------------------------------------
-- Theorem-facing surface for the Stage 3 profile decomposition.
--
-- This module does not claim the decomposition is proved. It exposes the
-- exact theorem shape needed to upgrade the receipt layer into a genuine
-- profile-wise analytic argument.

data PairIncidenceProfile : Set where
  forcedTailProfile : PairIncidenceProfile
  adversarialGeometryProfile : PairIncidenceProfile
  transitionProfile : PairIncidenceProfile
  residualProfile : PairIncidenceProfile

record NSTriadKNPairIncidenceProfileDecompositionModel
    {ℓS ℓE ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓV ⊔ ℓR)) where
  field
    Shell : Set ℓS
    Entry : Set ℓE
    Value : Set ℓV

    _≈_ : Value -> Value -> Set ℓR
    _+_ : Value -> Value -> Value
    0# : Value

    totalKernel : Shell -> Entry -> Entry -> Value
    profileKernel : PairIncidenceProfile -> Shell -> Entry -> Entry -> Value

    profileClassifier : Shell -> Entry -> Entry -> PairIncidenceProfile

    pointwiseProfileDecomposition :
      (N : Shell) -> (i j : Entry) ->
      _≈_ (totalKernel N i j)
        ((profileKernel forcedTailProfile N i j + profileKernel adversarialGeometryProfile N i j) +
         (profileKernel transitionProfile N i j + profileKernel residualProfile N i j))

    forcedTailClassifierSound :
      (N : Shell) -> (i j : Entry) ->
      profileClassifier N i j ≡ forcedTailProfile ->
      _≈_ (profileKernel adversarialGeometryProfile N i j) 0#

    adversarialClassifierSound :
      (N : Shell) -> (i j : Entry) ->
      profileClassifier N i j ≡ adversarialGeometryProfile ->
      _≈_ (profileKernel forcedTailProfile N i j) 0#

    transitionClassifierSound :
      (N : Shell) -> (i j : Entry) ->
      profileClassifier N i j ≡ transitionProfile ->
      _≈_ (profileKernel residualProfile N i j) 0#

    residualClassifierSound :
      (N : Shell) -> (i j : Entry) ->
      profileClassifier N i j ≡ residualProfile ->
      _≈_ (profileKernel transitionProfile N i j) 0#

open NSTriadKNPairIncidenceProfileDecompositionModel public

forcedTailProfileKernel :
  ∀ {ℓS ℓE ℓV ℓR}
  (m : NSTriadKNPairIncidenceProfileDecompositionModel {ℓS} {ℓE} {ℓV} {ℓR}) ->
  Shell m -> Entry m -> Entry m -> Value m
forcedTailProfileKernel m =
  profileKernel m forcedTailProfile

adversarialProfileKernel :
  ∀ {ℓS ℓE ℓV ℓR}
  (m : NSTriadKNPairIncidenceProfileDecompositionModel {ℓS} {ℓE} {ℓV} {ℓR}) ->
  Shell m -> Entry m -> Entry m -> Value m
adversarialProfileKernel m =
  profileKernel m adversarialGeometryProfile

transitionProfileKernel :
  ∀ {ℓS ℓE ℓV ℓR}
  (m : NSTriadKNPairIncidenceProfileDecompositionModel {ℓS} {ℓE} {ℓV} {ℓR}) ->
  Shell m -> Entry m -> Entry m -> Value m
transitionProfileKernel m =
  profileKernel m transitionProfile

residualProfileKernel :
  ∀ {ℓS ℓE ℓV ℓR}
  (m : NSTriadKNPairIncidenceProfileDecompositionModel {ℓS} {ℓE} {ℓV} {ℓR}) ->
  Shell m -> Entry m -> Entry m -> Value m
residualProfileKernel m =
  profileKernel m residualProfile

------------------------------------------------------------------------
-- Upstream actual kernel-construction surface.
--
-- The profile-decomposition layer still exposes only total/profile kernels and
-- a label classifier. The next honest upstream export needed by the
-- cross-product matrix is the actual pair-incidence kernel together with its
-- profile classification on a concrete index set. That construction is itself
-- downstream of the repeated-pair kernel formula, so this gate must remain
-- fail-closed until the kernel-formula boundary exports typed data.

record ActualPairIncidenceKernelData
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkActualPairIncidenceKernelData
  field
    decompositionModel :
      NSTriadKNPairIncidenceProfileDecompositionModel
        {lzero} {lzero} {lzero} {lzero}

    shellAt :
      Shell decompositionModel

    Index : Set

    entryOf : Index → Entry decompositionModel

    actualKernel : Index → Index → Nat

    sourceProfile : Index → PairIncidenceProfile
    targetProfile : Index → PairIncidenceProfile

    kernelRealizesTotalKernel : Set

    kernelProfileClassification : Set

    sourceTargetProfilesLandInClassifier : Set

open ActualPairIncidenceKernelData public

UnitShellActualPairIncidenceKernelDataTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) → Set₁
UnitShellActualPairIncidenceKernelDataTarget residueNormModel =
  ActualPairIncidenceKernelData residueNormModel (suc zero)

actualPairIncidenceKernelDataClosed : Bool
actualPairIncidenceKernelDataClosed =
  KernelFormula.actualPairIncidenceKernelFormulaDataClosed

actualPairIncidenceKernelDataClosedIsFalse :
  actualPairIncidenceKernelDataClosed ≡ false
actualPairIncidenceKernelDataClosedIsFalse =
  KernelFormula.actualPairIncidenceKernelFormulaDataClosedIsFalse

actualUnitShellPairIncidenceKernelDataClosed : Bool
actualUnitShellPairIncidenceKernelDataClosed =
  KernelFormula.actualUnitShellPairIncidenceKernelFormulaDataClosed

actualUnitShellPairIncidenceKernelDataClosedIsFalse :
  actualUnitShellPairIncidenceKernelDataClosed ≡ false
actualUnitShellPairIncidenceKernelDataClosedIsFalse =
  KernelFormula.actualUnitShellPairIncidenceKernelFormulaDataClosedIsFalse
