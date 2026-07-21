module DASHI.Physics.YangMills.BalabanFiniteFourierHodgeReduction where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Concrete dependency reduction for the flat reference Hodge estimate.
--
-- This module does not assert a spectral gap.  It proves that an exact finite
-- Fourier diagonalization, Parseval identity, constrained symbol-gap theorem
-- and uniform positive constant imply the repository bulk Hodge--Poincaré
-- estimate.  The remaining analytic/arithmetic work is therefore isolated to
-- the literal Fourier and symbol lemmas rather than hidden in one opaque field.
------------------------------------------------------------------------

record FiniteFourierHodgeData
    (Index State Frequency Bound : Set) : Set₁ where
  field
    fourier : State → Frequency

    referenceEnergy : Index → State → Bound
    normSq : State → Bound
    frequencyNormSq : Frequency → Bound
    symbolEnergy : Index → Frequency → Bound

    scale : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    Positive Nonnegative : Bound → Set

    cBulk : Bound
    cBulkPositive : Positive cBulk

    GaugeFixedTangent : Index → State → Set
    SymbolKernel : Index → Frequency → Set
    ConstantMode : Frequency → Set
    SymbolKernelRemoved : Index → Frequency → Set

    finiteFourierDiagonalizesReferenceLaplacian : ∀ index state →
      referenceEnergy index state ≡ symbolEnergy index (fourier state)

    fourierParsevalForBondFields : ∀ state →
      normSq state ≡ frequencyNormSq (fourier state)

    referenceSymbolNonnegative : ∀ index frequency →
      Nonnegative (symbolEnergy index frequency)

    referenceSymbolKernelCharacterization : ∀ index frequency →
      SymbolKernel index frequency → ConstantMode frequency

    constraintsRemoveReferenceSymbolKernel : ∀ index state →
      GaugeFixedTangent index state →
      SymbolKernelRemoved index (fourier state)

    constrainedReferenceSymbolHasPositiveGap : ∀ index frequency →
      SymbolKernelRemoved index frequency →
      LessEqual
        (scale cBulk (frequencyNormSq frequency))
        (symbolEnergy index frequency)

    CBulkIndependentOfVolume : Set
    CBulkIndependentOfLatticeSpacing : Set
    CBulkIndependentOfScale : Set
    CBulkUniformOverAdmissibleBackgrounds : Set

    cBulkIndependentOfVolume : CBulkIndependentOfVolume
    cBulkIndependentOfLatticeSpacing :
      CBulkIndependentOfLatticeSpacing
    cBulkIndependentOfScale : CBulkIndependentOfScale
    cBulkUniformOverAdmissibleBackgrounds :
      CBulkUniformOverAdmissibleBackgrounds

open FiniteFourierHodgeData public

symbolGapImpliesBulkHodgePoincare :
  ∀ {Index State Frequency Bound}
  (dataSet : FiniteFourierHodgeData Index State Frequency Bound) →
  ∀ index state →
  GaugeFixedTangent dataSet index state →
  LessEqual dataSet
    (scale dataSet (cBulk dataSet) (normSq dataSet state))
    (referenceEnergy dataSet index state)
symbolGapImpliesBulkHodgePoincare dataSet index state tangent
  rewrite fourierParsevalForBondFields dataSet state
        | finiteFourierDiagonalizesReferenceLaplacian dataSet index state =
  constrainedReferenceSymbolHasPositiveGap dataSet
    index
    (fourier dataSet state)
    (constraintsRemoveReferenceSymbolKernel dataSet index state tangent)

bulkGaugeFixedHodgePoincare :
  ∀ {Index State Frequency Bound}
  (dataSet : FiniteFourierHodgeData Index State Frequency Bound) →
  ∀ index state →
  GaugeFixedTangent dataSet index state →
  LessEqual dataSet
    (scale dataSet (cBulk dataSet) (normSq dataSet state))
    (referenceEnergy dataSet index state)
bulkGaugeFixedHodgePoincare = symbolGapImpliesBulkHodgePoincare

record UniformBulkHodgeCertificate
    (Index State Bound : Set) : Set₁ where
  field
    referenceEnergy : Index → State → Bound
    normSq : State → Bound
    scale : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    Positive : Bound → Set
    GaugeFixedTangent : Index → State → Set
    cBulk : Bound
    cBulkPositive : Positive cBulk

    bulkGaugeFixedHodgePoincare : ∀ index state →
      GaugeFixedTangent index state →
      LessEqual (scale cBulk (normSq state))
        (referenceEnergy index state)

    CBulkIndependentOfVolume : Set
    CBulkIndependentOfLatticeSpacing : Set
    CBulkIndependentOfScale : Set
    CBulkUniformOverAdmissibleBackgrounds : Set

    cBulkIndependentOfVolume : CBulkIndependentOfVolume
    cBulkIndependentOfLatticeSpacing :
      CBulkIndependentOfLatticeSpacing
    cBulkIndependentOfScale : CBulkIndependentOfScale
    cBulkUniformOverAdmissibleBackgrounds :
      CBulkUniformOverAdmissibleBackgrounds

open UniformBulkHodgeCertificate public

finiteFourierHodgeCertificate :
  ∀ {Index State Frequency Bound} →
  (dataSet : FiniteFourierHodgeData Index State Frequency Bound) →
  UniformBulkHodgeCertificate Index State Bound
finiteFourierHodgeCertificate dataSet = record
  { referenceEnergy = referenceEnergy dataSet
  ; normSq = normSq dataSet
  ; scale = scale dataSet
  ; LessEqual = LessEqual dataSet
  ; Positive = Positive dataSet
  ; GaugeFixedTangent = GaugeFixedTangent dataSet
  ; cBulk = cBulk dataSet
  ; cBulkPositive = cBulkPositive dataSet
  ; bulkGaugeFixedHodgePoincare =
      symbolGapImpliesBulkHodgePoincare dataSet
  ; CBulkIndependentOfVolume = CBulkIndependentOfVolume dataSet
  ; CBulkIndependentOfLatticeSpacing =
      CBulkIndependentOfLatticeSpacing dataSet
  ; CBulkIndependentOfScale = CBulkIndependentOfScale dataSet
  ; CBulkUniformOverAdmissibleBackgrounds =
      CBulkUniformOverAdmissibleBackgrounds dataSet
  ; cBulkIndependentOfVolume = cBulkIndependentOfVolume dataSet
  ; cBulkIndependentOfLatticeSpacing =
      cBulkIndependentOfLatticeSpacing dataSet
  ; cBulkIndependentOfScale = cBulkIndependentOfScale dataSet
  ; cBulkUniformOverAdmissibleBackgrounds =
      cBulkUniformOverAdmissibleBackgrounds dataSet
  }

finiteFourierHodgeReductionAssemblyLevel : ProofLevel
finiteFourierHodgeReductionAssemblyLevel = machineChecked

finiteFourierAndSymbolGapInputLevel : ProofLevel
finiteFourierAndSymbolGapInputLevel = conditional
