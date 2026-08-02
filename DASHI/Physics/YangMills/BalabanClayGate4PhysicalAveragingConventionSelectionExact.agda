module DASHI.Physics.YangMills.BalabanClayGate4PhysicalAveragingConventionSelectionExact where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingDimensionAuditExact as Primary

------------------------------------------------------------------------
-- Gate-4 physical convention selection.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Gate 4 is the four-dimensional small-field RG programme, so its physical
-- target convention is fixed to the CMP 109 Euclidean-symmetric average.  This
-- is a specification choice, not a proof that an existing repository map
-- already implements the CMP 109 equations.  Literal map, derivative, support
-- and normalization matching remain proof-bearing fields below.
--
-- The CMP 98 average remains primary authority for its own locality and kernel
-- estimates.  Reusing such an estimate for the CMP 109 target requires an
-- explicit convention bridge; chronology or dimensional analogy is not enough.
------------------------------------------------------------------------

record Both (left right : Set) : Set where
  constructor both
  field
    firstWitness : left
    secondWitness : right

open Both public

gate4PhysicalAveragingConvention : Primary.AveragingOperatorConvention
gate4PhysicalAveragingConvention =
  Primary.cmp109EuclideanSymmetricAverage

gate4PhysicalAveragingConventionIsCMP109 :
  gate4PhysicalAveragingConvention
  ≡ Primary.cmp109EuclideanSymmetricAverage
gate4PhysicalAveragingConventionIsCMP109 = refl

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

record Gate4CMP109PhysicalMeaning
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
    (LiteralMap : Set ℓ₁) (Derivative : Set ℓ₂)
    (Support : Set ℓ₃) (Normalization : Set ℓ₄) : Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
  field
    LiteralMapMatchesCMP109 : LiteralMap → Set
    DerivativeMatchesCMP109 : Derivative → Set
    SupportMatchesCMP109 : Support → Set
    NormalizationMatchesCMP109 : Normalization → Set

    physicalLiteralMap : LiteralMap
    physicalDerivative : Derivative
    physicalSupport : Support
    physicalNormalization : Normalization

    literalMapMatchesCMP109 :
      LiteralMapMatchesCMP109 physicalLiteralMap
    derivativeMatchesCMP109 :
      DerivativeMatchesCMP109 physicalDerivative
    supportMatchesCMP109 :
      SupportMatchesCMP109 physicalSupport
    normalizationMatchesCMP109 :
      NormalizationMatchesCMP109 physicalNormalization

open Gate4CMP109PhysicalMeaning public

asPrimaryPhysicalAveragingConventionMeaning :
  ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {LiteralMap : Set ℓ₁} {Derivative : Set ℓ₂}
    {Support : Set ℓ₃} {Normalization : Set ℓ₄}
    (meaning : Gate4CMP109PhysicalMeaning
      LiteralMap Derivative Support Normalization) →
  Primary.PhysicalAveragingConventionMeaning
    LiteralMap Derivative Support Normalization
asPrimaryPhysicalAveragingConventionMeaning meaning = record
  { selectedConvention = gate4PhysicalAveragingConvention
  ; LiteralMapMatches = λ convention literalMap →
      Both
        (convention ≡ gate4PhysicalAveragingConvention)
        (LiteralMapMatchesCMP109 meaning literalMap)
  ; DerivativeMatches = λ convention derivative →
      Both
        (convention ≡ gate4PhysicalAveragingConvention)
        (DerivativeMatchesCMP109 meaning derivative)
  ; SupportMatches = λ convention support →
      Both
        (convention ≡ gate4PhysicalAveragingConvention)
        (SupportMatchesCMP109 meaning support)
  ; NormalizationMatches = λ convention normalization →
      Both
        (convention ≡ gate4PhysicalAveragingConvention)
        (NormalizationMatchesCMP109 meaning normalization)
  ; physicalLiteralMap = physicalLiteralMap meaning
  ; physicalDerivative = physicalDerivative meaning
  ; physicalSupport = physicalSupport meaning
  ; physicalNormalization = physicalNormalization meaning
  ; literalMapMatchesSelected =
      both refl (literalMapMatchesCMP109 meaning)
  ; derivativeMatchesSelected =
      both refl (derivativeMatchesCMP109 meaning)
  ; supportMatchesSelected =
      both refl (supportMatchesCMP109 meaning)
  ; normalizationMatchesSelected =
      both refl (normalizationMatchesCMP109 meaning)
  }

record CMP98ToCMP109KernelBridge
    (Kernel : Set) : Set₁ where
  field
    cmp98Kernel cmp109Kernel : Kernel
    CMP98KernelEstimateTransfers : Kernel → Kernel → Set
    cmp98EstimateTransfersToCMP109 :
      CMP98KernelEstimateTransfers cmp98Kernel cmp109Kernel

open CMP98ToCMP109KernelBridge public

gate4CMP109ConventionSelectionLevel : ProofLevel
gate4CMP109ConventionSelectionLevel = computed

gate4CMP109PhysicalMeaningAssemblyLevel : ProofLevel
gate4CMP109PhysicalMeaningAssemblyLevel = machineChecked

physicalCMP109LiteralMapInputsLevel : ProofLevel
physicalCMP109LiteralMapInputsLevel = conditional

physicalCMP109DerivativeInputsLevel : ProofLevel
physicalCMP109DerivativeInputsLevel = conditional

physicalCMP109SupportInputsLevel : ProofLevel
physicalCMP109SupportInputsLevel = conditional

physicalCMP109NormalizationInputsLevel : ProofLevel
physicalCMP109NormalizationInputsLevel = conditional

cmp98KernelEstimateTransferToCMP109InputsLevel : ProofLevel
cmp98KernelEstimateTransferToCMP109InputsLevel = conditional
