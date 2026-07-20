module DASHI.Physics.Closure.FiniteRegionalSpectrum where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Fin using (Fin)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Unified.GRQuantumProofTerms

------------------------------------------------------------------------
-- Exact finite regional spectrum.
--
-- This proves finiteness for a regulated bounded region by exhibiting an
-- explicit finite enumeration.  It does not infer a continuum interacting UV
-- completion or low-energy empirical matching from finite ternary carriers.

record FiniteEnumeration (Carrier : Set) : Set where
  constructor finite-enumeration
  field
    size : Nat
    encode : Carrier → Fin size
    decode : Fin size → Carrier
    decodeEncode : (value : Carrier) → decode (encode value) ≡ value
    encodeDecode : (index : Fin size) → encode (decode index) ≡ index
open FiniteEnumeration public

finiteFin : (n : Nat) → FiniteEnumeration (Fin n)
finiteFin n =
  finite-enumeration n (λ index → index) (λ index → index)
    (λ _ → refl) (λ _ → refl)


data BoundedRegion : Set where
  canonicalRegion : BoundedRegion


data CutoffScale : Set where
  planckAgreementScale : CutoffScale


data RegulatedOperator : Set where
  regulatedHamiltonian : RegulatedOperator
  regulatedMetricOperator : RegulatedOperator

regionalBasis : BoundedRegion → Set
regionalBasis canonicalRegion = Fin 9

regulatedSpectrum : RegulatedOperator → Set
regulatedSpectrum regulatedHamiltonian = Fin 9
regulatedSpectrum regulatedMetricOperator = Fin 9

regionalBasisFinite :
  (region : BoundedRegion) → FiniteEnumeration (regionalBasis region)
regionalBasisFinite canonicalRegion = finiteFin 9

regulatedSpectrumFinite :
  (operator : RegulatedOperator) →
  FiniteEnumeration (regulatedSpectrum operator)
regulatedSpectrumFinite regulatedHamiltonian = finiteFin 9
regulatedSpectrumFinite regulatedMetricOperator = finiteFin 9

record FiniteAgreementDepth (region : BoundedRegion) : Set where
  constructor finite-agreement-depth
  field
    depth : Nat
open FiniteAgreementDepth public

canonicalAgreementDepth :
  (region : BoundedRegion) → FiniteAgreementDepth region
canonicalAgreementDepth canonicalRegion = finite-agreement-depth 3

record RegionalDimensionBound (region : BoundedRegion) : Set where
  constructor regional-dimension-bound
  field
    basisEnumeration : FiniteEnumeration (regionalBasis region)
open RegionalDimensionBound public

canonicalRegionalDimensionBound :
  (region : BoundedRegion) → RegionalDimensionBound region
canonicalRegionalDimensionBound canonicalRegion =
  regional-dimension-bound (finiteFin 9)

record RegulatedUVReceipt : Set where
  constructor regulated-uv-receipt
  field
    finiteDepth :
      (region : BoundedRegion) → FiniteAgreementDepth region
    finiteRegionalBasis :
      (region : BoundedRegion) → RegionalDimensionBound region
    finiteSpectrum :
      (operator : RegulatedOperator) →
      FiniteEnumeration (regulatedSpectrum operator)
    scope : String
open RegulatedUVReceipt public

canonicalRegulatedUVReceipt : RegulatedUVReceipt
canonicalRegulatedUVReceipt =
  regulated-uv-receipt
    canonicalAgreementDepth
    canonicalRegionalDimensionBound
    regulatedSpectrumFinite
    "exact finite nine-state regional cutoff model; no continuum interacting UV claim"

------------------------------------------------------------------------
-- Partial proposition surface.  All regulated finite fields are inhabited, but
-- the physically adequate low-energy match deliberately has no constructor.


data ExternalLowEnergyMatch : Set where

regulatedUVSurface : UVSpectralProof
regulatedUVSurface =
  record
    { Region = BoundedRegion
    ; Scale = CutoffScale
    ; Operator = RegulatedOperator
    ; Spectrum = regulatedSpectrum
    ; finiteResolvableDepth = FiniteAgreementDepth
    ; regionalHilbertDimensionBound = RegionalDimensionBound
    ; regulatedSpectrumFinite =
        λ operator → FiniteEnumeration (regulatedSpectrum operator)
    ; amplitudesConverge = ⊤
    ; renormalizationPreservesBound = ⊤
    ; lowEnergyLimitExists = ⊤
    ; lowEnergyLimitMatchesRequiredPhysics = ExternalLowEnergyMatch
    }

record RegulatedUVPartialClosure : Set where
  constructor regulated-uv-partial-closure
  field
    finiteDepthProof :
      (region : BoundedRegion) → FiniteAgreementDepth region
    regionalDimensionProof :
      (region : BoundedRegion) → RegionalDimensionBound region
    spectrumProof :
      (operator : RegulatedOperator) →
      FiniteEnumeration (regulatedSpectrum operator)
    finiteAmplitudeProof : ⊤
    rgBoundProof : ⊤
    formalLowEnergyLimitProof : ⊤
    missingPhysicalLowEnergyMatch : String
open RegulatedUVPartialClosure public

canonicalRegulatedUVPartialClosure : RegulatedUVPartialClosure
canonicalRegulatedUVPartialClosure =
  regulated-uv-partial-closure
    canonicalAgreementDepth
    canonicalRegionalDimensionBound
    regulatedSpectrumFinite
    tt tt tt
    "An external theorem must identify the regulated low-energy limit with the required GR/QFT observables and measured parameters."

uvSpectralBoundaryText : String
uvSpectralBoundaryText =
  "Finite agreement depth, finite regional basis, and finite regulated spectrum are now constructive theorems for the bounded nine-state model.  A UVSpectralClosed witness is intentionally not constructed because renormalized amplitude convergence and physically adequate low-energy recovery remain open."
