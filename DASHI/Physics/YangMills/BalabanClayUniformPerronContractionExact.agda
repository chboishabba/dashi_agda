module DASHI.Physics.YangMills.BalabanClayUniformPerronContractionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Hans Henrik Rugh,
-- "Cones and gauges in complex spaces: Spectral gaps and complex
-- Perron-Frobenius theory", Annals of Mathematics 171 (2010), 1707--1752.
-- DOI: 10.4007/annals.2010.171.1707.
--
-- DASHI CONTRIBUTION
--
-- Finite projective diameter at every finite volume is not a uniform diameter
-- bound.  Quantitative cone contraction requires one modulus shared by all
-- volumes/scales.  The diagonal countermodel below proves the distinction
-- without limits, classical choice, or numerical approximation.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

data Empty : Set where

infix 4 _≤ᴺ_
data _≤ᴺ_ : Nat → Nat → Set where
  zero≤ : ∀ {n} → zero ≤ᴺ n
  suc≤suc : ∀ {m n} → m ≤ᴺ n → suc m ≤ᴺ suc n

≤ᴺ-reflexive : ∀ n → n ≤ᴺ n
≤ᴺ-reflexive zero = zero≤
≤ᴺ-reflexive (suc n) = suc≤suc (≤ᴺ-reflexive n)

successorNotBelowSelf : ∀ n → suc n ≤ᴺ n → Empty
successorNotBelowSelf zero ()
successorNotBelowSelf (suc n) (suc≤suc proof) =
  successorNotBelowSelf n proof

finiteVolumeProjectiveDiameter : Nat → Nat
finiteVolumeProjectiveDiameter extent = extent

everyFiniteVolumeHasFiniteCertificate : ∀ extent →
  finiteVolumeProjectiveDiameter extent ≤ᴺ extent
everyFiniteVolumeHasFiniteCertificate extent = ≤ᴺ-reflexive extent

noUniformDiameterBound : ∀ proposedUniformBound →
  (∀ extent →
    finiteVolumeProjectiveDiameter extent ≤ᴺ proposedUniformBound) →
  Empty
noUniformDiameterBound proposedUniformBound allExtentsBounded =
  successorNotBelowSelf proposedUniformBound
    (allExtentsBounded (suc proposedUniformBound))

record UniformConeContractionCertificate
    (Stage Modulus : Set) : Set₁ where
  field
    projectiveDiameter : Stage → Modulus
    commonDiameterBound : Modulus
    DiameterAtMost : Modulus → Modulus → Set
    everyStageUsesCommonBound : ∀ stage →
      DiameterAtMost (projectiveDiameter stage) commonDiameterBound
    contractionCoefficient : Modulus
    UniformStrictlyBelowIdentity : Modulus → Set
    commonContractionStrict :
      UniformStrictlyBelowIdentity contractionCoefficient

open UniformConeContractionCertificate public

record PerStageStrictContraction
    (Stage Modulus : Set) : Set₁ where
  field
    stageCoefficient : Stage → Modulus
    StageStrictlyBelowIdentity : Modulus → Set
    eachStageStrict : ∀ stage →
      StageStrictlyBelowIdentity (stageCoefficient stage)

open PerStageStrictContraction public

-- This adapter is intentionally one-way.  A common certificate certainly
-- supplies per-stage strictness, but the converse requires the missing uniform
-- modulus theorem and is not defined.
uniformCertificateGivesPerStageStrictness :
  ∀ {Stage Modulus}
    (uniform : UniformConeContractionCertificate Stage Modulus) →
  PerStageStrictContraction Stage Modulus
uniformCertificateGivesPerStageStrictness uniform = record
  { stageCoefficient = λ stage → contractionCoefficient uniform
  ; StageStrictlyBelowIdentity = UniformStrictlyBelowIdentity uniform
  ; eachStageStrict = λ stage → commonContractionStrict uniform
  }

finiteButNotUniformDiameterCountermodelLevel : ProofLevel
finiteButNotUniformDiameterCountermodelLevel = machineChecked

uniformConeModulusInputsLevel : ProofLevel
uniformConeModulusInputsLevel = conditional
