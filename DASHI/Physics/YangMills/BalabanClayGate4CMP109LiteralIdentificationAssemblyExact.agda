module DASHI.Physics.YangMills.BalabanClayGate4CMP109LiteralIdentificationAssemblyExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingLocalityExact as Locality
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalAveragingConventionSelectionExact as Convention
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as PrincipalLog

------------------------------------------------------------------------
-- Unified CMP 109 literal-identification witness.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The purpose of this module is to prevent the seven physical identifications
-- from drifting apart.  A single witness owns the literal map, endpoint support,
-- derivative, principal-log interpretation and physical normalization.  Once
-- inhabited, it produces the repository's official CMP 109 convention meaning.
------------------------------------------------------------------------

data Empty : Set where

Not : Set → Set
Not proposition = proposition → Empty

record ProjectedEndpointLocality
    (Input Output FineBond CoarseBond Value : Set) : Set₁ where
  field
    stage : Locality.LocalAveragingStage
      Input Output FineBond CoarseBond Value

    ProjectedEndpointSupport : CoarseBond → FineBond → Set

    supportMatchesProjectedEndpoints : ∀ coarse fine →
      Locality.Support stage coarse fine
      ≡ ProjectedEndpointSupport coarse fine

open ProjectedEndpointLocality public

localDependenceOnProjectedEndpoints :
  ∀ {Input Output FineBond CoarseBond Value}
    (meaning : ProjectedEndpointLocality
      Input Output FineBond CoarseBond Value)
    (left right : Input) coarse →
  (∀ fine → ProjectedEndpointSupport meaning coarse fine →
    Locality.inputValue (stage meaning) left fine
    ≡ Locality.inputValue (stage meaning) right fine) →
  Locality.outputValue (stage meaning)
      (Locality.average (stage meaning) left) coarse
  ≡ Locality.outputValue (stage meaning)
      (Locality.average (stage meaning) right) coarse
localDependenceOnProjectedEndpoints meaning left right coarse agreement =
  Locality.localDependence (stage meaning) left right coarse
    (λ fine stageSupport →
      agreement fine
        (subst
          (λ proposition → proposition)
          (supportMatchesProjectedEndpoints meaning coarse fine)
          stageSupport))

record CMP109LiteralIdentification
    (Input Output FineBond CoarseBond Value Lie Group Radius Entry
      Normalization : Set) : Set₁ where
  field
    oneStepFormula : Locality.BalabanPrimaryOneStepFormula
      Input Output FineBond CoarseBond Value Lie

    projectedLocality : ProjectedEndpointLocality
      Input Output FineBond CoarseBond Value

    formulaStageMatchesLocality :
      Locality.localStage oneStepFormula ≡ stage projectedLocality

    principalLogMeaning : PrincipalLog.PhysicalSU2PrincipalLogMeaning
      Input CoarseBond FineBond Lie Group Radius

    derivativeEntry : CoarseBond → FineBond → Entry
    zeroDerivativeEntry : Entry

    derivativeVanishesOutsideProjectedSupport : ∀ coarse fine →
      Not (ProjectedEndpointSupport projectedLocality coarse fine) →
      derivativeEntry coarse fine ≡ zeroDerivativeEntry

    physicalNormalization : Normalization

    LiteralMapMatchesCMP109 : (Input → Output) → Set
    DerivativeMatchesCMP109 :
      (CoarseBond → FineBond → Entry) → Set
    SupportMatchesCMP109 :
      (CoarseBond → FineBond → Set) → Set
    NormalizationMatchesCMP109 : Normalization → Set

    literalMapMatchesCMP109 :
      LiteralMapMatchesCMP109
        (Locality.average (Locality.localStage oneStepFormula))

    derivativeMatchesCMP109 :
      DerivativeMatchesCMP109 derivativeEntry

    supportMatchesCMP109 :
      SupportMatchesCMP109
        (ProjectedEndpointSupport projectedLocality)

    normalizationMatchesCMP109 :
      NormalizationMatchesCMP109 physicalNormalization

open CMP109LiteralIdentification public

asGate4CMP109PhysicalMeaning :
  ∀ {Input Output FineBond CoarseBond Value Lie Group Radius Entry
      Normalization}
    (meaning : CMP109LiteralIdentification
      Input Output FineBond CoarseBond Value Lie Group Radius Entry
      Normalization) →
  Convention.Gate4CMP109PhysicalMeaning
    (Input → Output)
    (CoarseBond → FineBond → Entry)
    (CoarseBond → FineBond → Set)
    Normalization
asGate4CMP109PhysicalMeaning meaning = let open Convention.Gate4CMP109PhysicalMeaning in record
  { LiteralMapMatchesCMP109 =
      LiteralMapMatchesCMP109 meaning
  ; DerivativeMatchesCMP109 =
      DerivativeMatchesCMP109 meaning
  ; SupportMatchesCMP109 =
      SupportMatchesCMP109 meaning
  ; NormalizationMatchesCMP109 =
      NormalizationMatchesCMP109 meaning
  ; physicalLiteralMap =
      Locality.average (Locality.localStage (oneStepFormula meaning))
  ; physicalDerivative =
      derivativeEntry meaning
  ; physicalSupport =
      ProjectedEndpointSupport (projectedLocality meaning)
  ; physicalNormalization =
      physicalNormalization meaning
  ; literalMapMatchesCMP109 =
      literalMapMatchesCMP109 meaning
  ; derivativeMatchesCMP109 =
      derivativeMatchesCMP109 meaning
  ; supportMatchesCMP109 =
      supportMatchesCMP109 meaning
  ; normalizationMatchesCMP109 =
      normalizationMatchesCMP109 meaning
  }

cmp109ProjectedLocalityTransportLevel : ProofLevel
cmp109ProjectedLocalityTransportLevel = machineChecked

cmp109UnifiedLiteralIdentificationAssemblyLevel : ProofLevel
cmp109UnifiedLiteralIdentificationAssemblyLevel = machineChecked

physicalCMP109OneStepFormulaInputsLevel : ProofLevel
physicalCMP109OneStepFormulaInputsLevel = conditional

physicalCMP109PrincipalLogMeaningInputsLevel : ProofLevel
physicalCMP109PrincipalLogMeaningInputsLevel = conditional

physicalCMP109FrechetDerivativeIdentificationInputsLevel : ProofLevel
physicalCMP109FrechetDerivativeIdentificationInputsLevel = conditional

physicalCMP109UnifiedNormalizationInputsLevel : ProofLevel
physicalCMP109UnifiedNormalizationInputsLevel = conditional
