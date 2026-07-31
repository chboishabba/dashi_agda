module DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingLocalityExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingDimensionAuditExact as Dimension

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Balaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Equations (42)--(43) define the one-step and iterated averaging operations.
-- Directly after (43), the paper states that the kth averaged bond depends only
-- on the bond variables in B^k(c_-) union B^k(c_+). The theorem below isolates
-- the finite logical content: locality is closed under composition, and the
-- support relation of a composition is relational composition of supports.
------------------------------------------------------------------------

record LocalAveragingStage
    (Input Output InputSite OutputSite Value : Set) : Set₁ where
  field
    inputValue : Input → InputSite → Value
    outputValue : Output → OutputSite → Value
    average : Input → Output
    Support : OutputSite → InputSite → Set

    localDependence :
      ∀ (left right : Input) (outputSite : OutputSite) →
      (∀ (inputSite : InputSite) →
        Support outputSite inputSite →
        inputValue left inputSite ≡ inputValue right inputSite) →
      outputValue (average left) outputSite
      ≡ outputValue (average right) outputSite

open LocalAveragingStage public

data ComposedSupport
    {Input Middle Coarse InputSite MiddleSite CoarseSite Value : Set}
    (first : LocalAveragingStage
      Input Middle InputSite MiddleSite Value)
    (second : LocalAveragingStage
      Middle Coarse MiddleSite CoarseSite Value)
    (coarseSite : CoarseSite) : InputSite → Set where
  through : ∀ (middleSite : MiddleSite) {inputSite : InputSite} →
    Support second coarseSite middleSite →
    Support first middleSite inputSite →
    ComposedSupport first second coarseSite inputSite

record ComposableLocalAveraging
    (Input Middle Coarse InputSite MiddleSite CoarseSite Value : Set) : Set₁ where
  field
    first : LocalAveragingStage
      Input Middle InputSite MiddleSite Value
    second : LocalAveragingStage
      Middle Coarse MiddleSite CoarseSite Value

    middleValueCompatibility :
      ∀ (middle : Middle) (site : MiddleSite) →
      outputValue first middle site ≡ inputValue second middle site

open ComposableLocalAveraging public

composedLocalDependence :
  ∀ {Input Middle Coarse InputSite MiddleSite CoarseSite Value : Set}
    (dataSet : ComposableLocalAveraging
      Input Middle Coarse InputSite MiddleSite CoarseSite Value)
    (left right : Input)
    (coarseSite : CoarseSite) →
  (∀ (inputSite : InputSite) →
    ComposedSupport (first dataSet) (second dataSet)
      coarseSite inputSite →
    inputValue (first dataSet) left inputSite
    ≡ inputValue (first dataSet) right inputSite) →
  outputValue (second dataSet)
    (average (second dataSet) (average (first dataSet) left)) coarseSite
  ≡ outputValue (second dataSet)
      (average (second dataSet) (average (first dataSet) right)) coarseSite
composedLocalDependence dataSet left right coarseSite fineAgreement =
  localDependence (second dataSet)
    (average (first dataSet) left)
    (average (first dataSet) right)
    coarseSite
    (λ middleSite secondSupport →
      trans
        (sym (middleValueCompatibility dataSet
          (average (first dataSet) left) middleSite))
        (trans
          (localDependence (first dataSet) left right middleSite
            (λ inputSite firstSupport →
              fineAgreement inputSite
                (through middleSite secondSupport firstSupport)))
          (middleValueCompatibility dataSet
            (average (first dataSet) right) middleSite)))

composeLocalAveragingStage :
  ∀ {Input Middle Coarse InputSite MiddleSite CoarseSite Value : Set} →
  ComposableLocalAveraging
    Input Middle Coarse InputSite MiddleSite CoarseSite Value →
  LocalAveragingStage Input Coarse InputSite CoarseSite Value
composeLocalAveragingStage dataSet = record
  { inputValue = inputValue (first dataSet)
  ; outputValue = outputValue (second dataSet)
  ; average = λ input → average (second dataSet) (average (first dataSet) input)
  ; Support = ComposedSupport (first dataSet) (second dataSet)
  ; localDependence = composedLocalDependence dataSet
  }

record BalabanPrimaryOneStepFormula
    (Input Output InputSite OutputSite Value Lie : Set) : Set₁ where
  field
    localStage : LocalAveragingStage
      Input Output InputSite OutputSite Value

    transportedLog : Input → OutputSite → InputSite → Lie
    weightedLocalLogSum : Input → OutputSite → Lie
    exponential : Lie → Value
    multiply : Value → Value → Value
    endpointValue : Input → OutputSite → Value

    primaryFormula : ∀ (input : Input) (outputSite : OutputSite) →
      outputValue localStage (average localStage input) outputSite
      ≡ multiply
          (exponential (weightedLocalLogSum input outputSite))
          (endpointValue input outputSite)

    coefficientConvention : Dimension.AveragingExponentConvention
    coefficientConventionExact :
      coefficientConvention ≡ Dimension.volumeDimensionExponent

open BalabanPrimaryOneStepFormula public

primaryOneStepFormulaLevel : ProofLevel
primaryOneStepFormulaLevel = standardImported

localityClosedUnderCompositionLevel : ProofLevel
localityClosedUnderCompositionLevel = machineChecked

physicalAveragingFormulaIdentificationInputsLevel : ProofLevel
physicalAveragingFormulaIdentificationInputsLevel = conditional

physicalIteratedSupportEnumerationInputsLevel : ProofLevel
physicalIteratedSupportEnumerationInputsLevel = conditional
