module DASHI.Physics.YangMills.BalabanClayGate4FiniteROperationAndDecayAssemblyExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (_∈_)

import DASHI.Physics.YangMills.BalabanClayGate4TypedReuseAndFiniteGeometryExact as Typed

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban, "Large Field Renormalization. I. The Basic Step of the
-- R Operation", Communications in Mathematical Physics 122 (1989), 175--202.
-- DOI: 10.1007/BF01257412.
--
-- Tadeusz Bałaban, "Large Field Renormalization. II. Localization,
-- Exponentiation, and Bounds for the R Operation", Communications in
-- Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- Target locator pending primary-source verification:
-- equation (1.100), p. 388, for boundary-uniform R-polymer decay;
-- equation (1.69), p. 377, for the boundary-term estimate;
-- Theorem 1, p. 388, for inductive-parameter preservation.
--
-- Relationship: the list partition and R-expression construction below are
-- exact. Analytic locality, gauge covariance, common-domain and norm-decay
-- statements remain separate typed inhabitants.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Keep expression-intersection classes distinct from component classes.
------------------------------------------------------------------------

localizedExpressionPartition :
  ∀ {Term Region}
    (dataSet : Typed.SupportLargeFieldIntersection Term Region)
    term region →
  Typed.ClassifiedLocalizedTerm dataSet term region Typed.firstClass
  ⊎ Typed.ClassifiedLocalizedTerm dataSet term region Typed.secondClass
localizedExpressionPartition dataSet term region
  with Typed.classifyLocalizedTermExact dataSet term region
... | Typed.classifiedFirst notIntersects =
  inj₁ (Typed.classifiedFirst notIntersects)
... | Typed.classifiedSecond intersects =
  inj₂ (Typed.classifiedSecond intersects)

------------------------------------------------------------------------
-- Concrete finite R-operation pipeline.
------------------------------------------------------------------------

data ExpressionDisposition : Set where
  regularDisposition boundaryDisposition : ExpressionDisposition

sameDisposition : ExpressionDisposition → ExpressionDisposition → Bool
sameDisposition regularDisposition regularDisposition = true
sameDisposition regularDisposition boundaryDisposition = false
sameDisposition boundaryDisposition regularDisposition = false
sameDisposition boundaryDisposition boundaryDisposition = true

record FiniteROperationData
    (Scale Polymer BoundaryCondition Region Term LocalizedTerm BoundaryTerm
      RExpression : Set) : Set₁ where
  field
    sourceTerms : Scale → Polymer → BoundaryCondition → List Term
    regionOf : Scale → Polymer → Region
    intersection : Typed.SupportLargeFieldIntersection Term Region

    disposition : Typed.LocalizedClass → ExpressionDisposition
    localize : Scale → Polymer → Term → LocalizedTerm
    extractBoundary : Scale → Polymer → LocalizedTerm → BoundaryTerm
    exponentiateLocalized : Scale → Polymer → List LocalizedTerm → RExpression

open FiniteROperationData public

map : ∀ {A B : Set} → (A → B) → List A → List B
map function [] = []
map function (value ∷ values) = function value ∷ map function values

filterDisposition :
  ∀ {Scale Polymer BoundaryCondition Region Term LocalizedTerm BoundaryTerm
      RExpression}
    (dataSet : FiniteROperationData Scale Polymer BoundaryCondition Region Term
      LocalizedTerm BoundaryTerm RExpression) →
  ExpressionDisposition → Region → List Term → List Term
filterDisposition dataSet selected region [] = []
filterDisposition dataSet selected region (term ∷ terms)
  with sameDisposition selected
    (disposition dataSet
      (Typed.classifyLocalizedTerm (intersection dataSet) term region))
... | true = term ∷ filterDisposition dataSet selected region terms
... | false = filterDisposition dataSet selected region terms

regularTerms :
  ∀ {Scale Polymer BoundaryCondition Region Term LocalizedTerm BoundaryTerm
      RExpression}
    (dataSet : FiniteROperationData Scale Polymer BoundaryCondition Region Term
      LocalizedTerm BoundaryTerm RExpression) →
  Scale → Polymer → BoundaryCondition → List Term
regularTerms dataSet scale polymer boundary =
  filterDisposition dataSet regularDisposition
    (regionOf dataSet scale polymer)
    (sourceTerms dataSet scale polymer boundary)

boundarySourceTerms :
  ∀ {Scale Polymer BoundaryCondition Region Term LocalizedTerm BoundaryTerm
      RExpression}
    (dataSet : FiniteROperationData Scale Polymer BoundaryCondition Region Term
      LocalizedTerm BoundaryTerm RExpression) →
  Scale → Polymer → BoundaryCondition → List Term
boundarySourceTerms dataSet scale polymer boundary =
  filterDisposition dataSet boundaryDisposition
    (regionOf dataSet scale polymer)
    (sourceTerms dataSet scale polymer boundary)

record ROperationResult (RExpression BoundaryTerm : Set) : Set where
  constructor rResult
  field
    regularExpression : RExpression
    generatedBoundaryTerms : List BoundaryTerm

open ROperationResult public

runROperation :
  ∀ {Scale Polymer BoundaryCondition Region Term LocalizedTerm BoundaryTerm
      RExpression}
    (dataSet : FiniteROperationData Scale Polymer BoundaryCondition Region Term
      LocalizedTerm BoundaryTerm RExpression) →
  Scale → Polymer → BoundaryCondition → ROperationResult RExpression BoundaryTerm
runROperation dataSet scale polymer boundary =
  rResult
    (exponentiateLocalized dataSet scale polymer
      (map (localize dataSet scale polymer)
        (regularTerms dataSet scale polymer boundary)))
    (map (extractBoundary dataSet scale polymer)
      (map (localize dataSet scale polymer)
        (boundarySourceTerms dataSet scale polymer boundary)))

R :
  ∀ {Scale Polymer BoundaryCondition Region Term LocalizedTerm BoundaryTerm
      RExpression}
    (dataSet : FiniteROperationData Scale Polymer BoundaryCondition Region Term
      LocalizedTerm BoundaryTerm RExpression) →
  Scale → Polymer → BoundaryCondition → RExpression
R dataSet scale polymer boundary =
  regularExpression (runROperation dataSet scale polymer boundary)

B :
  ∀ {Scale Polymer BoundaryCondition Region Term LocalizedTerm BoundaryTerm
      RExpression}
    (dataSet : FiniteROperationData Scale Polymer BoundaryCondition Region Term
      LocalizedTerm BoundaryTerm RExpression) →
  Scale → Polymer → BoundaryCondition → List BoundaryTerm
B dataSet scale polymer boundary =
  generatedBoundaryTerms (runROperation dataSet scale polymer boundary)

------------------------------------------------------------------------
-- Exact boundary reinjection bookkeeping tied to the R result.
------------------------------------------------------------------------

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ right = right
(left ∷ rest) ++ right = left ∷ (rest ++ right)

reinjectGeneratedBoundaryTerms :
  ∀ {BoundaryTerm} → List BoundaryTerm → List BoundaryTerm → List BoundaryTerm
reinjectGeneratedBoundaryTerms generated nextDensity = generated ++ nextDensity

nextBoundaryDensity :
  ∀ {Scale Polymer BoundaryCondition Region Term LocalizedTerm BoundaryTerm
      RExpression}
    (dataSet : FiniteROperationData Scale Polymer BoundaryCondition Region Term
      LocalizedTerm BoundaryTerm RExpression) →
  Scale → Polymer → BoundaryCondition → List BoundaryTerm → List BoundaryTerm
nextBoundaryDensity dataSet scale polymer boundary previous =
  reinjectGeneratedBoundaryTerms (B dataSet scale polymer boundary) previous

reinjectBoundaryTermsPreservesEffectiveDensity :
  ∀ {Scale Polymer BoundaryCondition Region Term LocalizedTerm BoundaryTerm
      RExpression}
    (dataSet : FiniteROperationData Scale Polymer BoundaryCondition Region Term
      LocalizedTerm BoundaryTerm RExpression)
    scale polymer boundary previous →
  nextBoundaryDensity dataSet scale polymer boundary previous
  ≡ B dataSet scale polymer boundary ++ previous
reinjectBoundaryTermsPreservesEffectiveDensity dataSet scale polymer boundary previous = refl

------------------------------------------------------------------------
-- Representation-specific structural laws.
------------------------------------------------------------------------

record ROperationStructuralLaws
    {Scale Polymer BoundaryCondition Region Term LocalizedTerm BoundaryTerm
      RExpression Support Gauge AnalyticDomain : Set}
    (dataSet : FiniteROperationData Scale Polymer BoundaryCondition Region Term
      LocalizedTerm BoundaryTerm RExpression) : Set₁ where
  field
    support : RExpression → Support
    enlargedSupport : Scale → Polymer → Support
    Subset : Support → Support → Set

    transformBoundary : Gauge → BoundaryCondition → BoundaryCondition
    transformExpression : Gauge → RExpression → RExpression

    analyticDomain : Scale → Polymer → AnalyticDomain
    AnalyticOnR : RExpression → AnalyticDomain → Set
    AnalyticOnBoundary : List BoundaryTerm → AnalyticDomain → Set

    rOperationLocalized : ∀ scale polymer boundary →
      Subset
        (support (R dataSet scale polymer boundary))
        (enlargedSupport scale polymer)

    rOperationGaugeCovariant : ∀ gauge scale polymer boundary →
      R dataSet scale polymer (transformBoundary gauge boundary)
      ≡ transformExpression gauge (R dataSet scale polymer boundary)

    rAndBoundaryShareAnalyticityRadius : ∀ scale polymer boundary →
      AnalyticOnR
        (R dataSet scale polymer boundary)
        (analyticDomain scale polymer)
      × AnalyticOnBoundary
        (B dataSet scale polymer boundary)
        (analyticDomain scale polymer)

open ROperationStructuralLaws public

record BoundarySupportReinjectionLaws
    {Scale Polymer BoundaryCondition Region Term LocalizedTerm BoundaryTerm
      RExpression Support DeterminingSet : Set}
    (dataSet : FiniteROperationData Scale Polymer BoundaryCondition Region Term
      LocalizedTerm BoundaryTerm RExpression) : Set₁ where
  field
    boundarySupport : BoundaryTerm → Support
    nextDeterminingSet : Scale → Polymer → DeterminingSet
    SupportOwnedBy : Support → DeterminingSet → Set

    reinjectBoundaryTermsPreservesSupport :
      ∀ scale polymer boundary term →
      term ∈ B dataSet scale polymer boundary →
      SupportOwnedBy (boundarySupport term)
        (nextDeterminingSet scale polymer)

open BoundarySupportReinjectionLaws public

------------------------------------------------------------------------
-- R-decay assembly: the hard analytic estimates are separated into named
-- inequalities, while their transitive composition is proved here.
------------------------------------------------------------------------

record ROperationDecayDerivation
    (Scale Polymer BoundaryCondition Bound : Set) : Set₁ where
  field
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    multiply : Bound → Bound → Bound
    rNorm : Scale → Polymer → BoundaryCondition → Bound
    componentProductBound localizedBound exponentiatedBound :
      Scale → Polymer → Bound
    p0Suppression diameterDecay targetBound : Scale → Polymer → Bound

    rToComponentProduct : ∀ scale polymer boundary →
      LessEqual (rNorm scale polymer boundary)
        (componentProductBound scale polymer)

    connectedComponentCounting : ∀ scale polymer →
      LessEqual (componentProductBound scale polymer)
        (localizedBound scale polymer)

    rLocalizationNonexpansive : ∀ scale polymer →
      LessEqual (localizedBound scale polymer)
        (exponentiatedBound scale polymer)

    localizedExponentiationBound : ∀ scale polymer →
      LessEqual (exponentiatedBound scale polymer)
        (targetBound scale polymer)

    targetIsP0TimesDiameter : ∀ scale polymer →
      targetBound scale polymer
      ≡ multiply
          (p0Suppression scale polymer)
          (diameterDecay scale polymer)

open ROperationDecayDerivation public

rOperationDecayUniformInBoundary :
  ∀ {Scale Polymer BoundaryCondition Bound}
    (dataSet : ROperationDecayDerivation
      Scale Polymer BoundaryCondition Bound)
    scale polymer boundary →
  LessEqual dataSet
    (rNorm dataSet scale polymer boundary)
    (targetBound dataSet scale polymer)
rOperationDecayUniformInBoundary dataSet scale polymer boundary =
  transitive dataSet
    (rToComponentProduct dataSet scale polymer boundary)
    (transitive dataSet
      (connectedComponentCounting dataSet scale polymer)
      (transitive dataSet
        (rLocalizationNonexpansive dataSet scale polymer)
        (localizedExponentiationBound dataSet scale polymer)))

rDecayTargetIndependentOfBoundary :
  ∀ {Scale Polymer BoundaryCondition Bound}
    (dataSet : ROperationDecayDerivation
      Scale Polymer BoundaryCondition Bound)
    scale polymer (first second : BoundaryCondition) →
  targetBound dataSet scale polymer ≡ targetBound dataSet scale polymer
rDecayTargetIndependentOfBoundary dataSet scale polymer first second = refl

expressionIntersectionPartitionLevel : ProofLevel
expressionIntersectionPartitionLevel = machineChecked

finiteROperationDefinitionLevel : ProofLevel
finiteROperationDefinitionLevel = machineChecked

boundaryReinjectionDefinitionLevel : ProofLevel
boundaryReinjectionDefinitionLevel = machineChecked

rOperationStructuralLawInputsLevel : ProofLevel
rOperationStructuralLawInputsLevel = conditional

rBoundarySupportReinjectionInputsLevel : ProofLevel
rBoundarySupportReinjectionInputsLevel = conditional

rDecayTransitiveAssemblyLevel : ProofLevel
rDecayTransitiveAssemblyLevel = machineChecked

rDecayAnalyticInequalityInputsLevel : ProofLevel
rDecayAnalyticInequalityInputsLevel = conditional
