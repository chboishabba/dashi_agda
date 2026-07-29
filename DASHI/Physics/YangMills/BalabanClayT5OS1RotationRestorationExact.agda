module DASHI.Physics.YangMills.BalabanClayT5OS1RotationRestorationExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit

------------------------------------------------------------------------
-- Primary provenance.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- Kurt Symanzik,
-- "Continuum Limit and Improved Action in Lattice Theories: (I). Principles
-- and phi^4 Theory", Nuclear Physics B 226 (1983), 187--204.
-- DOI: 10.1016/0550-3213(83)90468-6.
--
-- Zohreh Davoudi and Martin J. Savage,
-- "Restoration of Rotational Symmetry in the Continuum Limit of Lattice Field
-- Theories", Physical Review D 86 (2012), 054505.
-- DOI: 10.1103/PhysRevD.86.054505; arXiv:1204.4146.
--
-- The last paper supplies a perturbative precedent, not a nonperturbative
-- Yang--Mills OS1 theorem.  The exact hypotheses required by the dense-limit
-- argument remain visible below.
------------------------------------------------------------------------

record DenseRotationRestoration
    (Rotation Observable Scalar : Set) : Set₁ where
  field
    rotate : Rotation → Observable → Observable
    correlator : Observable → Scalar

    HypercubicRotation FullRotation : Rotation → Set
    approximate : Rotation → Nat → Rotation

    approximantsAreHypercubic : ∀ rotation depth →
      FullRotation rotation → HypercubicRotation (approximate rotation depth)

    Converges : (Nat → Scalar) → Scalar → Set
    convergenceCongruent : ∀ first second target →
      (∀ depth → first depth ≡ second depth) →
      Converges first target → Converges second target
    constantConverges : ∀ value → Converges (λ _ → value) value
    limitUnique : ∀ sequence first second →
      Converges sequence first → Converges sequence second → first ≡ second

    hypercubicCovariance : ∀ rotation observable →
      HypercubicRotation rotation →
      correlator (rotate rotation observable) ≡ correlator observable

    rotationApproximationContinuity : ∀ rotation observable →
      FullRotation rotation →
      Converges
        (λ depth → correlator (rotate (approximate rotation depth) observable))
        (correlator (rotate rotation observable))

open DenseRotationRestoration public

fullRotationCovariance :
  ∀ {Rotation Observable Scalar}
    (dataSet : DenseRotationRestoration Rotation Observable Scalar)
    rotation observable →
  FullRotation dataSet rotation →
  correlator dataSet (rotate dataSet rotation observable)
  ≡ correlator dataSet observable
fullRotationCovariance dataSet rotation observable full =
  limitUnique dataSet
    (λ depth → correlator dataSet
      (rotate dataSet (approximate dataSet rotation depth) observable))
    (correlator dataSet (rotate dataSet rotation observable))
    (correlator dataSet observable)
    (rotationApproximationContinuity dataSet rotation observable full)
    (convergenceCongruent dataSet
      (λ _ → correlator dataSet observable)
      (λ depth → correlator dataSet
        (rotate dataSet (approximate dataSet rotation depth) observable))
      (correlator dataSet observable)
      (λ depth → sym (hypercubicCovariance dataSet
        (approximate dataSet rotation depth) observable
        (approximantsAreHypercubic dataSet rotation depth full)))
      (constantConverges dataSet (correlator dataSet observable)))

record EuclideanCovarianceAssembly
    (Translation Rotation Observable Scalar : Set) : Set₁ where
  field
    rotationData : DenseRotationRestoration Rotation Observable Scalar

    translate : Translation → Observable → Observable
    correlator : Observable → Scalar
    translationCovariant : ∀ translation observable →
      correlator (translate translation observable) ≡ correlator observable

    rotationCorrelatorMeaning : ∀ observable →
      DenseRotationRestoration.correlator rotationData observable
      ≡ correlator observable

open EuclideanCovarianceAssembly public

assembledRotationCovariance :
  ∀ {Translation Rotation Observable Scalar}
    (dataSet : EuclideanCovarianceAssembly
      Translation Rotation Observable Scalar)
    rotation observable →
  FullRotation (rotationData dataSet) rotation →
  correlator dataSet
    (rotate (rotationData dataSet) rotation observable)
  ≡ correlator dataSet observable
assembledRotationCovariance dataSet rotation observable full =
  trans
    (sym (rotationCorrelatorMeaning dataSet
      (rotate (rotationData dataSet) rotation observable)))
    (trans
      (fullRotationCovariance (rotationData dataSet) rotation observable full)
      (rotationCorrelatorMeaning dataSet observable))

record OS1ClosureInterpretation
    {Measure Schwinger Translation Rotation Observable Scalar : Set}
    (closure : Limit.FiniteToContinuumOSClosure Measure Schwinger)
    (assembly : EuclideanCovarianceAssembly
      Translation Rotation Observable Scalar) : Set₁ where
  field
    continuumSchwingerObservables : Schwinger → Observable

    translationAndRotationCovarianceImpliesOS1 :
      ((translation : Translation) → (observable : Observable) →
        correlator assembly (translate assembly translation observable)
        ≡ correlator assembly observable) →
      ((rotation : Rotation) → (observable : Observable) →
        FullRotation (rotationData assembly) rotation →
        correlator assembly
          (rotate (rotationData assembly) rotation observable)
        ≡ correlator assembly observable) →
      Limit.EuclideanCovariant closure
        (Limit.schwinger closure (Limit.continuumMeasure closure))

open OS1ClosureInterpretation public

continuumOS1FromDenseRotationRestoration :
  ∀ {Measure Schwinger Translation Rotation Observable Scalar}
    {closure : Limit.FiniteToContinuumOSClosure Measure Schwinger}
    {assembly : EuclideanCovarianceAssembly
      Translation Rotation Observable Scalar} →
  OS1ClosureInterpretation closure assembly →
  Limit.EuclideanCovariant closure
    (Limit.schwinger closure (Limit.continuumMeasure closure))
continuumOS1FromDenseRotationRestoration interpretation =
  translationAndRotationCovarianceImpliesOS1 interpretation
    (translationCovariant _)
    (assembledRotationCovariance _)

denseRotationLimitArgumentLevel : ProofLevel
denseRotationLimitArgumentLevel = machineChecked

euclideanCovarianceAssemblyLevel : ProofLevel
euclideanCovarianceAssemblyLevel = machineChecked

continuumOS1InterpretationAssemblyLevel : ProofLevel
continuumOS1InterpretationAssemblyLevel = machineChecked

physicalDenseRotationApproximationInputsLevel : ProofLevel
physicalDenseRotationApproximationInputsLevel = conditional

physicalRotatedCorrelatorContinuityInputsLevel : ProofLevel
physicalRotatedCorrelatorContinuityInputsLevel = conditional

physicalOS1PredicateMeaningInputsLevel : ProofLevel
physicalOS1PredicateMeaningInputsLevel = conditional
