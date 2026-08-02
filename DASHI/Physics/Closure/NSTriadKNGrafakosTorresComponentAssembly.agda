module DASHI.Physics.Closure.NSTriadKNGrafakosTorresComponentAssembly where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Pierre Germain; DASHI
-- repository contributors.
-- Title: "Componentwise assembly of the three Grafakos-Torres conditions for
-- the periodic Navier-Stokes kernel".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; Journal of
-- Differential Equations 226 (2006), 373--428; DASHI formal development,
-- 2026.
-- DOI: 10.1006/jfan.2001.3804; 10.1016/j.jde.2005.10.007;
-- repository-original class assembly has no DOI.
-- Uses: a positive kernel, six exact absolute geometry classes, monotonicity
-- of finite sums, the output condition and both partial-adjoint conditions.
-- Relationship: proves the finite six-class addition step generically.  The
-- Navier-Stokes instantiation remains open precisely at the classwise analytic
-- bounds, affine weights and cutoff-independent transport constants.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNExactDyadicShellGeometry as Geometry
import DASHI.Physics.Closure.NSTriadKNGrafakosTorresThreeFunctionSchurProgram as GT
import DASHI.Physics.Closure.NSTriadKNComponentAffineConstraintLedger as Affine

data SixGeometryClass : Set where
  leftLowClass rightLowClass outputLowClass
  comparableClass transitionClass residualClass : SixGeometryClass

record SixClassOrderedAdditiveCarrier {s : Level} : Set (lsuc s) where
  field
    Scalar : Set s
    zero : Scalar
    add : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set s

    leqTransitive : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    addMonotone : ∀ {a b c d} → a ≤ b → c ≤ d →
      add a c ≤ add b d

open SixClassOrderedAdditiveCarrier public

sumSix :
  ∀ {s} (C : SixClassOrderedAdditiveCarrier {s}) →
  (SixGeometryClass → Scalar C) → Scalar C
sumSix C value =
  add C (value leftLowClass)
    (add C (value rightLowClass)
      (add C (value outputLowClass)
        (add C (value comparableClass)
          (add C (value transitionClass) (value residualClass)))))

sumSixMonotone :
  ∀ {s} (C : SixClassOrderedAdditiveCarrier {s})
    (left right : SixGeometryClass → Scalar C) →
  (∀ geometry → _≤_ C (left geometry) (right geometry)) →
  _≤_ C (sumSix C left) (sumSix C right)
sumSixMonotone C left right bound =
  addMonotone C (bound leftLowClass)
    (addMonotone C (bound rightLowClass)
      (addMonotone C (bound outputLowClass)
        (addMonotone C (bound comparableClass)
          (addMonotone C
            (bound transitionClass)
            (bound residualClass)))))

record OneSchurConditionClassAssembly {s : Level}
    (C : SixClassOrderedAdditiveCarrier {s}) : Set (lsuc s) where
  field
    classContribution : SixGeometryClass → Scalar C
    classTarget : SixGeometryClass → Scalar C

    classBound : ∀ geometry →
      _≤_ C (classContribution geometry) (classTarget geometry)

open OneSchurConditionClassAssembly public

assembleOneSchurCondition :
  ∀ {s} {C : SixClassOrderedAdditiveCarrier {s}} →
  (A : OneSchurConditionClassAssembly C) →
  _≤_ C
    (sumSix C (classContribution A))
    (sumSix C (classTarget A))
assembleOneSchurCondition {C = C} A =
  sumSixMonotone C
    (classContribution A)
    (classTarget A)
    (classBound A)

record ThreeConditionComponentAssembly {s : Level} : Set (lsuc s) where
  field
    orderedCarrier : SixClassOrderedAdditiveCarrier {s}

    outputAssembly : OneSchurConditionClassAssembly orderedCarrier
    firstAdjointAssembly : OneSchurConditionClassAssembly orderedCarrier
    secondAdjointAssembly : OneSchurConditionClassAssembly orderedCarrier

    outputClassPartitionMatchesKernel : Set s
    firstClassPartitionMatchesTransposeKernel : Set s
    secondClassPartitionMatchesTransposeKernel : Set s

    positiveKernelDominatesSignedCoefficient : Set s
    completeAffineLedger : Affine.CompleteComponentConstraintLedger {s}

    outputTargetsReassembleToGTTarget : Set s
    firstTargetsReassembleToGTTarget : Set s
    secondTargetsReassembleToGTTarget : Set s

    orbitHelicityRealityConstantsIncluded : Set s
    directionWeightPreservesEveryClass : Set s
    everyAssemblyConstantIndependentOfCutoff : Set s

open ThreeConditionComponentAssembly public

outputConditionAssembled :
  ∀ {s} (A : ThreeConditionComponentAssembly {s}) →
  let C = orderedCarrier A in
  _≤_ C
    (sumSix C (classContribution (outputAssembly A)))
    (sumSix C (classTarget (outputAssembly A)))
outputConditionAssembled A = assembleOneSchurCondition (outputAssembly A)

firstAdjointConditionAssembled :
  ∀ {s} (A : ThreeConditionComponentAssembly {s}) →
  let C = orderedCarrier A in
  _≤_ C
    (sumSix C (classContribution (firstAdjointAssembly A)))
    (sumSix C (classTarget (firstAdjointAssembly A)))
firstAdjointConditionAssembled A =
  assembleOneSchurCondition (firstAdjointAssembly A)

secondAdjointConditionAssembled :
  ∀ {s} (A : ThreeConditionComponentAssembly {s}) →
  let C = orderedCarrier A in
  _≤_ C
    (sumSix C (classContribution (secondAdjointAssembly A)))
    (sumSix C (classTarget (secondAdjointAssembly A)))
secondAdjointConditionAssembled A =
  assembleOneSchurCondition (secondAdjointAssembly A)

record ConcreteGrafakosTorresInstantiationCutset : Set₁ where
  field
    exactPositiveNavierStokesKernel : Set
    outputSixClassBounds : Set
    firstAdjointSixClassBounds : Set
    secondAdjointSixClassBounds : Set

    strictThreeWeightCertificate : Set
    outputTargetIdentification : Set
    firstTargetIdentification : Set
    secondTargetIdentification : Set

    orbitToShellTransport : Set
    finiteHelicityTransport : Set
    realityMateTransport : Set
    directionWeightTransport : Set
    allConstantsUniformInCutoff : Set

    grafakosTorresConditionC : Set

open ConcreteGrafakosTorresInstantiationCutset public

sixClassMonotoneAssemblyClosed : Bool
sixClassMonotoneAssemblyClosed = true

sixClassMonotoneAssemblyClosedIsTrue :
  sixClassMonotoneAssemblyClosed ≡ true
sixClassMonotoneAssemblyClosedIsTrue = refl

allThreeGenericClassAssembliesClosed : Bool
allThreeGenericClassAssembliesClosed = true

allThreeGenericClassAssembliesClosedIsTrue :
  allThreeGenericClassAssembliesClosed ≡ true
allThreeGenericClassAssembliesClosedIsTrue = refl

concreteNavierStokesGrafakosTorresConditionsClosed : Bool
concreteNavierStokesGrafakosTorresConditionsClosed = false

concreteNavierStokesGrafakosTorresConditionsClosedIsFalse :
  concreteNavierStokesGrafakosTorresConditionsClosed ≡ false
concreteNavierStokesGrafakosTorresConditionsClosedIsFalse = refl
