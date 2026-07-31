module DASHI.Physics.YangMills.BalabanClayGate4TreeBackgroundSliceTransitionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Local analytic transition from rooted tree gauge to Bałaban's gauge slice.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions", Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- The finite tranche already constructs unique rooted tree-gauge coordinates.
-- The physical theorem is not literal equality of that slice with Bałaban's
-- background/Faddeev--Popov slice; it is a local analytic equivalence.  The
-- record below fixes the correct theorem boundary.  Once the two local maps and
-- their differentiated composition laws are supplied, their tangent maps are
-- automatically mutually inverse.  Hessian conjugacy then transports
-- eigenpairs without a second basis-identification assumption.
------------------------------------------------------------------------

record LocalSliceTransition
    (TreeSlice BackgroundSlice TreeTangent BackgroundTangent : Set) : Set₁ where
  field
    treeOrigin : TreeSlice
    backgroundOrigin : BackgroundSlice

    toBackground : TreeSlice → BackgroundSlice
    toTree : BackgroundSlice → TreeSlice

    toBackgroundAtOrigin :
      toBackground treeOrigin ≡ backgroundOrigin
    toTreeAtOrigin :
      toTree backgroundOrigin ≡ treeOrigin

    localTreeDomain : TreeSlice → Set
    localBackgroundDomain : BackgroundSlice → Set

    treeRoundTrip : ∀ tree →
      localTreeDomain tree → toTree (toBackground tree) ≡ tree

    backgroundRoundTrip : ∀ background →
      localBackgroundDomain background →
      toBackground (toTree background) ≡ background

    derivativeToBackground : TreeTangent → BackgroundTangent
    derivativeToTree : BackgroundTangent → TreeTangent

    differentiatedTreeRoundTrip : ∀ tangent →
      derivativeToTree (derivativeToBackground tangent) ≡ tangent

    differentiatedBackgroundRoundTrip : ∀ tangent →
      derivativeToBackground (derivativeToTree tangent) ≡ tangent

open LocalSliceTransition public

record TangentIsomorphism (Left Right : Set) : Set₁ where
  field
    forward : Left → Right
    inverse : Right → Left
    inverseAfterForward : ∀ value → inverse (forward value) ≡ value
    forwardAfterInverse : ∀ value → forward (inverse value) ≡ value

open TangentIsomorphism public

sliceTransitionTangentIsomorphism :
  ∀ {TreeSlice BackgroundSlice TreeTangent BackgroundTangent}
    (transition : LocalSliceTransition
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent) →
  TangentIsomorphism TreeTangent BackgroundTangent
sliceTransitionTangentIsomorphism transition = record
  { forward = derivativeToBackground transition
  ; inverse = derivativeToTree transition
  ; inverseAfterForward = differentiatedTreeRoundTrip transition
  ; forwardAfterInverse = differentiatedBackgroundRoundTrip transition
  }

record ConjugateOperators
    (Left Right Scalar : Set)
    (isomorphism : TangentIsomorphism Left Right) : Set₁ where
  field
    leftOperator : Left → Left
    rightOperator : Right → Right
    scaleLeft : Scalar → Left → Left
    scaleRight : Scalar → Right → Right

    forwardLinearForScale : ∀ scalar vector →
      forward isomorphism (scaleLeft scalar vector)
      ≡ scaleRight scalar (forward isomorphism vector)

    conjugacy : ∀ vector →
      rightOperator (forward isomorphism vector)
      ≡ forward isomorphism (leftOperator vector)

open ConjugateOperators public

record Eigenpair
    (Vector Scalar : Set)
    (operator : Vector → Vector)
    (scale : Scalar → Vector → Vector) : Set₁ where
  field
    eigenvector : Vector
    eigenvalue : Scalar
    eigenEquation :
      operator eigenvector ≡ scale eigenvalue eigenvector

open Eigenpair public

transportEigenpairAcrossSlice :
  ∀ {Left Right Scalar}
    {isomorphism : TangentIsomorphism Left Right}
    (operators : ConjugateOperators Left Right Scalar isomorphism) →
  Eigenpair Left Scalar
    (leftOperator operators) (scaleLeft operators) →
  Eigenpair Right Scalar
    (rightOperator operators) (scaleRight operators)
transportEigenpairAcrossSlice {isomorphism = isomorphism} operators source = record
  { eigenvector = forward isomorphism (eigenvector source)
  ; eigenvalue = eigenvalue source
  ; eigenEquation =
      trans
        (conjugacy operators (eigenvector source))
        (trans
          (cong (forward isomorphism)
            (eigenEquation source))
          (forwardLinearForScale operators
            (eigenvalue source) (eigenvector source)))
  }

record SliceNormEquivalence
    (Left Right Bound : Set)
    (isomorphism : TangentIsomorphism Left Right) : Set₁ where
  field
    leftNormSq : Left → Bound
    rightNormSq : Right → Bound
    forwardNormExact : ∀ vector →
      rightNormSq (forward isomorphism vector) ≡ leftNormSq vector
    inverseNormExact : ∀ vector →
      leftNormSq (inverse isomorphism vector) ≡ rightNormSq vector

open SliceNormEquivalence public

record SliceCoercivityTransport
    (Left Right Bound : Set)
    (isomorphism : TangentIsomorphism Left Right) : Set₁ where
  field
    norms : SliceNormEquivalence Left Right Bound isomorphism
    leftForm : Left → Bound
    rightForm : Right → Bound
    coercivityConstant : Bound
    LessEqual : Bound → Bound → Set

    leftCoercive : ∀ vector →
      LessEqual coercivityConstant (leftForm vector)

    rightFormMeaning : ∀ vector →
      rightForm (forward isomorphism vector) ≡ leftForm vector

open SliceCoercivityTransport public

rightCoerciveOnForwardImage :
  ∀ {Left Right Bound}
    {isomorphism : TangentIsomorphism Left Right}
    (dataSet : SliceCoercivityTransport Left Right Bound isomorphism)
    vector →
  LessEqual dataSet
    (coercivityConstant dataSet)
    (rightForm dataSet (forward isomorphism vector))
rightCoerciveOnForwardImage dataSet vector =
  substRight
    (rightFormMeaning dataSet vector)
    (leftCoercive dataSet vector)
  where
  substRight : ∀ {A : Set} {Relation : A → A → Set}
    {lower left right : A} →
    left ≡ right → Relation lower right → Relation lower left
  substRight equality proof rewrite equality = proof

localSliceTangentIsomorphismAssemblyLevel : ProofLevel
localSliceTangentIsomorphismAssemblyLevel = machineChecked

sliceHessianEigenpairTransportLevel : ProofLevel
sliceHessianEigenpairTransportLevel = machineChecked

sliceCoercivityTransportLevel : ProofLevel
sliceCoercivityTransportLevel = machineChecked

physicalTreeBackgroundLocalTransitionInputsLevel : ProofLevel
physicalTreeBackgroundLocalTransitionInputsLevel = conditional

physicalFaddeevPopovInvertibilityInputsLevel : ProofLevel
physicalFaddeevPopovInvertibilityInputsLevel = conditional

physicalSliceNormIsometryInputsLevel : ProofLevel
physicalSliceNormIsometryInputsLevel = conditional
