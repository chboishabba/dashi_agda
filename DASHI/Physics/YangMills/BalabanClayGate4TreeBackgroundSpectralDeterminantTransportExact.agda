module DASHI.Physics.YangMills.BalabanClayGate4TreeBackgroundSpectralDeterminantTransportExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4TreeBackgroundSliceTransitionExact as Slice
import DASHI.Physics.YangMills.BalabanClayGate4FiniteSimilaritySpectrumDeterminantExact as Similarity

------------------------------------------------------------------------
-- Coherent tree/background spectrum and determinant transport.
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
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- The same local slice transition must own the tangent isomorphism, Hessian
-- conjugacy, matrix similarity and norm transport.  This record prevents a
-- spectral proof from using one basis change while the determinant proof uses
-- another.  Eigenpairs, coercivity and determinants are then transported by
-- the already proved finite algebra.
------------------------------------------------------------------------

record TreeBackgroundSpectralDeterminantTransport
    (TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      Matrix Scalar Bound : Set) : Set₁ where
  field
    sliceTransition : Slice.LocalSliceTransition
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent

  tangentIsomorphism : Slice.TangentIsomorphism TreeTangent BackgroundTangent
  tangentIsomorphism = Slice.sliceTransitionTangentIsomorphism sliceTransition

  field
    referenceOperators : Slice.ConjugateOperators
      TreeTangent BackgroundTangent Scalar tangentIsomorphism

    coercivity : Slice.SliceCoercivityTransport
      TreeTangent BackgroundTangent Bound tangentIsomorphism

    determinantSimilarity :
      Similarity.FiniteSimilarityDeterminantData Matrix Scalar

    TreeReferenceMatrixMatchesLeftOperator : Set
    BackgroundReferenceMatrixMatchesRightOperator : Set
    TangentAndMatrixChangeAgree : Set

    treeReferenceMatrixMatchesLeftOperator :
      TreeReferenceMatrixMatchesLeftOperator
    backgroundReferenceMatrixMatchesRightOperator :
      BackgroundReferenceMatrixMatchesRightOperator
    tangentAndMatrixChangeAgree : TangentAndMatrixChangeAgree

open TreeBackgroundSpectralDeterminantTransport public

treeEigenpairToBackgroundEigenpair :
  ∀ {TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      Matrix Scalar Bound}
    (dataSet : TreeBackgroundSpectralDeterminantTransport
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      Matrix Scalar Bound) →
  Slice.Eigenpair TreeTangent Scalar
    (Slice.leftOperator (referenceOperators dataSet))
    (Slice.scaleLeft (referenceOperators dataSet)) →
  Slice.Eigenpair BackgroundTangent Scalar
    (Slice.rightOperator (referenceOperators dataSet))
    (Slice.scaleRight (referenceOperators dataSet))
treeEigenpairToBackgroundEigenpair dataSet =
  Slice.transportEigenpairAcrossSlice (referenceOperators dataSet)

backgroundReferenceCoerciveOnTreeImage :
  ∀ {TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      Matrix Scalar Bound}
    (dataSet : TreeBackgroundSpectralDeterminantTransport
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      Matrix Scalar Bound)
    treeVector →
  Slice.LessEqual (coercivity dataSet)
    (Slice.coercivityConstant (coercivity dataSet))
    (Slice.rightForm (coercivity dataSet)
      (Slice.forward (tangentIsomorphism dataSet) treeVector))
backgroundReferenceCoerciveOnTreeImage dataSet =
  Slice.rightCoerciveOnForwardImage (coercivity dataSet)

backgroundReferenceDeterminantEqualsTreeReference :
  ∀ {TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      Matrix Scalar Bound}
    (dataSet : TreeBackgroundSpectralDeterminantTransport
      TreeSlice BackgroundSlice TreeTangent BackgroundTangent
      Matrix Scalar Bound) →
  Similarity.Determinant.determinant
    (Similarity.matrixAlgebra (determinantSimilarity dataSet))
    (Similarity.similarityMatrix (determinantSimilarity dataSet))
  ≡ Similarity.Determinant.determinant
      (Similarity.matrixAlgebra (determinantSimilarity dataSet))
      (Similarity.operator (determinantSimilarity dataSet))
backgroundReferenceDeterminantEqualsTreeReference dataSet =
  Similarity.determinantSimilarityInvariant
    (determinantSimilarity dataSet)

treeBackgroundCoherentChangeOfBasisLevel : ProofLevel
treeBackgroundCoherentChangeOfBasisLevel = machineChecked

treeBackgroundEigenpairTransportLevel : ProofLevel
treeBackgroundEigenpairTransportLevel = machineChecked

treeBackgroundCoercivityTransportLevel : ProofLevel
treeBackgroundCoercivityTransportLevel = machineChecked

treeBackgroundDeterminantTransportLevel : ProofLevel
treeBackgroundDeterminantTransportLevel = machineChecked

physicalTreeBackgroundMatrixAgreementInputsLevel : ProofLevel
physicalTreeBackgroundMatrixAgreementInputsLevel = conditional
