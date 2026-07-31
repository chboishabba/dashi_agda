module DASHI.Physics.YangMills.BalabanClayGate4T3TreeGaugeSpectralDeterminantExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT3PhysicalUniformFluctuationCoercivityExact as T3
import DASHI.Physics.YangMills.BalabanClayGate4SelfAdjointFormOperatorNormExact as FormNorm
import DASHI.Physics.YangMills.BalabanClayGate4T3FiveChannelSumReuseExact as Five
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicTreeGaugeFiniteBasisExact as TreeBasis
import DASHI.Physics.YangMills.BalabanClayGate4FiniteTangentMatrixRepresentationExact as Matrix
import DASHI.Physics.YangMills.BalabanClayGate4FiniteMatrixSpectrumDeterminantAssemblyExact as Assembly
import DASHI.Physics.YangMills.BalabanClayGate4FiniteHermitianRayleighSpectrumExact as Spectrum
import DASHI.Physics.YangMills.BalabanClayGate4IpsenRehmanPrimaryCorollary214Exact as Determinant

------------------------------------------------------------------------
-- T3 physical spectral identification on tree-gauge coordinates.
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
-- Ilse C. F. Ipsen and Rizwana Rehman,
-- "Perturbation Bounds for Determinants and Characteristic Polynomials",
-- SIAM Journal on Matrix Analysis and Applications 30 (2008), 762--776.
-- DOI: 10.1137/070704770.
--
-- One coherent witness below owns the T3 remainder, the off-tree basis, the
-- physical/reference/remainder matrices, the matrix norm, the finite spectrum
-- and the determinant data.  This prevents the coercivity, inverse norm and
-- determinant claims from silently referring to different finite carriers.
------------------------------------------------------------------------

record T3TreeGaugeSpectralDeterminantInputs
    (n : Nat)
    (Scale Volume PatchRegime Background Fluctuation Tangent Bound
      MatrixCarrier SpectralIndex : Set) : Set₁ where
  field
    fiveChannel : Five.T3FiveChannelReducedInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound

    treeBasis : TreeBasis.PeriodicTreeGaugeBasisInputs n Bound Fluctuation

    matrixRepresentation :
      Matrix.RestrictedHessianMatrixRepresentation
        (Fluctuation → Fluctuation) MatrixCarrier Fluctuation

    matrixReferenceIsT3Reference :
      Matrix.referenceOperator matrixRepresentation
      ≡ T3.referenceHessian (Five.t3 fiveChannel)
          (T3.makeIndex (Five.t3 fiveChannel)
            (Five.scale fiveChannel)
            (Five.volume fiveChannel)
            (Five.regime fiveChannel)
            (Five.background fiveChannel))

    matrixPhysicalIsT3Physical :
      Matrix.physicalOperator matrixRepresentation
      ≡ T3.physicalFluctuationHessian (Five.t3 fiveChannel)
          (Five.scale fiveChannel)
          (Five.volume fiveChannel)
          (Five.regime fiveChannel)
          (Five.background fiveChannel)

    matrixRemainderIsT3Remainder :
      Matrix.remainderOperator matrixRepresentation
      ≡ T3.backgroundHessianRemainder (Five.t3 fiveChannel)
          (T3.makeIndex (Five.t3 fiveChannel)
            (Five.scale fiveChannel)
            (Five.volume fiveChannel)
            (Five.regime fiveChannel)
            (Five.background fiveChannel))

    remainderNormTransport : Matrix.MatrixOperatorNormTransport
      (Fluctuation → Fluctuation) MatrixCarrier Bound

    selectedRemainderOperatorExact :
      Matrix.selectedOperator remainderNormTransport
      ≡ T3.backgroundHessianRemainder (Five.t3 fiveChannel)
          (T3.makeIndex (Five.t3 fiveChannel)
            (Five.scale fiveChannel)
            (Five.volume fiveChannel)
            (Five.regime fiveChannel)
            (Five.background fiveChannel))

    selectedRemainderMatrixExact :
      Matrix.selectedMatrix remainderNormTransport
      ≡ Matrix.remainderMatrix matrixRepresentation

    operatorNormMeaning :
      Matrix.operatorNorm remainderNormTransport
        (Matrix.selectedOperator remainderNormTransport)
      ≡ FormNorm.operatorNorm (Five.normData fiveChannel)
          (T3.backgroundHessianRemainder (Five.t3 fiveChannel)
            (T3.makeIndex (Five.t3 fiveChannel)
              (Five.scale fiveChannel)
              (Five.volume fiveChannel)
              (Five.regime fiveChannel)
              (Five.background fiveChannel)))

    operatorOrderMeaning : ∀ left right →
      Matrix.OperatorLessEqual remainderNormTransport left right
      ≡ FormNorm.LessEqual (Five.normData fiveChannel) left right

    finiteAssembly : Assembly.FiniteMatrixSpectrumDeterminantAssembly
      SpectralIndex (Fluctuation → Fluctuation)
      MatrixCarrier Fluctuation Bound

    assemblyUsesSelectedMatrixRepresentation :
      Assembly.matrixRepresentation finiteAssembly ≡ matrixRepresentation

    TreeGaugeBasisRepresentsConstrainedTangent : Set
    treeGaugeBasisRepresentsConstrainedTangent :
      TreeGaugeBasisRepresentsConstrainedTangent

    SelectedSpectrumIsReferenceHessianSpectrum : Set
    selectedSpectrumIsReferenceHessianSpectrum :
      SelectedSpectrumIsReferenceHessianSpectrum

open T3TreeGaugeSpectralDeterminantInputs public

remainderOperatorNormBoundInTransportOrder :
  ∀ {n Scale Volume PatchRegime Background Fluctuation Tangent Bound
      MatrixCarrier SpectralIndex}
    (inputs : T3TreeGaugeSpectralDeterminantInputs n
      Scale Volume PatchRegime Background Fluctuation Tangent Bound
      MatrixCarrier SpectralIndex) →
  Matrix.OperatorLessEqual (remainderNormTransport inputs)
    (Matrix.operatorNorm (remainderNormTransport inputs)
      (Matrix.selectedOperator (remainderNormTransport inputs)))
    (T3.εTotal (Five.t3 (fiveChannel inputs)))
remainderOperatorNormBoundInTransportOrder inputs =
  subst
    (λ lower → Matrix.OperatorLessEqual
      (remainderNormTransport inputs) lower
      (T3.εTotal (Five.t3 (fiveChannel inputs))))
    (sym (operatorNormMeaning inputs))
    (subst
      (λ proposition → proposition)
      (sym
        (operatorOrderMeaning inputs
          (FormNorm.operatorNorm
            (Five.normData (fiveChannel inputs))
            (T3.backgroundHessianRemainder
              (Five.t3 (fiveChannel inputs))
              (T3.makeIndex (Five.t3 (fiveChannel inputs))
                (Five.scale (fiveChannel inputs))
                (Five.volume (fiveChannel inputs))
                (Five.regime (fiveChannel inputs))
                (Five.background (fiveChannel inputs)))))
          (T3.εTotal (Five.t3 (fiveChannel inputs)))))
      (Five.t3FiveChannelOperatorNormFromReducedInputs
        (fiveChannel inputs)))

selectedRemainderMatrixNormBelowEpsilonTotal :
  ∀ {n Scale Volume PatchRegime Background Fluctuation Tangent Bound
      MatrixCarrier SpectralIndex}
    (inputs : T3TreeGaugeSpectralDeterminantInputs n
      Scale Volume PatchRegime Background Fluctuation Tangent Bound
      MatrixCarrier SpectralIndex) →
  Matrix.MatrixLessEqual (remainderNormTransport inputs)
    (Matrix.matrixNorm (remainderNormTransport inputs)
      (Matrix.selectedMatrix (remainderNormTransport inputs)))
    (T3.εTotal (Five.t3 (fiveChannel inputs)))
selectedRemainderMatrixNormBelowEpsilonTotal inputs =
  Matrix.matrixNormBoundFromOperatorNormBound
    (remainderNormTransport inputs)
    (T3.εTotal (Five.t3 (fiveChannel inputs)))
    (remainderOperatorNormBoundInTransportOrder inputs)

selectedReferenceInverseNormBelowCoercivityReciprocal :
  ∀ {n Scale Volume PatchRegime Background Fluctuation Tangent Bound
      MatrixCarrier SpectralIndex}
    (inputs : T3TreeGaugeSpectralDeterminantInputs n
      Scale Volume PatchRegime Background Fluctuation Tangent Bound
      MatrixCarrier SpectralIndex) →
  Spectrum.LessEqual
    (Spectrum.rayleigh (Assembly.inverseMeaning (finiteAssembly inputs)))
    (Spectrum.inverseOperatorNorm
      (Assembly.inverseMeaning (finiteAssembly inputs))
      (Assembly.selectedIndex (finiteAssembly inputs)))
    (Spectrum.reciprocal
      (Assembly.inverseMeaning (finiteAssembly inputs))
      (Spectrum.coercivityConstant
        (Spectrum.rayleigh
          (Assembly.inverseMeaning (finiteAssembly inputs)))
        (Assembly.selectedIndex (finiteAssembly inputs))))
selectedReferenceInverseNormBelowCoercivityReciprocal inputs =
  Assembly.assembledInverseNormBelowCoercivityReciprocal
    (finiteAssembly inputs)

selectedPhysicalDeterminantBelowPrimaryMultiplier :
  ∀ {n Scale Volume PatchRegime Background Fluctuation Tangent Bound
      MatrixCarrier SpectralIndex}
    (inputs : T3TreeGaugeSpectralDeterminantInputs n
      Scale Volume PatchRegime Background Fluctuation Tangent Bound
      MatrixCarrier SpectralIndex) →
  Determinant.LessEqual
    (Assembly.determinantData (finiteAssembly inputs))
    (Determinant.determinant
      (Assembly.determinantData (finiteAssembly inputs))
      (Matrix.physicalMatrix
        (Assembly.matrixRepresentation (finiteAssembly inputs))))
    (Determinant.multiply
      (Assembly.determinantData (finiteAssembly inputs))
      (Determinant.determinant
        (Assembly.determinantData (finiteAssembly inputs))
        (Matrix.referenceMatrix
          (Assembly.matrixRepresentation (finiteAssembly inputs))))
      (Determinant.power
        (Assembly.determinantData (finiteAssembly inputs))
        (Determinant.add
          (Assembly.determinantData (finiteAssembly inputs))
          (Determinant.one
            (Assembly.determinantData (finiteAssembly inputs)))
          (Determinant.relativeSize
            (Assembly.determinantData (finiteAssembly inputs))))
        (Determinant.naturalScalar
          (Assembly.determinantData (finiteAssembly inputs))
          (Determinant.dimension
            (Assembly.determinantData (finiteAssembly inputs))))))
selectedPhysicalDeterminantBelowPrimaryMultiplier inputs =
  Assembly.assembledPhysicalDeterminantBelowPrimaryMultiplier
    (finiteAssembly inputs)

t3TreeGaugeCoherentCarrierLevel : ProofLevel
t3TreeGaugeCoherentCarrierLevel = machineChecked

t3RemainderMatrixNormTransportLevel : ProofLevel
t3RemainderMatrixNormTransportLevel = machineChecked

t3ReferenceInverseNormIdentificationLevel : ProofLevel
t3ReferenceInverseNormIdentificationLevel = machineChecked

t3PhysicalDeterminantIdentificationLevel : ProofLevel
t3PhysicalDeterminantIdentificationLevel = machineChecked

physicalTreeGaugeTangentRepresentationInputsLevel : ProofLevel
physicalTreeGaugeTangentRepresentationInputsLevel = conditional

physicalT3MatrixOperatorIdentificationInputsLevel : ProofLevel
physicalT3MatrixOperatorIdentificationInputsLevel = conditional

physicalT3ReferenceSpectrumIdentificationInputsLevel : ProofLevel
physicalT3ReferenceSpectrumIdentificationInputsLevel = conditional

physicalT3DeterminantCarrierIdentificationInputsLevel : ProofLevel
physicalT3DeterminantCarrierIdentificationInputsLevel = conditional
