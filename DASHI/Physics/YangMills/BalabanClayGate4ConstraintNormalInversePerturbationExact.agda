module DASHI.Physics.YangMills.BalabanClayGate4ConstraintNormalInversePerturbationExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4ResolventDefectPipelineExact as Resolvent

------------------------------------------------------------------------
-- Normal inverse perturbation for Q Q*.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics (1995 reprint).
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- The physical normal operator is not proved positive from scratch. It is
-- compared with the exactly controlled reference normal operator, and its
-- inverse defect is obtained from the second resolvent identity.
------------------------------------------------------------------------

record ConstraintNormalInversePerturbation
    (Operator Bound : Set) : Set₁ where
  field
    algebra : Resolvent.ResolventNormAlgebra Operator Bound

    referenceNormal physicalNormal normalPerturbation : Operator
    referenceInverse physicalInverse inverseDifference : Operator

    normalPerturbationIdentification : Set
    normalPerturbationIdentificationEvidence :
      normalPerturbationIdentification

    inverseDifferenceMeaning :
      inverseDifference
      ≡ Resolvent.subtract algebra physicalInverse referenceInverse

    secondResolventIdentity :
      inverseDifference
      ≡ Resolvent.negate algebra
          (Resolvent.compose algebra physicalInverse
            (Resolvent.compose algebra normalPerturbation referenceInverse))

    physicalInverseBound perturbationBound referenceInverseBound
      inverseDifferenceBudget : Bound

    physicalInverseEstimate :
      Resolvent.LessEqual algebra
        (Resolvent.operatorNorm algebra physicalInverse)
        physicalInverseBound

    perturbationEstimate :
      Resolvent.LessEqual algebra
        (Resolvent.operatorNorm algebra normalPerturbation)
        perturbationBound

    referenceInverseEstimate :
      Resolvent.LessEqual algebra
        (Resolvent.operatorNorm algebra referenceInverse)
        referenceInverseBound

    inverseDifferenceBudgetMeaning :
      inverseDifferenceBudget
      ≡ Resolvent.multiply algebra physicalInverseBound
          (Resolvent.multiply algebra perturbationBound referenceInverseBound)

open ConstraintNormalInversePerturbation public

asResolventIdentityData :
  ∀ {Operator Bound} →
  ConstraintNormalInversePerturbation Operator Bound →
  Resolvent.ResolventIdentityData Operator Bound
asResolventIdentityData dataSet = record
  { Resolvent.ResolventIdentityData.algebra = algebra dataSet
  ; Resolvent.ResolventIdentityData.referenceInverse =
      referenceInverse dataSet
  ; Resolvent.ResolventIdentityData.perturbedInverse =
      physicalInverse dataSet
  ; Resolvent.ResolventIdentityData.perturbation =
      normalPerturbation dataSet
  ; Resolvent.ResolventIdentityData.difference =
      inverseDifference dataSet
  ; Resolvent.ResolventIdentityData.differenceMeaning =
      inverseDifferenceMeaning dataSet
  ; Resolvent.ResolventIdentityData.secondResolventIdentity =
      secondResolventIdentity dataSet
  ; Resolvent.ResolventIdentityData.perturbedInverseBound =
      physicalInverseBound dataSet
  ; Resolvent.ResolventIdentityData.perturbationBound =
      perturbationBound dataSet
  ; Resolvent.ResolventIdentityData.referenceInverseBound =
      referenceInverseBound dataSet
  ; Resolvent.ResolventIdentityData.differenceBudget =
      inverseDifferenceBudget dataSet
  ; Resolvent.ResolventIdentityData.perturbedInverseEstimate =
      physicalInverseEstimate dataSet
  ; Resolvent.ResolventIdentityData.perturbationEstimate =
      perturbationEstimate dataSet
  ; Resolvent.ResolventIdentityData.referenceInverseEstimate =
      referenceInverseEstimate dataSet
  ; Resolvent.ResolventIdentityData.differenceBudgetMeaning =
      inverseDifferenceBudgetMeaning dataSet
  }

constraintNormalInverseDifferenceBound :
  ∀ {Operator Bound}
    (dataSet : ConstraintNormalInversePerturbation Operator Bound) →
  Resolvent.LessEqual (algebra dataSet)
    (Resolvent.operatorNorm (algebra dataSet)
      (inverseDifference dataSet))
    (inverseDifferenceBudget dataSet)
constraintNormalInverseDifferenceBound dataSet =
  Resolvent.resolventDifferenceNormBelowBudget
    (asResolventIdentityData dataSet)

constraintNormalResolventAssemblyLevel : ProofLevel
constraintNormalResolventAssemblyLevel = machineChecked

constraintNormalInverseDifferenceBoundLevel : ProofLevel
constraintNormalInverseDifferenceBoundLevel = machineChecked

physicalConstraintNormalPerturbationInputsLevel : ProofLevel
physicalConstraintNormalPerturbationInputsLevel = conditional

physicalConstraintInverseBoundsInputsLevel : ProofLevel
physicalConstraintInverseBoundsInputsLevel = conditional
