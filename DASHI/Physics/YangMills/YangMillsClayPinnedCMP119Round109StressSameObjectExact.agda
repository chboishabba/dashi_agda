{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119Round109StressSameObjectExact where

------------------------------------------------------------------------
-- LITERAL C / ROUND109 COMPLETED MARKED STRESS = PINNED COMMON-CORE STRESS
--
-- Round109 constructs the continuum stress projection from the SAME completed
-- marked RG state and identifies it with the literal Clay stress tensor.
-- The pinned C common-core route separately fixes the stress tensor whose charge
-- closes to the reconstructed OS Hamiltonian.  This owner composes those two
-- same-object equalities so a later inhabitant cannot use a different stress
-- field in the RG completion and Ward/common-core arguments.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as StressMarked
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119StressCommonCoreExact as Common

completedMarkedStressEqualsPinnedCommonCoreStress :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
      sequenceLimit limitLaws quotient division osInputs reconstruction}
    (completion : R109.LiteralSchwingerStressMarkedCompletion Y group)
    (common :
      Common.PinnedStressCommonCoreData
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} {osInputs = osInputs} reconstruction group)
    (literalStressIsPinnedStress :
      DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact.stressTensor Y group
      ≡ Common.stressTensor common) →
  Marked.continuumComposite
    (StressMarked.stressField
      (StressMarked.sameCompletedMarkedSourcesGiveCompositeAndStressFields
        (R109.completedSources completion)))
  ≡ Common.stressTensor common
completedMarkedStressEqualsPinnedCommonCoreStress
    completion common literalStressIsPinnedStress =
  trans
    (R109.literalStressIsCompletedMarkedStress completion)
    literalStressIsPinnedStress

round109StressCompletionToPinnedCommonCoreLevel : ProofLevel
round109StressCompletionToPinnedCommonCoreLevel = machineChecked

-- Physical C residue: supply the Round109 completed-marked stress inhabitant
-- and prove that the literal stress selected there is the stress entering the
-- pinned Ward/common-core construction.
literalCompletedStressPinnedCommonCoreIdentificationLevel : ProofLevel
literalCompletedStressPinnedCommonCoreIdentificationLevel = conditional
