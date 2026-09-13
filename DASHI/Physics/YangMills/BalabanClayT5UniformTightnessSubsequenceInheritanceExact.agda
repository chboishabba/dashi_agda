{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5UniformTightnessSubsequenceInheritanceExact where

------------------------------------------------------------------------
-- UNIFORM TIGHTNESS OF ONE SELECTED SEQUENCE -> EVERY LITERAL SUBSEQUENCE
--
-- Round195 correctly asked for tightness of every literal subsequence before
-- invoking Prokhorov.  That quantifier is not a new physical estimate when the
-- selected sequence already has one uniform tightness certificate: the same
-- epsilon-dependent compact witness works after restricting the index set.
--
-- This module makes that restriction argument definitionally explicit.  It does
-- not prove the Yang--Mills moment/tail estimate which supplies the selected
-- uniform tightness certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as CompactUnique
import DASHI.Physics.YangMills.BalabanClayT5SubsequenceProkhorovExtractionExact as Prokhorov

------------------------------------------------------------------------
-- Abstract but genuinely uniform tightness certificate.
--
-- `Witness` can be instantiated by compact sets (or the repository's chosen
-- compact-containment carrier).  For every epsilon, one witness controls every
-- member of the selected sequence.  The crucial quantifier order is therefore
--
--     forall epsilon, exists K_epsilon, forall n, Controls epsilon K_epsilon mu_n
--
-- rather than a separate compact witness for every n.
------------------------------------------------------------------------

record UniformTightnessCertificate
    (Measure Epsilon Witness : Set)
    (Admissible : Epsilon → Witness → Set)
    (Controls : Epsilon → Witness → Measure → Set)
    (sequence : Nat → Measure) : Set where
  field
    witness : Epsilon → Witness
    witnessAdmissible : ∀ epsilon → Admissible epsilon (witness epsilon)
    controlsAll : ∀ epsilon n →
      Controls epsilon (witness epsilon) (sequence n)

open UniformTightnessCertificate public

restrictUniformTightnessToSubsequence :
  ∀ {Measure Epsilon Witness}
    {Admissible : Epsilon → Witness → Set}
    {Controls : Epsilon → Witness → Measure → Set}
    {sequence : Nat → Measure} →
  UniformTightnessCertificate
    Measure Epsilon Witness Admissible Controls sequence →
  (subsequence : CompactUnique.SubsequenceWitness sequence) →
  UniformTightnessCertificate
    Measure Epsilon Witness Admissible Controls
    (CompactUnique.values subsequence)
restrictUniformTightnessToSubsequence certificate subsequence = record
  { witness = witness certificate
  ; witnessAdmissible = witnessAdmissible certificate
  ; controlsAll = λ epsilon n →
      controlsAll certificate epsilon (CompactUnique.indices subsequence n)
  }

------------------------------------------------------------------------
-- Adapter to the Round195 Prokhorov surface.
------------------------------------------------------------------------

record SelectedPhysicalUniformTightnessInputs
    (Measure Epsilon Witness : Set) : Set₁ where
  field
    convergence : Limit.SequentialLimit Measure
    sequence : Nat → Measure

    Admissible : Epsilon → Witness → Set
    Controls : Epsilon → Witness → Measure → Set

    -- This is the only physical tightness leaf on the preferred route.
    selectedSequenceUniformlyTight :
      UniformTightnessCertificate
        Measure Epsilon Witness Admissible Controls sequence

open SelectedPhysicalUniformTightnessInputs public

compilePhysicalSubsequenceTightnessData :
  ∀ {Measure Epsilon Witness} →
  SelectedPhysicalUniformTightnessInputs Measure Epsilon Witness →
  Prokhorov.PhysicalSubsequenceTightnessData Measure
compilePhysicalSubsequenceTightnessData inputs = record
  { convergence = convergence inputs
  ; sequence = sequence inputs
  ; TightMeasureSequence =
      UniformTightnessCertificate
        _ _ _ (Admissible inputs) (Controls inputs)
  ; everyLiteralSubsequenceTight = λ subsequence →
      restrictUniformTightnessToSubsequence
        (selectedSequenceUniformlyTight inputs) subsequence
  }

uniformTightnessSubsequenceRestrictionLevel : ProofLevel
uniformTightnessSubsequenceRestrictionLevel = machineChecked

selectedPhysicalSequenceUniformTightnessLevel : ProofLevel
selectedPhysicalSequenceUniformTightnessLevel = conditional
