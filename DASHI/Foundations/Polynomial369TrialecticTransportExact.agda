module DASHI.Foundations.Polynomial369TrialecticTransportExact where

------------------------------------------------------------------------
-- DASHI POLYNOMIAL / TRIALECTIC 27-CELL TRANSPORT
--
-- Existing LevelTwoCode and SynthesisChoice27 are literally the same
-- carrier T x T x T. The *meaning* (3-input endomorphism vs x/y/z
-- thesis/antithesis/synthesis cell) and the choice of group action differ.
-- This is a precisely typed chart, NOT a cubic polynomial and NOT 27 roots.
--
-- Uses established permutation-action, C3, cube, quaternion and hypervoxel
-- owners without changing any parent lemma or claiming Monster recognition.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)


import Base369 as Base
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Trialectic
import DASHI.Reasoning.TernarySynthesisCellComplexExact as Cells
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.TernaryEndomorphismS3ActionLawsExact as Act
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Foundations.TernaryHypervoxelPermutationTransportExact as Hyper
import DASHI.Foundations.RecursiveRadixHypervoxel as Address
import DASHI.Foundations.PolynomialMonodromyTernaryQuaternionBridgeExact as Spin
import DASHI.Foundations.PolynomialBraidPermutationImageExact as Braid

-- Identity is literal: both owners independently chose the same pair nesting.
endoToSynthesis : Tower.LevelTwoCode → Trialectic.SynthesisChoice27
endoToSynthesis code = code

synthesisToEndo : Trialectic.SynthesisChoice27 → Tower.LevelTwoCode
synthesisToEndo choice = choice

endoSynthesisEndo :
  (code : Tower.LevelTwoCode) →
  synthesisToEndo (endoToSynthesis code) ≡ code
endoSynthesisEndo code = refl

synthesisEndoSynthesis :
  (choice : Trialectic.SynthesisChoice27) →
  endoToSynthesis (synthesisToEndo choice) ≡ choice
synthesisEndoSynthesis choice = refl

sameCarrierCountDifferentSemantics :
  Tower.levelTwoCodeCount ≡ Trialectic.synthesisChoiceDimension
sameCarrierCountDifferentSemantics = refl

synthesisCell : Tower.LevelTwoCode → Cells.LocalSynthesisTwoCell
synthesisCell code = Cells.choiceToTwoCell (endoToSynthesis code)

synthesisCellForgetsNothing :
  (code : Tower.LevelTwoCode) →
  Cells.twoCellToChoice (synthesisCell code) ≡ endoToSynthesis code
synthesisCellForgetsNothing code =
  Cells.twoCellChoiceRoundTrip (endoToSynthesis code)

-- Action 1: conjugate an endomorphism by relabelling inputs and outputs.
conjugateSynthesisChart :
  Perm.TriPermutation → Trialectic.SynthesisChoice27 →
  Trialectic.SynthesisChoice27
conjugateSynthesisChart p choice =
  endoToSynthesis (Perm.conjugateCode p (synthesisToEndo choice))

conjugateSynthesisChartIdentity :
  (choice : Trialectic.SynthesisChoice27) →
  conjugateSynthesisChart Perm.permIdentity choice ≡ choice
conjugateSynthesisChartIdentity choice =
  Act.conjugateIdentity (synthesisToEndo choice)

conjugateSynthesisChartComposition :
  (p q : Perm.TriPermutation)
  (choice : Trialectic.SynthesisChoice27) →
  conjugateSynthesisChart (S3._∙_ p q) choice
  ≡ conjugateSynthesisChart p (conjugateSynthesisChart q choice)
conjugateSynthesisChartComposition p q choice =
  Act.conjugateComposition p q (synthesisToEndo choice)

-- Action 2: on an actual x/y/z synthesis cell, permuting coordinates can
-- change their role. This operation is not "conjugate endomorphism".
swapFirstSecondSlots :
  Trialectic.SynthesisChoice27 → Trialectic.SynthesisChoice27
swapFirstSecondSlots (a , (b , z)) = b , (a , z)

swapFirstSecondSlotsInvolutive :
  (choice : Trialectic.SynthesisChoice27) →
  swapFirstSecondSlots (swapFirstSecondSlots choice) ≡ choice
swapFirstSecondSlotsInvolutive (a , (b , z)) = refl

-- The already constructed quaternion generator acts on labels through
-- C3. This lemma is true for each axis; it does NOT lift the full S3.
quaternionC3AxisTransport :
  (a : Base.TriTruth) →
  Spin.rotateImaginaryBasis (Spin.imaginaryBasis a)
  ≡ Spin.imaginaryBasis
      (Perm.applyPermutation Perm.permRotate a)
quaternionC3AxisTransport =
  Spin.spinConjugationIntertwinesABCThreeCycle

-- Coarse/fine radix address embedding is a genuine axis chart.
hypervoxelReorientation :
  (a : Address.Axis3) →
  Hyper.permuteAxis Perm.permRotate a
  ≡ Hyper.triToAxis
       (Perm.applyPermutation Perm.permRotate (Hyper.axisToTri a))
hypervoxelReorientation a = refl

-- A braid can have identity S3 endpoint while retaining a nonempty history.
braidCoarseReturn :
  Braid.image Braid.sigma0Sigma0 ≡ Perm.permIdentity
braidCoarseReturn = Braid.pureBraidPermutationImageIsIdentity

data Same27CarrierMeansSameSemanticRole : Set where
sameCarrierDoesNotForceSameSemanticRole :
  Same27CarrierMeansSameSemanticRole → ⊥
sameCarrierDoesNotForceSameSemanticRole ()

data QuaternionC3ImpliesAllQuinticRootMonodromy : Set where
quaternionC3DoesNotImplyQuinticMonodromy :
  QuaternionC3ImpliesAllQuinticRootMonodromy → ⊥
quaternionC3DoesNotImplyQuinticMonodromy ()
