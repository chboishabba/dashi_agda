module DASHI.Physics.Plasma.MHDMomentumInductionElsasserAmplitudeWeldBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ElsasserAmplitudeRechartAlgebraExact as Algebra
import DASHI.Physics.Plasma.ElsasserSectorSelectionBidiExact as Selection
import DASHI.Physics.Plasma.MHDHelicalElsasserTriadHypervoxelExact as V
import DASHI.Physics.Plasma.MHDMomentumCommutatorAfterElsasserBidiExact as Momentum
import DASHI.Physics.Plasma.MHDInductionResidualConsumerBidiExact as Induction

------------------------------------------------------------------------
-- SAME-SUPPORT / DIFFERENT-COMBINATION WELD
--
-- Momentum and induction live on the same surviving Elsasser support:
--   (+,-) and (-,+).
-- But momentum uses the symmetric mixed combination, whereas induction uses
-- the antisymmetric mixed combination.  Same support therefore does not imply
-- same amplitude or same cancellation theorem.
------------------------------------------------------------------------

record MixedElsasserSupport : Set where
  constructor mixed-elsasser-support
  field
    plusMinusSurvives : Selection.SurvivesElsasserAmplitude Selection.plusMinus
    minusPlusSurvives : Selection.SurvivesElsasserAmplitude Selection.minusPlus

canonicalMixedElsasserSupport : MixedElsasserSupport
canonicalMixedElsasserSupport =
  mixed-elsasser-support
    Selection.plusMinusSurvives
    Selection.minusPlusSurvives

record MomentumAmplitudeWeld
    (voxel : V.MHDHelicalElsasserTriadHypervoxel) : Set₁ where
  constructor momentum-amplitude-weld
  field
    momentumReceipt : Momentum.ElsasserMomentumCommutatorReceipt voxel
    support : MixedElsasserSupport
    physicalAmplitudeIsUUminusBB : Set
    exactSymmetricMixedElsasserIdentity : Set
    sameTriadSameSlotOrdering : Set
    weldReference : String

open MomentumAmplitudeWeld public

record InductionAmplitudeWeld
    (voxel : V.MHDHelicalElsasserTriadHypervoxel) : Set₁ where
  constructor induction-amplitude-weld
  field
    inductionReceipt : Induction.InductionResidualReceipt voxel
    support : MixedElsasserSupport
    physicalAmplitudeIsUBminusBU : Set
    exactAntisymmetricMixedElsasserIdentity : Set
    sameTriadSameSlotOrdering : Set
    weldReference : String

open InductionAmplitudeWeld public

record SharedSupportDifferentCombinationBoundary : Set where
  constructor shared-support-different-combination-boundary
  field
    momentumAndInductionShareElsasserSupport : Bool
    momentumAndInductionShareElsasserSupportIsTrue :
      momentumAndInductionShareElsasserSupport ≡ true

    sharedSupportImpliesSameAmplitudeCombination : Bool
    sharedSupportImpliesSameAmplitudeCombinationIsFalse :
      sharedSupportImpliesSameAmplitudeCombination ≡ false

    symmetricMomentumIdentityClosesAntisymmetricInductionResidual : Bool
    symmetricMomentumIdentityClosesAntisymmetricInductionResidualIsFalse :
      symmetricMomentumIdentityClosesAntisymmetricInductionResidual ≡ false

    exactAmplitudeAlgebraRemovesSameSignSectorProducts : Bool
    exactAmplitudeAlgebraRemovesSameSignSectorProductsIsTrue :
      exactAmplitudeAlgebraRemovesSameSignSectorProducts ≡ true

canonicalSharedSupportDifferentCombinationBoundary :
  SharedSupportDifferentCombinationBoundary
canonicalSharedSupportDifferentCombinationBoundary =
  shared-support-different-combination-boundary
    true refl
    false refl
    false refl
    true refl
