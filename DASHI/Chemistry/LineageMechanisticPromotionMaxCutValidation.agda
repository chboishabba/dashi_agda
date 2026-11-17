module DASHI.Chemistry.LineageMechanisticPromotionMaxCutValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Chemistry.MolecularMechanisticPromotionLadderExact as Ladder
import DASHI.Chemistry.PAHMechanismStatePromotionExact as PAH

pahReactionPromotedBeyondStoichiometry :
  PAH.reactionIdentityPaid PAH.canonicalPAHMechanisticPromotionBoundary ≡ true
  × PAH.sourceBackedStructurePaid PAH.canonicalPAHMechanisticPromotionBoundary ≡ true
  × PAH.sourceBackedKineticMechanismPaid PAH.canonicalPAHMechanisticPromotionBoundary ≡ true
  × PAH.sourceBackedQMMPESPaid PAH.canonicalPAHMechanisticPromotionBoundary ≡ true
pahReactionPromotedBeyondStoichiometry = refl , (refl , (refl , refl))

pahNumericalWavefunctionNotInvented :
  PAH.numericRealSpaceWavefunctionPaid PAH.canonicalPAHMechanisticPromotionBoundary ≡ false
  × PAH.releasedHamiltonianMatrixPaid PAH.canonicalPAHMechanisticPromotionBoundary ≡ false
pahNumericalWavefunctionNotInvented = refl , refl

mechanisticDepthDoesNotSubstituteForFluxDiscriminator :
  Ladder.mechanisticPromotionPaysCausalFlux Ladder.canonicalMolecularMechanisticPromotionBoundary ≡ false
mechanisticDepthDoesNotSubstituteForFluxDiscriminator = refl

artifactAndPaperAuthorityRemainDistinct :
  Ladder.authorReleasedArtifactEqualsIndependentAuthority Ladder.canonicalMolecularMechanisticPromotionBoundary ≡ false
artifactAndPaperAuthorityRemainDistinct = refl
