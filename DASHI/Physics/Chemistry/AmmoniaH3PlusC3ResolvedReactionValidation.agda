module DASHI.Physics.Chemistry.AmmoniaH3PlusC3ResolvedReactionValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaH3PlusC3ResolvedReactionExact as R

sourceCyclesOriginalAmmoniaHydrogens :
  R.rotateOriginalH R.a ≡ R.b
sourceCyclesOriginalAmmoniaHydrogens = refl

targetKeepsTransferredProtonFixed :
  R.rotateProductAtom R.d ≡ R.d
targetKeepsTransferredProtonFixed = refl

targetCyclesOriginalHydrogens :
  R.rotateProductAtom R.a ≡ R.b
targetCyclesOriginalHydrogens = refl

protonAffinityDifferenceIs4313Tenths :
  R.reactionExothermicityMagnitudeTenthsKJPerMol ≡ 4313
protonAffinityDifferenceIs4313Tenths = refl

sameReactionThermochemistryPaid :
  R.C3ResolvedH3AmmoniaBoundary.sameReactionThermochemicalDifferencePaid
    R.canonicalC3ResolvedH3AmmoniaBoundary ≡ true
sameReactionThermochemistryPaid = refl

resolvedTransitionPaid :
  R.C3ResolvedH3AmmoniaBoundary.fullProofRelevantC3ResolvedReactionTransitionPaid
    R.canonicalC3ResolvedH3AmmoniaBoundary ≡ true
resolvedTransitionPaid = refl

selectedSubgroupNotFullSymmetry :
  R.C3ResolvedH3AmmoniaBoundary.selectedC3EqualsFullProductPointGroup
    R.canonicalC3ResolvedH3AmmoniaBoundary ≡ false
selectedSubgroupNotFullSymmetry = refl
