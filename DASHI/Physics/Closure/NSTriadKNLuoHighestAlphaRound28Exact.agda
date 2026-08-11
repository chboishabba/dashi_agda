module DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaRound28Exact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Integrate the highest-alpha exact exports prompted by the Round 28 audit:
--
-- * a commuting dependent physical-carrier selector;
-- * cutoff/output-fibre conjugation orbits;
-- * a finite rational local-Lipschitz majorant for literal Galerkin coordinates;
-- * signed constituent trees with delayed positive taxation;
-- * a dependent unique-owner partition;
-- * signed interaction fibres;
-- * orbit parity and division-free Plucker homogeneity;
-- * a no-hidden-norm owner-tax language;
-- * exact nine-owner critical absorption algebra.
--
-- These results preserve cancellation and make later physical estimates harder
-- to state circularly.  They do not prove continuum-real Picard--Lindelof, the
-- physical shell evolution, any cutoff-uniform owner tax, etaTotal < 1,
-- compactness or the unconditional Clay theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
import Data.Integer.Base as Int
import Data.Rational.Base as Rat

import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNCommutingPhysicalCarrierSelectorRound28Exact as Selector
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadConjugationOrbitRound28Exact as Conjugation
import DASHI.Physics.Closure.NSTriadKNFiniteGalerkinLocalLipschitzRound28Exact as Lipschitz
import DASHI.Physics.Closure.NSTriadKNDependentTaxOwnerPartitionRound28Exact as Partition
import DASHI.Physics.Closure.NSTriadKNSignedInteractionFibreRound28Exact as Interaction
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitSignatureRound28Exact as Orbit
import DASHI.Physics.Closure.NSTriadKNDivisionFreePluckerDefectRound28Exact as Defect
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadPluckerInvariantRound27Exact as Plucker
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as TaxLanguage
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Absorption
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax

record Round28ExactEvidence : Set₁ where
  field
    physicalSelectorIdempotent :
      (State : Set) →
      (selectors : Selector.CommutingPhysicalSelectors State) →
      (state : State) →
      Selector.physicalSelector selectors
        (Selector.physicalSelector selectors state)
      ≡ Selector.physicalSelector selectors state

    conjugateOutputFibre :
      ∀ {cutoff output triad} →
      triad Cube.∈ Output.physicalOutputFiber cutoff output →
      Conjugation.ConjugateOutputFiberWitness cutoff output triad

    finiteRationalLocalLipschitz :
      Lipschitz.finiteRationalLocalLipschitzMajorantClosed ≡ true

    dependentOwnerPartitionRoundtrip :
      (atoms : List Tax.TaxAtom) →
      Partition.eraseTaggedTaxAtoms (Partition.tagTaxAtoms atoms)
      ≡ atoms

    signedInteractionFibre :
      (fibre : List Interaction.SignedInteractionCell) →
      Interaction.interactionFibreCommutator fibre
      ≡ Interaction.interactionFibreSignedDifference fibre

    orbitAreaInvariant :
      (action : Orbit.TriadOrbitAction) →
      (triad : Physical.PhysicalTriadIncidence) →
      Plucker.pluckerNormSquared
        (Physical.p (Orbit.act action triad))
        (Physical.q (Orbit.act action triad))
      ≡
      Plucker.pluckerNormSquared
        (Physical.p triad) (Physical.q triad)

    divisionFreePluckerScaling :
      ∀ leftScale rightScale left right →
      Plucker.pluckerNormSquared
        (Defect.scaleMode leftScale left)
        (Defect.scaleMode rightScale right)
      ≡
      Int._*_
        (Int._*_
          (Int._*_ leftScale rightScale)
          (Int._*_ leftScale rightScale))
        (Plucker.pluckerNormSquared left right)

    nineOwnerAggregate :
      ∀ {environment}
        (family : TaxLanguage.NineOwnerEstimateFamily environment) →
      Rat._≤_
        (TaxLanguage.sumProduction (TaxLanguage.nineOwnerList family))
        (TaxLanguage.admissibleAggregateRight
          (TaxLanguage.nineOwnerList family))

    positiveRemainingViscosity :
      (balance : Absorption.NineOwnerCriticalBalance) →
      Rat._<_ Rat.0ℚ (Absorption.remainingViscosity balance)

    strictNineOwnerAbsorption :
      (balance : Absorption.NineOwnerCriticalBalance) →
      Rat._≤_
        (Rat._+_
          (Absorption.energyOut balance)
          (Rat._*_
            (Absorption.remainingViscosity balance)
            (TaxLanguage.dissipation (Absorption.environment balance))))
        (Rat._+_
          (Absorption.energyIn balance)
          (Absorption.admissibleRemainder balance))

open Round28ExactEvidence public

canonicalRound28ExactEvidence : Round28ExactEvidence
canonicalRound28ExactEvidence = record
  { physicalSelectorIdempotent =
      λ State selectors state →
        Selector.physicalSelectorIdempotent selectors state
  ; conjugateOutputFibre = Conjugation.conjugateOutputFiberWitness
  ; finiteRationalLocalLipschitz =
      Lipschitz.finiteRationalLocalLipschitzMajorantClosedIsTrue
  ; dependentOwnerPartitionRoundtrip =
      Partition.dependentPartitionListRoundtrip
  ; signedInteractionFibre = Interaction.interactionFibreSignedIdentity
  ; orbitAreaInvariant = Orbit.orbitSquaredAreaInvariant
  ; divisionFreePluckerScaling = Defect.pluckerNormScale
  ; nineOwnerAggregate = TaxLanguage.nineOwnerAggregateBound
  ; positiveRemainingViscosity =
      Absorption.nineOwnerRemainingViscosityPositive
  ; strictNineOwnerAbsorption = Absorption.nineOwnerStrictCriticalEstimate
  }

record Round28HighestAlphaBoundary : Set where
  constructor round28-highest-alpha-boundary
  field
    genericPhysicalSelectorClosed : Bool
    concretePhysicalSelectorInstantiated : Bool
    conjugateOutputFibreClosed : Bool
    fullNonlinearRealityEquivariance : Bool
    finiteRationalCoordinateLipschitz : Bool
    continuumRealNormedPicardLindelof : Bool
    constituentTreePreservesSign : Bool
    dependentOwnerPartitionClosed : Bool
    signedInteractionFibreClosed : Bool
    cutoffUniformTStarTBound : Bool
    orbitParityClosed : Bool
    divisionFreePluckerScalingClosed : Bool
    admissibleTaxLanguageClosed : Bool
    nineOwnerAbsorptionAlgebraClosed : Bool
    physicalNineOwnerEstimates : Bool
    strictTotalViscosityMargin : Bool
    finiteGlobalGalerkinFlow : Bool
    physicalTimeDependentShellBalance : Bool
    shellAndGalerkinLimits : Bool
    unconditionalClayTheorem : Bool

open Round28HighestAlphaBoundary public

canonicalRound28HighestAlphaBoundary : Round28HighestAlphaBoundary
canonicalRound28HighestAlphaBoundary =
  round28-highest-alpha-boundary
    true false true false
    true false
    true true true false
    true true true true
    false false false false false false

physicalSelectorInstanceStillOpen :
  concretePhysicalSelectorInstantiated canonicalRound28HighestAlphaBoundary
  ≡ false
physicalSelectorInstanceStillOpen = refl

nonlinearRealityStillOpen :
  fullNonlinearRealityEquivariance canonicalRound28HighestAlphaBoundary
  ≡ false
nonlinearRealityStillOpen = refl

continuumPicardLindelofStillOpen :
  continuumRealNormedPicardLindelof canonicalRound28HighestAlphaBoundary
  ≡ false
continuumPicardLindelofStillOpen = refl

uniformOperatorTaxStillOpen :
  cutoffUniformTStarTBound canonicalRound28HighestAlphaBoundary
  ≡ false
uniformOperatorTaxStillOpen = refl

strictMarginStillOpen :
  strictTotalViscosityMargin canonicalRound28HighestAlphaBoundary
  ≡ false
strictMarginStillOpen = refl

clayPromotionStillFalse :
  unconditionalClayTheorem canonicalRound28HighestAlphaBoundary
  ≡ false
clayPromotionStillFalse = refl
