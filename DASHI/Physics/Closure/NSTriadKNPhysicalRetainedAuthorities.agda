module DASHI.Physics.Closure.NSTriadKNPhysicalRetainedAuthorities where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat using (_≤_; z≤n)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNAdmissibleFourierTriadCarrier as Rich
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as FTClass
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType as FT
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteNatBounds as FTB
import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates as AdvClass
import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType as Adv
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates as TrClass
import DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType as Tr

------------------------------------------------------------------------
-- Physical realization, weight and retained-sector authorities.
--
-- The existing class-specific incidence records contain bounded head, tail and
-- residue coordinates but no interpretation theorem from those coordinates to
-- Fourier modes.  The records below isolate exactly that missing representation
-- data.  Every downstream construction in this module is theorem-producing once
-- these authorities are supplied; no arbitrary Fin-to-mode assignment is made.
------------------------------------------------------------------------

record ConcreteFourierRealization : Set₁ where
  constructor mkConcreteFourierRealization
  field
    forcedTailIncidenceP :
      {c : FTClass.ForcedTailClass} {N : Nat} →
      FT.ForcedTailTriadIncidence c N → Z3.FourierMode
    forcedTailIncidenceQ :
      {c : FTClass.ForcedTailClass} {N : Nat} →
      FT.ForcedTailTriadIncidence c N → Z3.FourierMode
    forcedTailIncidenceK :
      {c : FTClass.ForcedTailClass} {N : Nat} →
      FT.ForcedTailTriadIncidence c N → Z3.FourierMode
    forcedTailIncidenceResonance :
      {c : FTClass.ForcedTailClass} {N : Nat} →
      (τ : FT.ForcedTailTriadIncidence c N) →
      Z3.addMode (forcedTailIncidenceP τ) (forcedTailIncidenceQ τ)
        ≡ forcedTailIncidenceK τ

    adversarialIncidenceP :
      {c : AdvClass.AdversarialClass} {N : Nat} →
      Adv.AdversarialTriadIncidence c N → Z3.FourierMode
    adversarialIncidenceQ :
      {c : AdvClass.AdversarialClass} {N : Nat} →
      Adv.AdversarialTriadIncidence c N → Z3.FourierMode
    adversarialIncidenceK :
      {c : AdvClass.AdversarialClass} {N : Nat} →
      Adv.AdversarialTriadIncidence c N → Z3.FourierMode
    adversarialIncidenceResonance :
      {c : AdvClass.AdversarialClass} {N : Nat} →
      (τ : Adv.AdversarialTriadIncidence c N) →
      Z3.addMode (adversarialIncidenceP τ) (adversarialIncidenceQ τ)
        ≡ adversarialIncidenceK τ

    transitionIncidenceP :
      {c : TrClass.TransitionClass} {N : Nat} →
      Tr.TransitionTriadIncidence c N → Z3.FourierMode
    transitionIncidenceQ :
      {c : TrClass.TransitionClass} {N : Nat} →
      Tr.TransitionTriadIncidence c N → Z3.FourierMode
    transitionIncidenceK :
      {c : TrClass.TransitionClass} {N : Nat} →
      Tr.TransitionTriadIncidence c N → Z3.FourierMode
    transitionIncidenceResonance :
      {c : TrClass.TransitionClass} {N : Nat} →
      (τ : Tr.TransitionTriadIncidence c N) →
      Z3.addMode (transitionIncidenceP τ) (transitionIncidenceQ τ)
        ≡ transitionIncidenceK τ

open ConcreteFourierRealization public

concreteIncidenceP :
  (realization : ConcreteFourierRealization) →
  {N : Nat} →
  Relation.ConcreteNonResidualTriadIncidence N → Z3.FourierMode
concreteIncidenceP realization (Relation.forcedTailIncidence c τ) =
  forcedTailIncidenceP realization τ
concreteIncidenceP realization (Relation.adversarialIncidence c τ) =
  adversarialIncidenceP realization τ
concreteIncidenceP realization (Relation.transitionIncidence c τ) =
  transitionIncidenceP realization τ

concreteIncidenceQ :
  (realization : ConcreteFourierRealization) →
  {N : Nat} →
  Relation.ConcreteNonResidualTriadIncidence N → Z3.FourierMode
concreteIncidenceQ realization (Relation.forcedTailIncidence c τ) =
  forcedTailIncidenceQ realization τ
concreteIncidenceQ realization (Relation.adversarialIncidence c τ) =
  adversarialIncidenceQ realization τ
concreteIncidenceQ realization (Relation.transitionIncidence c τ) =
  transitionIncidenceQ realization τ

concreteIncidenceK :
  (realization : ConcreteFourierRealization) →
  {N : Nat} →
  Relation.ConcreteNonResidualTriadIncidence N → Z3.FourierMode
concreteIncidenceK realization (Relation.forcedTailIncidence c τ) =
  forcedTailIncidenceK realization τ
concreteIncidenceK realization (Relation.adversarialIncidence c τ) =
  adversarialIncidenceK realization τ
concreteIncidenceK realization (Relation.transitionIncidence c τ) =
  transitionIncidenceK realization τ

concreteIncidenceResonance :
  (realization : ConcreteFourierRealization) →
  {N : Nat} →
  (τ : Relation.ConcreteNonResidualTriadIncidence N) →
  Z3.addMode (concreteIncidenceP realization τ)
             (concreteIncidenceQ realization τ)
    ≡ concreteIncidenceK realization τ
concreteIncidenceResonance realization (Relation.forcedTailIncidence c τ) =
  forcedTailIncidenceResonance realization τ
concreteIncidenceResonance realization (Relation.adversarialIncidence c τ) =
  adversarialIncidenceResonance realization τ
concreteIncidenceResonance realization (Relation.transitionIncidence c τ) =
  transitionIncidenceResonance realization τ

record PhysicalTriadWeightAuthority
    (realization : ConcreteFourierRealization) : Set₁ where
  constructor mkPhysicalTriadWeightAuthority
  field
    forcedTailPhysicalTriadWeight :
      {c : FTClass.ForcedTailClass} {N : Nat} →
      FT.ForcedTailTriadIncidence c N → Nat
    adversarialPhysicalTriadWeight :
      {c : AdvClass.AdversarialClass} {N : Nat} →
      Adv.AdversarialTriadIncidence c N → Nat
    transitionPhysicalTriadWeight :
      {c : TrClass.TransitionClass} {N : Nat} →
      Tr.TransitionTriadIncidence c N → Nat

    forcedTailPiFactorBound :
      {c : FTClass.ForcedTailClass} {N : Nat} →
      (τ : FT.ForcedTailTriadIncidence c N) →
      FT.triadPiScaledFactor τ * FTB.forcedTailDenominator c N ≤ suc zero
    forcedTailPositiveCosFactorBound :
      {c : FTClass.ForcedTailClass} {N : Nat} →
      (τ : FT.ForcedTailTriadIncidence c N) →
      FT.cosPositivePartFactor τ ≤ suc zero
    forcedTailScaledWeightFormula :
      {c : FTClass.ForcedTailClass} {N : Nat} →
      (τ : FT.ForcedTailTriadIncidence c N) →
      forcedTailPhysicalTriadWeight τ ≡ FT.actualForcedTailKernelWeight N τ

    adversarialPiFactor :
      {c : AdvClass.AdversarialClass} {N : Nat} →
      Adv.AdversarialTriadIncidence c N → Nat
    adversarialPositiveCosFactor :
      {c : AdvClass.AdversarialClass} {N : Nat} →
      Adv.AdversarialTriadIncidence c N → Nat
    adversarialPiFactorBound :
      {c : AdvClass.AdversarialClass} {N : Nat} →
      (τ : Adv.AdversarialTriadIncidence c N) →
      adversarialPiFactor τ ≤ suc zero
    adversarialPositiveCosFactorBound :
      {c : AdvClass.AdversarialClass} {N : Nat} →
      (τ : Adv.AdversarialTriadIncidence c N) →
      adversarialPositiveCosFactor τ ≤ suc zero
    adversarialScaledWeightFormula :
      {c : AdvClass.AdversarialClass} {N : Nat} →
      (τ : Adv.AdversarialTriadIncidence c N) →
      adversarialPhysicalTriadWeight τ
        ≡ adversarialPiFactor τ * adversarialPositiveCosFactor τ

    transitionPiFactor :
      {c : TrClass.TransitionClass} {N : Nat} →
      Tr.TransitionTriadIncidence c N → Nat
    transitionPositiveCosFactor :
      {c : TrClass.TransitionClass} {N : Nat} →
      Tr.TransitionTriadIncidence c N → Nat
    transitionPiFactorBound :
      {c : TrClass.TransitionClass} {N : Nat} →
      (τ : Tr.TransitionTriadIncidence c N) →
      transitionPiFactor τ ≤ suc zero
    transitionPositiveCosFactorBound :
      {c : TrClass.TransitionClass} {N : Nat} →
      (τ : Tr.TransitionTriadIncidence c N) →
      transitionPositiveCosFactor τ ≤ suc zero
    transitionScaledWeightFormula :
      {c : TrClass.TransitionClass} {N : Nat} →
      (τ : Tr.TransitionTriadIncidence c N) →
      transitionPhysicalTriadWeight τ
        ≡ transitionPiFactor τ * transitionPositiveCosFactor τ

open PhysicalTriadWeightAuthority public

physicalTriadWeight :
  {realization : ConcreteFourierRealization} →
  (weights : PhysicalTriadWeightAuthority realization) →
  {N : Nat} →
  Relation.ConcreteNonResidualTriadIncidence N → Nat
physicalTriadWeight weights (Relation.forcedTailIncidence c τ) =
  forcedTailPhysicalTriadWeight weights τ
physicalTriadWeight weights (Relation.adversarialIncidence c τ) =
  adversarialPhysicalTriadWeight weights τ
physicalTriadWeight weights (Relation.transitionIncidence c τ) =
  transitionPhysicalTriadWeight weights τ

physicalTriadWeightNonnegative :
  {realization : ConcreteFourierRealization} →
  (weights : PhysicalTriadWeightAuthority realization) →
  {N : Nat} →
  (τ : Relation.ConcreteNonResidualTriadIncidence N) →
  zero ≤ physicalTriadWeight weights τ
physicalTriadWeightNonnegative weights τ = z≤n

concreteIncidenceToRetainedTriad :
  (realization : ConcreteFourierRealization) →
  (weights : PhysicalTriadWeightAuthority realization) →
  {N : Nat} →
  Relation.ConcreteNonResidualTriadIncidence N → Rich.RetainedTriad
concreteIncidenceToRetainedTriad realization weights τ =
  Rich.triad
    (concreteIncidenceP realization τ)
    (concreteIncidenceQ realization τ)
    (concreteIncidenceK realization τ)
    (record { closes = concreteIncidenceResonance realization τ })
    (physicalTriadWeight weights τ)

retainedTriadWeightAgreesWithPhysicalFormula :
  (realization : ConcreteFourierRealization) →
  (weights : PhysicalTriadWeightAuthority realization) →
  {N : Nat} →
  (τ : Relation.ConcreteNonResidualTriadIncidence N) →
  Rich.weight (concreteIncidenceToRetainedTriad realization weights τ)
    ≡ physicalTriadWeight weights τ
retainedTriadWeightAgreesWithPhysicalFormula realization weights τ = refl

record PhysicalRetainedSectorPredicates
    (realization : ConcreteFourierRealization)
    (weights : PhysicalTriadWeightAuthority realization) : Set₁ where
  constructor mkPhysicalRetainedSectorPredicates
  field
    shellAdmissible :
      {N : Nat} → Relation.ConcreteNonResidualTriadIncidence N → Set
    nonzeroModes :
      {N : Nat} → Relation.ConcreteNonResidualTriadIncidence N → Set
    positiveSpectralWeight :
      {N : Nat} → Relation.ConcreteNonResidualTriadIncidence N → Set
    phaseCompatible :
      {N : Nat} → Relation.ConcreteNonResidualTriadIncidence N → Set
    parityCompatible :
      {N : Nat} → Relation.ConcreteNonResidualTriadIncidence N → Set
    orientationCompatible :
      {N : Nat} → Relation.ConcreteNonResidualTriadIncidence N → Set

open PhysicalRetainedSectorPredicates public

record PhysicalRetainedPositiveSector
    {realization : ConcreteFourierRealization}
    {weights : PhysicalTriadWeightAuthority realization}
    (predicates : PhysicalRetainedSectorPredicates realization weights)
    {N : Nat}
    (τ : Relation.ConcreteNonResidualTriadIncidence N) : Set where
  constructor retainedPositive
  field
    shellAdmissibleProof : shellAdmissible predicates τ
    nonzeroModesProof : nonzeroModes predicates τ
    positiveSpectralWeightProof : positiveSpectralWeight predicates τ
    phaseCompatibleProof : phaseCompatible predicates τ
    parityCompatibleProof : parityCompatible predicates τ
    orientationCompatibleProof : orientationCompatible predicates τ

record PhysicalRetainedFamilyLanding
    {realization : ConcreteFourierRealization}
    {weights : PhysicalTriadWeightAuthority realization}
    (predicates : PhysicalRetainedSectorPredicates realization weights) : Set₁ where
  constructor mkPhysicalRetainedFamilyLanding
  field
    forcedTailIncidenceRetained :
      {c : FTClass.ForcedTailClass} {N : Nat} →
      (τ : FT.ForcedTailTriadIncidence c N) →
      PhysicalRetainedPositiveSector predicates
        (Relation.forcedTailIncidence c τ)
    adversarialIncidenceRetained :
      {c : AdvClass.AdversarialClass} {N : Nat} →
      (τ : Adv.AdversarialTriadIncidence c N) →
      PhysicalRetainedPositiveSector predicates
        (Relation.adversarialIncidence c τ)
    transitionIncidenceRetained :
      {c : TrClass.TransitionClass} {N : Nat} →
      (τ : Tr.TransitionTriadIncidence c N) →
      PhysicalRetainedPositiveSector predicates
        (Relation.transitionIncidence c τ)

open PhysicalRetainedFamilyLanding public
