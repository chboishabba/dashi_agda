module DASHI.Physics.Closure.NSTriadKNPhysicalClassEncoding where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalStage3Allocation as Allocation
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedAuthorities as Legacy
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as FTClass
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType as FT
import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates as AdvClass
import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType as Adv
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates as TrClass
import DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType as Tr

------------------------------------------------------------------------
-- Canonical physical coefficient.
--
-- The kernel weight is not introduced as a second independent ansatz.  It is
-- defined as the positive part of the exact coefficient produced by the chosen
-- Fourier/polarisation/profile conventions.  Phase-cosine or class-envelope
-- formulae are downstream theorems about this one definition.
------------------------------------------------------------------------

record PhysicalWeightDerivation (PhysicalState : Set) : Set₁ where
  constructor physical-weight-derivation
  field
    RawCoefficient : Set
    rawFourierCoefficient : PhysicalState → RawCoefficient
    positivePart : RawCoefficient → Nat

open PhysicalWeightDerivation public

physicalWeight :
  ∀ {PhysicalState} →
  PhysicalWeightDerivation PhysicalState →
  PhysicalState → Nat
physicalWeight derivation state =
  positivePart derivation (rawFourierCoefficient derivation state)

record PhysicalPhaseEnvelope
    {PhysicalState : Set}
    (derivation : PhysicalWeightDerivation PhysicalState) : Set₁ where
  constructor physical-phase-envelope
  field
    amplitudeFactor positivePhaseFactor : PhysicalState → Nat
    exactPositivePhaseFormula :
      ∀ state →
      physicalWeight derivation state
      ≡ amplitudeFactor state * positivePhaseFactor state
    positivePhaseFactorBound :
      ∀ state → positivePhaseFactor state ≤ 1

open PhysicalPhaseEnvelope public

------------------------------------------------------------------------
-- Physical retained incidences <-> canonical existing finite coordinates.
------------------------------------------------------------------------

physicalIncidenceOf :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N} →
  Allocation.RetainedPhysicalTriad retainedPolicy →
  Physical.PhysicalTriadIncidence
physicalIncidenceOf τ =
  Allocation.incidence (Allocation.state τ)

record SameLatticeTriad
    (left right : Physical.PhysicalTriadIncidence) : Set where
  constructor same-lattice-triad
  field
    sameP : Physical.p left ≡ Physical.p right
    sameQ : Physical.q left ≡ Physical.q right
    sameK : Physical.k left ≡ Physical.k right

open SameLatticeTriad public

record PhysicalStage3Representation
    {carrier : Allocation.TriadStateCarrier}
    {N : Nat}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    (geometry : Allocation.Stage3GeometricPredicates retainedPolicy)
    (weightDerivation :
      PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)) : Set₁ where
  constructor physical-stage3-representation
  field
    CodeValid :
      Relation.ConcreteNonResidualTriadIncidence N → Set

    encode :
      (τ : Allocation.RetainedPhysicalTriad retainedPolicy) →
      Allocation.NonResidualAllocation geometry τ →
      Relation.ConcreteNonResidualTriadIncidence N

    encodeValid :
      (τ : Allocation.RetainedPhysicalTriad retainedPolicy) →
      (allocation : Allocation.NonResidualAllocation geometry τ) →
      CodeValid (encode τ allocation)

    decode :
      (code : Relation.ConcreteNonResidualTriadIncidence N) →
      CodeValid code →
      Allocation.RetainedPhysicalTriad retainedPolicy

    decodedNonResidual :
      (code : Relation.ConcreteNonResidualTriadIncidence N) →
      (valid : CodeValid code) →
      Allocation.NonResidualAllocation geometry (decode code valid)

    decodeEncodeSamePhysical :
      (τ : Allocation.RetainedPhysicalTriad retainedPolicy) →
      (allocation : Allocation.NonResidualAllocation geometry τ) →
      SameLatticeTriad
        (physicalIncidenceOf
          (decode
            (encode τ allocation)
            (encodeValid τ allocation)))
        (physicalIncidenceOf τ)

    encodeDecodeCanonical :
      (code : Relation.ConcreteNonResidualTriadIncidence N) →
      (valid : CodeValid code) →
      encode
        (decode code valid)
        (decodedNonResidual code valid)
      ≡ code

    physicalSource :
      (τ : Allocation.RetainedPhysicalTriad retainedPolicy) →
      Allocation.NonResidualAllocation geometry τ →
      Relation.ConcreteNonResidualFiniteIndex N

    physicalTarget :
      (τ : Allocation.RetainedPhysicalTriad retainedPolicy) →
      Allocation.NonResidualAllocation geometry τ →
      Relation.ConcreteNonResidualTailIndex N

    sourcePreserved :
      (τ : Allocation.RetainedPhysicalTriad retainedPolicy) →
      (allocation : Allocation.NonResidualAllocation geometry τ) →
      Relation.concreteNonResidualSourceIndex (encode τ allocation)
      ≡ physicalSource τ allocation

    targetPreserved :
      (τ : Allocation.RetainedPhysicalTriad retainedPolicy) →
      (allocation : Allocation.NonResidualAllocation geometry τ) →
      Relation.concreteNonResidualTargetIndex (encode τ allocation)
      ≡ physicalTarget τ allocation

    abstractCodeWeight :
      Relation.ConcreteNonResidualTriadIncidence N → Nat

    physicalWeightPreserved :
      (τ : Allocation.RetainedPhysicalTriad retainedPolicy) →
      (allocation : Allocation.NonResidualAllocation geometry τ) →
      abstractCodeWeight (encode τ allocation)
      ≡ physicalWeight weightDerivation τ

open PhysicalStage3Representation public

------------------------------------------------------------------------
-- The old code->mode authority is now a derived projection, but only after
-- every existing finite coordinate is proved physically valid.  This is the
-- precise anti-cheating boundary: no arbitrary Fin -> FourierMode map can be
-- inserted.
------------------------------------------------------------------------

record ExistingClassCoordinatesArePhysical
    {carrier : Allocation.TriadStateCarrier}
    {N : Nat}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    {weightDerivation :
      PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)}
    (representation :
      PhysicalStage3Representation geometry weightDerivation) : Set₁ where
  constructor existing-coordinates-physical
  field
    allCodesValid :
      (code : Relation.ConcreteNonResidualTriadIncidence N) →
      CodeValid representation code

open ExistingClassCoordinatesArePhysical public

decodedPhysicalIncidence :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    {weightDerivation :
      PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)}
    (representation :
      PhysicalStage3Representation geometry weightDerivation) →
    ExistingClassCoordinatesArePhysical representation →
    Relation.ConcreteNonResidualTriadIncidence N →
    Physical.PhysicalTriadIncidence
decodedPhysicalIncidence representation coverage code =
  physicalIncidenceOf
    (decode representation code (allCodesValid coverage code))

record ConcreteFourierRealizationAt (N : Nat) : Set₁ where
  constructor concrete-fourier-realization-at
  field
    forcedTailP :
      {c : FTClass.ForcedTailClass} →
      FT.ForcedTailTriadIncidence c N → Z3.FourierMode
    forcedTailQ :
      {c : FTClass.ForcedTailClass} →
      FT.ForcedTailTriadIncidence c N → Z3.FourierMode
    forcedTailK :
      {c : FTClass.ForcedTailClass} →
      FT.ForcedTailTriadIncidence c N → Z3.FourierMode
    forcedTailResonance :
      {c : FTClass.ForcedTailClass} →
      (τ : FT.ForcedTailTriadIncidence c N) →
      Z3.addMode (forcedTailP τ) (forcedTailQ τ) ≡ forcedTailK τ

    adversarialP :
      {c : AdvClass.AdversarialClass} →
      Adv.AdversarialTriadIncidence c N → Z3.FourierMode
    adversarialQ :
      {c : AdvClass.AdversarialClass} →
      Adv.AdversarialTriadIncidence c N → Z3.FourierMode
    adversarialK :
      {c : AdvClass.AdversarialClass} →
      Adv.AdversarialTriadIncidence c N → Z3.FourierMode
    adversarialResonance :
      {c : AdvClass.AdversarialClass} →
      (τ : Adv.AdversarialTriadIncidence c N) →
      Z3.addMode (adversarialP τ) (adversarialQ τ) ≡ adversarialK τ

    transitionP :
      {c : TrClass.TransitionClass} →
      Tr.TransitionTriadIncidence c N → Z3.FourierMode
    transitionQ :
      {c : TrClass.TransitionClass} →
      Tr.TransitionTriadIncidence c N → Z3.FourierMode
    transitionK :
      {c : TrClass.TransitionClass} →
      Tr.TransitionTriadIncidence c N → Z3.FourierMode
    transitionResonance :
      {c : TrClass.TransitionClass} →
      (τ : Tr.TransitionTriadIncidence c N) →
      Z3.addMode (transitionP τ) (transitionQ τ) ≡ transitionK τ

open ConcreteFourierRealizationAt public

representationToConcreteFourierRealizationAt :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    {weightDerivation :
      PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)}
    (representation :
      PhysicalStage3Representation geometry weightDerivation) →
    ExistingClassCoordinatesArePhysical representation →
    ConcreteFourierRealizationAt N
representationToConcreteFourierRealizationAt representation coverage =
  concrete-fourier-realization-at
    forcedP forcedQ forcedK forcedResonance
    adversarialP adversarialQ adversarialK adversarialResonance
    transitionP transitionQ transitionK transitionResonance
  where
  decoded :
    Relation.ConcreteNonResidualTriadIncidence N →
    Physical.PhysicalTriadIncidence
  decoded = decodedPhysicalIncidence representation coverage

  forcedCode :
    {c : FTClass.ForcedTailClass} →
    FT.ForcedTailTriadIncidence c N →
    Relation.ConcreteNonResidualTriadIncidence N
  forcedCode {c} τ = Relation.forcedTailIncidence c τ

  forcedP :
    {c : FTClass.ForcedTailClass} →
    FT.ForcedTailTriadIncidence c N → Z3.FourierMode
  forcedP τ = Physical.p (decoded (forcedCode τ))

  forcedQ :
    {c : FTClass.ForcedTailClass} →
    FT.ForcedTailTriadIncidence c N → Z3.FourierMode
  forcedQ τ = Physical.q (decoded (forcedCode τ))

  forcedK :
    {c : FTClass.ForcedTailClass} →
    FT.ForcedTailTriadIncidence c N → Z3.FourierMode
  forcedK τ = Physical.k (decoded (forcedCode τ))

  forcedResonance :
    {c : FTClass.ForcedTailClass} →
    (τ : FT.ForcedTailTriadIncidence c N) →
    Z3.addMode (forcedP τ) (forcedQ τ) ≡ forcedK τ
  forcedResonance τ = Physical.resonance (decoded (forcedCode τ))

  adversarialCode :
    {c : AdvClass.AdversarialClass} →
    Adv.AdversarialTriadIncidence c N →
    Relation.ConcreteNonResidualTriadIncidence N
  adversarialCode {c} τ = Relation.adversarialIncidence c τ

  adversarialP :
    {c : AdvClass.AdversarialClass} →
    Adv.AdversarialTriadIncidence c N → Z3.FourierMode
  adversarialP τ = Physical.p (decoded (adversarialCode τ))

  adversarialQ :
    {c : AdvClass.AdversarialClass} →
    Adv.AdversarialTriadIncidence c N → Z3.FourierMode
  adversarialQ τ = Physical.q (decoded (adversarialCode τ))

  adversarialK :
    {c : AdvClass.AdversarialClass} →
    Adv.AdversarialTriadIncidence c N → Z3.FourierMode
  adversarialK τ = Physical.k (decoded (adversarialCode τ))

  adversarialResonance :
    {c : AdvClass.AdversarialClass} →
    (τ : Adv.AdversarialTriadIncidence c N) →
    Z3.addMode (adversarialP τ) (adversarialQ τ)
    ≡ adversarialK τ
  adversarialResonance τ =
    Physical.resonance (decoded (adversarialCode τ))

  transitionCode :
    {c : TrClass.TransitionClass} →
    Tr.TransitionTriadIncidence c N →
    Relation.ConcreteNonResidualTriadIncidence N
  transitionCode {c} τ = Relation.transitionIncidence c τ

  transitionP :
    {c : TrClass.TransitionClass} →
    Tr.TransitionTriadIncidence c N → Z3.FourierMode
  transitionP τ = Physical.p (decoded (transitionCode τ))

  transitionQ :
    {c : TrClass.TransitionClass} →
    Tr.TransitionTriadIncidence c N → Z3.FourierMode
  transitionQ τ = Physical.q (decoded (transitionCode τ))

  transitionK :
    {c : TrClass.TransitionClass} →
    Tr.TransitionTriadIncidence c N → Z3.FourierMode
  transitionK τ = Physical.k (decoded (transitionCode τ))

  transitionResonance :
    {c : TrClass.TransitionClass} →
    (τ : Tr.TransitionTriadIncidence c N) →
    Z3.addMode (transitionP τ) (transitionQ τ) ≡ transitionK τ
  transitionResonance τ =
    Physical.resonance (decoded (transitionCode τ))

record UniformPhysicalRealization : Set₁ where
  constructor uniform-physical-realization
  field
    realizationAt : (N : Nat) → ConcreteFourierRealizationAt N

open UniformPhysicalRealization public

uniformPhysicalRealizationToLegacy :
  UniformPhysicalRealization → Legacy.ConcreteFourierRealization
uniformPhysicalRealizationToLegacy family =
  Legacy.mkConcreteFourierRealization
    (λ {c} {N} τ → forcedTailP (realizationAt family N) τ)
    (λ {c} {N} τ → forcedTailQ (realizationAt family N) τ)
    (λ {c} {N} τ → forcedTailK (realizationAt family N) τ)
    (λ {c} {N} τ → forcedTailResonance (realizationAt family N) τ)
    (λ {c} {N} τ → adversarialP (realizationAt family N) τ)
    (λ {c} {N} τ → adversarialQ (realizationAt family N) τ)
    (λ {c} {N} τ → adversarialK (realizationAt family N) τ)
    (λ {c} {N} τ → adversarialResonance (realizationAt family N) τ)
    (λ {c} {N} τ → transitionP (realizationAt family N) τ)
    (λ {c} {N} τ → transitionQ (realizationAt family N) τ)
    (λ {c} {N} τ → transitionK (realizationAt family N) τ)
    (λ {c} {N} τ → transitionResonance (realizationAt family N) τ)

physicalFirstRepresentationSurfaceImplemented : Bool
physicalFirstRepresentationSurfaceImplemented = true

physicalFirstRepresentationSurfaceImplementedIsTrue :
  physicalFirstRepresentationSurfaceImplemented ≡ true
physicalFirstRepresentationSurfaceImplementedIsTrue = refl

legacyRealizationDerivedOnlyFromPhysicalDecode : Bool
legacyRealizationDerivedOnlyFromPhysicalDecode = true

legacyRealizationDerivedOnlyFromPhysicalDecodeIsTrue :
  legacyRealizationDerivedOnlyFromPhysicalDecode ≡ true
legacyRealizationDerivedOnlyFromPhysicalDecodeIsTrue = refl

physicalClassEncodingInhabited : Bool
physicalClassEncodingInhabited = false

physicalClassEncodingInhabitedIsFalse :
  physicalClassEncodingInhabited ≡ false
physicalClassEncodingInhabitedIsFalse = refl

allExistingClassCoordinatesProvedPhysical : Bool
allExistingClassCoordinatesProvedPhysical = false

allExistingClassCoordinatesProvedPhysicalIsFalse :
  allExistingClassCoordinatesProvedPhysical ≡ false
allExistingClassCoordinatesProvedPhysicalIsFalse = refl

physicalWeightCoefficientTheoremClosed : Bool
physicalWeightCoefficientTheoremClosed = false

physicalWeightCoefficientTheoremClosedIsFalse :
  physicalWeightCoefficientTheoremClosed ≡ false
physicalWeightCoefficientTheoremClosedIsFalse = refl
