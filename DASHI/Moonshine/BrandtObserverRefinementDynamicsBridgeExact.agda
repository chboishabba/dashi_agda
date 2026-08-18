module DASHI.Moonshine.BrandtObserverRefinementDynamicsBridgeExact where

------------------------------------------------------------------------
-- Direct instantiation of the repository-wide observer-refinement and
-- fibre-preserving-dynamics cores on the live Brandt/Frobenius/Fricke stack.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.FibrePreservingDynamicsExact as Dynamics

import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo
import DASHI.Moonshine.P11MarkedX2FrobeniusFrickeExact as MarkedF
import DASHI.Moonshine.P11MarkedFrobeniusQuotientDefectExact as MarkedDefect
import DASHI.Moonshine.P11P37HeckeFrobeniusJointSpectrumExact as Joint
import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact as Decomp

------------------------------------------------------------------------
-- p=11 versus p=37: T2 alone collides, adding Frobenius parity strictly
-- refines that observation.
------------------------------------------------------------------------

t2MinusTwoObserver :
  Observer.Observer Joint.MinusTwoHeckeModeParity ℤ
t2MinusTwoObserver mode = -[1+ 1 ]

frobeniusParityObserver :
  Observer.Observer Joint.MinusTwoHeckeModeParity ℤ
frobeniusParityObserver = Joint.MinusTwoHeckeModeParity.frobeniusEigenvalue

minusTwoT2Collision :
  t2MinusTwoObserver Joint.p11MinusTwoModeParity
    ≡ t2MinusTwoObserver Joint.p37MinusTwoModeParity
minusTwoT2Collision = refl

minusTwoT2ToFrobeniusStrictRefinement :
  Observer.StrictRefinement
    t2MinusTwoObserver
    (Observer.pairObserver t2MinusTwoObserver frobeniusParityObserver)
minusTwoT2ToFrobeniusStrictRefinement =
  Observer.strictPairRefinement
    t2MinusTwoObserver
    frobeniusParityObserver
    Joint.p11MinusTwoModeParity
    Joint.p37MinusTwoModeParity
    refl
    Joint.p11P37MinusTwoFrobeniusParityDiffers

------------------------------------------------------------------------
-- Even T3/T5/F is not separating on the marked p=11 representation sectors.
------------------------------------------------------------------------

data RepresentationSectorWitness : Set where
  coarseBrandtSector deckStandardSector : RepresentationSectorWitness

jointT3T5FObserver :
  Observer.Observer RepresentationSectorWitness Decomp.JointEigenFingerprint
jointT3T5FObserver coarseBrandtSector = Decomp.brandtNewformFingerprint
jointT3T5FObserver deckStandardSector = Decomp.standardFingerprint

jointFingerprintCollision :
  jointT3T5FObserver coarseBrandtSector
    ≡ jointT3T5FObserver deckStandardSector
jointFingerprintCollision = Decomp.brandtAndStandardFingerprintsCoincide

sectorWitnessesDistinct : coarseBrandtSector ≡ deckStandardSector → ⊥
sectorWitnessesDistinct ()

jointT3T5FNotSeparating : Observer.Separating jointT3T5FObserver → ⊥
jointT3T5FNotSeparating =
  Observer.collisionBlocksSeparation
    (Observer.observerCollision
      coarseBrandtSector
      deckStandardSector
      jointFingerprintCollision
      sectorWitnessesDistinct)

deckRepresentationTypeObserver :
  Observer.Observer RepresentationSectorWitness Bool
deckRepresentationTypeObserver coarseBrandtSector = false
deckRepresentationTypeObserver deckStandardSector = true

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

jointFingerprintToDeckTypeStrictRefinement :
  Observer.StrictRefinement
    jointT3T5FObserver
    (Observer.pairObserver jointT3T5FObserver deckRepresentationTypeObserver)
jointFingerprintToDeckTypeStrictRefinement =
  Observer.strictPairRefinement
    jointT3T5FObserver
    deckRepresentationTypeObserver
    coarseBrandtSector
    deckStandardSector
    jointFingerprintCollision
    falseNotTrue

------------------------------------------------------------------------
-- Marked Frobenius is a nontrivial fibre automorphism over coarse j.
------------------------------------------------------------------------

p11MarkedJCore : Fibre.FibreRestrictionCore
p11MarkedJCore = record
  { Fibre.Carrier = Fine.P11Fine5
  ; Fibre.Surface = Geo.P11SupersingularJ
  ; Fibre.Evidence = ⊤
  ; Fibre.project = Fine.projectFine5
  ; Fibre.Fibre = λ j → Σ Fine.P11Fine5 (λ x → Fine.projectFine5 x ≡ j)
  ; Fibre.restrictsFibre = λ _ j →
      Σ Fine.P11Fine5 (λ x → Fine.projectFine5 x ≡ j)
  ; Fibre.doesNotRecoverCarrier = true
  ; Fibre.promotesTruth = false
  }

markedFrobeniusFibreAutomorphism : Dynamics.FibreAutomorphism p11MarkedJCore
markedFrobeniusFibreAutomorphism =
  Dynamics.fibreAutomorphism
    MarkedF.markedFrobenius
    MarkedF.markedFrobenius
    MarkedF.markedFrobeniusPreservesJClass
    MarkedF.markedFrobeniusPreservesJClass
    MarkedF.markedFrobeniusInvolution
    MarkedF.markedFrobeniusInvolution

markedFrobeniusMovesA0 :
  MarkedF.markedFrobenius Fine.a0 ≡ Fine.a0 → ⊥
markedFrobeniusMovesA0 equality =
  MarkedDefect.a0a1DistinctMarkedPoints (sym equality)

markedFrobeniusNontrivialFibreAutomorphism :
  Dynamics.NontrivialFibreAutomorphism p11MarkedJCore
markedFrobeniusNontrivialFibreAutomorphism =
  Dynamics.nontrivialFibreAutomorphism
    markedFrobeniusFibreAutomorphism
    Fine.a0
    markedFrobeniusMovesA0

markedFrobeniusHiddenTransition :
  Dynamics.HiddenTransition
    p11MarkedJCore
    MarkedF.markedFrobenius
    Fine.a0
markedFrobeniusHiddenTransition =
  Dynamics.nontrivialFibreAutomorphismCreatesHiddenTransition
    markedFrobeniusNontrivialFibreAutomorphism

markedFrobeniusForcesCoarseProjectionLoss :
  ((x y : Fine.P11Fine5) →
    Fine.projectFine5 x ≡ Fine.projectFine5 y → x ≡ y) →
  ⊥
markedFrobeniusForcesCoarseProjectionLoss =
  Dynamics.nontrivialFibreAutomorphismBlocksProjectionInjectivity
    markedFrobeniusNontrivialFibreAutomorphism

record BrandtObserverDynamicsSynthesis : Set where
  constructor brandtObserverDynamicsSynthesis
  field
    t2ToT2FIsStrictRefinement : Bool
    t2ToT2FIsStrictRefinementIsTrue : t2ToT2FIsStrictRefinement ≡ true
    t3T5FStillCollidesAcrossRepresentationSectors : Bool
    t3T5FStillCollidesAcrossRepresentationSectorsIsTrue :
      t3T5FStillCollidesAcrossRepresentationSectors ≡ true
    deckTypeStrictlyRefinesJointScalarFingerprint : Bool
    deckTypeStrictlyRefinesJointScalarFingerprintIsTrue :
      deckTypeStrictlyRefinesJointScalarFingerprint ≡ true
    markedFrobeniusIsNontrivialVerticalAutomorphism : Bool
    markedFrobeniusIsNontrivialVerticalAutomorphismIsTrue :
      markedFrobeniusIsNontrivialVerticalAutomorphism ≡ true

canonicalBrandtObserverDynamicsSynthesis : BrandtObserverDynamicsSynthesis
canonicalBrandtObserverDynamicsSynthesis =
  brandtObserverDynamicsSynthesis true refl true refl true refl true refl
