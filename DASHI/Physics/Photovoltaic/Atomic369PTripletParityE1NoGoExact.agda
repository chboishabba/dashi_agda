module DASHI.Physics.Photovoltaic.Atomic369PTripletParityE1NoGoExact where

-- 2026-11-16: SECOND independent 369 optical max-cut.
-- NIST Atomic Spectroscopy E1 rigorous rule: PARITY MUST CHANGE.
-- DOI-free authoritative source: NIST Atomic Spectroscopy / Spectral
-- Lines, Selection Rules: https://www.nist.gov/pml/atomic-spectroscopy-
-- compendium-basic-ideas-notation-data-and-formulas/atomic-spectroscopy
--
-- The source p-triplet has l=1: all m labels have odd one-electron parity.
-- The source selected p^2 sector has two l=1 orbitals: even total parity.
-- A pure electric-dipole p->p or p^2->p^2 transition inside an
-- inversion-symmetric source sector therefore cannot be bright.
-- Nonzero E1 transitions may involve OTHER parity sectors or broken
-- inversion in real materials/defects; magnetic/quadruple transitions
-- are separately possible. No Agda kernel check yet.

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3PhysicalRealizationExact as P
import DASHI.Physics.Chemistry.AtomicPeriodicTable369P2CoulombExecutionExact as P2

data Parity : Set where
  even odd : Parity

pOneElectronParity : P.MagneticState -> Parity
pOneElectronParity P.mNegOne = odd
pOneElectronParity P.mZero = odd
pOneElectronParity P.mPosOne = odd

pTwoElectronParity : P2.P2Basis -> Parity
pTwoElectronParity P2.p2NegZero = even
pTwoElectronParity P2.p2NegPos = even
pTwoElectronParity P2.p2ZeroPos = even

pTripletSameParity :
  (initial final : P.MagneticState) ->
  pOneElectronParity initial ≡ pOneElectronParity final
pTripletSameParity P.mNegOne P.mNegOne = refl
pTripletSameParity P.mNegOne P.mZero = refl
pTripletSameParity P.mNegOne P.mPosOne = refl
pTripletSameParity P.mZero P.mNegOne = refl
pTripletSameParity P.mZero P.mZero = refl
pTripletSameParity P.mZero P.mPosOne = refl
pTripletSameParity P.mPosOne P.mNegOne = refl
pTripletSameParity P.mPosOne P.mZero = refl
pTripletSameParity P.mPosOne P.mPosOne = refl

p2SelectedSameParity :
  (initial final : P2.P2Basis) ->
  pTwoElectronParity initial ≡ pTwoElectronParity final
p2SelectedSameParity P2.p2NegZero P2.p2NegZero = refl
p2SelectedSameParity P2.p2NegZero P2.p2NegPos = refl
p2SelectedSameParity P2.p2NegZero P2.p2ZeroPos = refl
p2SelectedSameParity P2.p2NegPos P2.p2NegZero = refl
p2SelectedSameParity P2.p2NegPos P2.p2NegPos = refl
p2SelectedSameParity P2.p2NegPos P2.p2ZeroPos = refl
p2SelectedSameParity P2.p2ZeroPos P2.p2NegZero = refl
p2SelectedSameParity P2.p2ZeroPos P2.p2NegPos = refl
p2SelectedSameParity P2.p2ZeroPos P2.p2ZeroPos = refl

-- An actual optical complex amplitude domain has characteristic !=2;
-- therefore a = -a entails a = 0. This cannot be derived from the
-- symbolic C3 phase-only table: it is a separate PHYSICAL scalar gate.
record InversionOddE1Amplitude : Set₁ where
  field
    Amplitude : Set
    zero : Amplitude
    negateAmplitude : Amplitude -> Amplitude
    selfOppositeImpliesZero :
      (a : Amplitude) ->
      a ≡ negateAmplitude a ->
      a ≡ zero

open InversionOddE1Amplitude public

record PTripletInversionSymmetricOptics (a : InversionOddE1Amplitude) : Set where
  field
    dipoleE1 : P.MagneticState -> P.MagneticState -> Amplitude a
    inversionOddCovariance :
      (i f : P.MagneticState) ->
      dipoleE1 i f ≡ negateAmplitude a (dipoleE1 i f)

pTripletInternalE1MustVanish :
  (a : InversionOddE1Amplitude) ->
  (m : PTripletInversionSymmetricOptics a) ->
  (i f : P.MagneticState) ->
  PTripletInversionSymmetricOptics.dipoleE1 m i f ≡ zero a
pTripletInternalE1MustVanish a m i f =
  selfOppositeImpliesZero a
    (PTripletInversionSymmetricOptics.dipoleE1 m i f)
    (PTripletInversionSymmetricOptics.inversionOddCovariance m i f)

-- The same logic applies to a pure 2p^2 inversion-symmetric sector.
record P2InversionSymmetricOptics (a : InversionOddE1Amplitude) : Set where
  field
    dipoleE1 : P2.P2Basis -> P2.P2Basis -> Amplitude a
    inversionOddCovariance :
      (i f : P2.P2Basis) ->
      dipoleE1 i f ≡ negateAmplitude a (dipoleE1 i f)

p2InternalE1MustVanish :
  (a : InversionOddE1Amplitude) ->
  (m : P2InversionSymmetricOptics a) ->
  (i f : P2.P2Basis) ->
  P2InversionSymmetricOptics.dipoleE1 m i f ≡ zero a
p2InternalE1MustVanish a m i f =
  selfOppositeImpliesZero a
    (P2InversionSymmetricOptics.dipoleE1 m i f)
    (P2InversionSymmetricOptics.inversionOddCovariance m i f)

-- IMPORTANT: this statement requires an inversion-symmetric source
-- Hamiltonian and an odd E1 operator. A C3v NV centre, an interface,
-- inversion-mixed exciton or applied field can violate this admission.
