module DASHI.Moonshine.BrandtFrobeniusFrickeCrossPollinationRegression where

open import DASHI.Core.Prelude
open import Data.Integer using (+_; -[1+_])

import DASHI.Foundations.F9FrobeniusInvolutionNormalFormExact as F9
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact as Spectrum
import DASHI.Moonshine.P11MarkedFrobeniusQuotientDefectExact as P11Marked
import DASHI.Moonshine.P11P37HeckeFrobeniusJointSpectrumExact as Joint
import DASHI.Moonshine.P11MarkedX2C3CharacterWeldExact as P11C3
import DASHI.Moonshine.P37MarkedX2DeckTorsorExact as P37Deck
import DASHI.Moonshine.P37MarkedLegendreT3T5Exact as P37Marked
import DASHI.Moonshine.P37MarkedX2DeckOrbitalHeckeExact as P37Orbital
import DASHI.Moonshine.P37MarkedX2DeckOrbitalPermutationExact as P37Permutation
import DASHI.Moonshine.P37MarkedX2HeckeFrobeniusFrickeExact as P37JointMarked
import DASHI.Moonshine.P37JointHeckeAlgebraExact as P37Hecke
import DASHI.Moonshine.BrandtFrickeCarrierCountControlsExact as CountControls
import DASHI.Moonshine.P13OggOneClassHeckeControlExact as P13
import DASHI.Moonshine.BrandtHeckeFrobeniusFrickeSelectorWeldExact as Selector

------------------------------------------------------------------------
-- #572 finite-field Frobenius is an actual 3-fixed + 3-pair realization.
------------------------------------------------------------------------

f9FixedThree : F9.f9FixedOrbitCountIsThree ≡ refl
f9FixedThree = refl

f9PairedThree : F9.f9PairedOrbitCountIsThree ≡ refl
f9PairedThree = refl

------------------------------------------------------------------------
-- Frobenius is carrier-sensitive at p=11: marked X(2) has one pair, while the
-- coarse j-class carrier has no pair.
------------------------------------------------------------------------

p11MarkedPairOne : P11Marked.p11MarkedPairCountIsOne ≡ refl
p11MarkedPairOne = refl

p11CoarsePairZero :
  Spectrum.frobeniusTwoOrbitCount Matrix.prime11 ≡ 0
p11CoarsePairZero = refl

------------------------------------------------------------------------
-- p11 and p37 share a T2=-2 mode but not its Frobenius parity.
------------------------------------------------------------------------

minusTwoParityDiffers = Joint.p11P37MinusTwoFrobeniusParityDiffers

------------------------------------------------------------------------
-- Genuine deck C3 character weld at p11; p37 carries the same Phase3 chart on
-- each deck-R cycle of the actual 3x6 torsor.
------------------------------------------------------------------------

p11DeckCharacterWitness =
  P11C3.bDeckCharacterDiagonalizesRotation

p37DeckCharacterWitness =
  P37Deck.frameCharacterDiagonalizesRightR

------------------------------------------------------------------------
-- p37 actual marked Legendre T3/T5 recover the exact coarse Brandt rows and
-- commute with the marked Frobenius/Fricke action.
------------------------------------------------------------------------

p37MarkedT3ProjectionWitness = P37Marked.markedT3ProjectsToCoarse
p37MarkedT5ProjectionWitness = P37Marked.markedT5ProjectsToCoarse
p37MarkedT3FrickeWitness = P37JointMarked.markedT3CommutesWithFricke
p37MarkedT5FrickeWitness = P37JointMarked.markedT5CommutesWithFricke

------------------------------------------------------------------------
-- Every p37 orbital summand is now an actual bijection and deck-equivariant.
------------------------------------------------------------------------

p37OrbitalBijectionWitness = P37Permutation.canonicalDeckOrbitalBijection
p37T3DeckRWitness = P37Orbital.orbitalT3DeckREquivariant
p37T5DeckSWitness = P37Orbital.orbitalT5DeckSEquivariant

------------------------------------------------------------------------
-- Full positive coarse T2/T3/T5 Hecke algebra survives non-Ogg p37.
------------------------------------------------------------------------

p37T2T3Commutation = P37Hecke.B2B3Commute
p37T2T5Commutation = P37Hecke.B2B5Commute
p37T3T5Commutation = P37Hecke.B3B5Commute
p37T2Square = P37Hecke.B2SquareHecke
p37T3Square = P37Hecke.B3SquareHecke
p37T5Square = P37Hecke.B5SquareHecke

------------------------------------------------------------------------
-- Selector and same-cardinality controls.
------------------------------------------------------------------------

p11SelectorTrue = Selector.p11FiniteFrobeniusSelectorTrue
p37SelectorFalse = Selector.p37FiniteFrobeniusSelectorFalse
p13SelectorTrue = P13.p13FiniteFrobeniusSelectorTrue
p43CountCoincidenceOnly = CountControls.p43BrandtAndFrickeCountsCoincide
