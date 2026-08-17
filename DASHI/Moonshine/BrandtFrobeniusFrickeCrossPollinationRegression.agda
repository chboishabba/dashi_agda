module DASHI.Moonshine.BrandtFrobeniusFrickeCrossPollinationRegression where

open import DASHI.Core.Prelude
open import Data.Fin using (zero)

import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.Phase3RootCharacterWeldExact as Root3
import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Foundations.F9FrobeniusInvolutionNormalFormExact as F9
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact as Spectrum
import DASHI.Moonshine.P11MarkedFrobeniusQuotientDefectExact as P11Marked
import DASHI.Moonshine.P11MarkedX2C3CharacterWeldExact as P11C3
import DASHI.Moonshine.P37NonOggFullLevel2DeuringControlExact as P37
import DASHI.Moonshine.P37MarkedX2DeckTorsorExact as P37Deck
import DASHI.Moonshine.P37MarkedLegendreT3T5Exact as P37Marked
import DASHI.Moonshine.P37MarkedX2DeckOrbitalHeckeExact as P37Orbital
import DASHI.Moonshine.P37MarkedX2DeckOrbitalPermutationExact as P37Permutation
import DASHI.Moonshine.P37JointHeckeAlgebraExact as P37Hecke
import DASHI.Moonshine.BrandtFrickeCarrierCountControlsExact as CountControls
import DASHI.Moonshine.P13OggOneClassHeckeControlExact as P13
import DASHI.Moonshine.BrandtHeckeFrobeniusFrickeSelectorWeldExact as Selector

------------------------------------------------------------------------
-- #572 finite-field Frobenius is an actual 3-fixed + 3-pair realization.
------------------------------------------------------------------------

f9FixedThree : Orbit.fixedOrbitCount F9.f9Spectrum ≡ 3
f9FixedThree = F9.f9FixedOrbitCountIsThree

f9PairedThree : Orbit.pairedOrbitCount F9.f9Spectrum ≡ 3
f9PairedThree = F9.f9PairedOrbitCountIsThree

------------------------------------------------------------------------
-- Frobenius is carrier-sensitive at p=11: marked X(2) has one pair, while the
-- coarse j-class carrier has no pair.
------------------------------------------------------------------------

p11MarkedPairOne : Orbit.pairedOrbitCount P11Marked.p11MarkedFrobeniusSpectrum ≡ 1
p11MarkedPairOne = P11Marked.p11MarkedPairCountIsOne

p11CoarsePairZero : Spectrum.frobeniusTwoOrbitCount Matrix.prime11 ≡ 0
p11CoarsePairZero = refl

------------------------------------------------------------------------
-- Genuine deck C3 character weld at p11 and p37.
------------------------------------------------------------------------

p11DeckCharacterWitness :
  P11C3.bDeckCharacter Phase.phase1 (P11C3.bRotate P11C3.bF0)
  ≡ Root3.phaseMul Phase.phase1
      (P11C3.bDeckCharacter Phase.phase1 P11C3.bF0)
p11DeckCharacterWitness =
  P11C3.bDeckCharacterDiagonalizesRotation Phase.phase1 P11C3.bF0

p37DeckCharacterWitness :
  P37Deck.frameCharacter Phase.phase1 (P37Deck.rightR37 P37.frame0)
  ≡ Root3.phaseMul Phase.phase1
      (P37Deck.frameCharacter Phase.phase1 P37.frame0)
p37DeckCharacterWitness =
  P37Deck.frameCharacterDiagonalizesRightR Phase.phase1 P37.frame0

------------------------------------------------------------------------
-- Actual marked Legendre T3/T5 recover the exact coarse Brandt rows.
------------------------------------------------------------------------

p37MarkedT3ProjectionWitness :
  P37Marked.markedT3CoarseRow (P37.lambda37 P37.q0 P37.root0)
  ≡ P37Marked.expectedT3Row
      (P37Marked.coarseClass (P37.lambda37 P37.q0 P37.root0))
p37MarkedT3ProjectionWitness =
  P37Marked.markedT3ProjectsToCoarse (P37.lambda37 P37.q0 P37.root0)

p37MarkedT5ProjectionWitness :
  P37Marked.markedT5CoarseRow (P37.lambda37 P37.q0 P37.root0)
  ≡ P37Marked.expectedT5Row
      (P37Marked.coarseClass (P37.lambda37 P37.q0 P37.root0))
p37MarkedT5ProjectionWitness =
  P37Marked.markedT5ProjectsToCoarse (P37.lambda37 P37.q0 P37.root0)

------------------------------------------------------------------------
-- Every p37 orbital summand is now an actual bijection and deck-equivariant.
------------------------------------------------------------------------

p37OrbitalBijectionWitness :
  P37Permutation.DeckOrbitalBijection P37Orbital.t3o0
p37OrbitalBijectionWitness =
  P37Permutation.canonicalDeckOrbitalBijection P37Orbital.t3o0

p37T3DeckRWitness :
  P37Orbital.orbitalT3Neighbour
    (P37Deck.rightRPoint (P37.p37MarkedPoint P37.j8 P37.frame0)) zero
  ≡ P37Deck.rightRPoint
      (P37Orbital.orbitalT3Neighbour
        (P37.p37MarkedPoint P37.j8 P37.frame0) zero)
p37T3DeckRWitness =
  P37Orbital.orbitalT3DeckREquivariant
    (P37.p37MarkedPoint P37.j8 P37.frame0) zero

------------------------------------------------------------------------
-- Full positive coarse T2/T3/T5 Hecke algebra survives non-Ogg p37.
------------------------------------------------------------------------

p37T2T3Commutation :
  P37Hecke.compose P37Hecke.B37_2 P37Hecke.B37_3
  ≡ P37Hecke.compose P37Hecke.B37_3 P37Hecke.B37_2
p37T2T3Commutation = P37Hecke.B2B3Commute

p37T2T5Commutation :
  P37Hecke.compose P37Hecke.B37_2 P37Hecke.B37_5
  ≡ P37Hecke.compose P37Hecke.B37_5 P37Hecke.B37_2
p37T2T5Commutation = P37Hecke.B2B5Commute

p37T3T5Commutation :
  P37Hecke.compose P37Hecke.B37_3 P37Hecke.B37_5
  ≡ P37Hecke.compose P37Hecke.B37_5 P37Hecke.B37_3
p37T3T5Commutation = P37Hecke.B3B5Commute

p37T3Square :
  P37Hecke.compose P37Hecke.B37_3 P37Hecke.B37_3
  ≡ P37Hecke.addScaledIdentity P37Hecke.B37_9 3
p37T3Square = P37Hecke.B3SquareHecke

------------------------------------------------------------------------
-- Selector and same-cardinality controls.
------------------------------------------------------------------------

p11SelectorTrue : Selector.finiteFrobeniusSelector Matrix.prime11 ≡ true
p11SelectorTrue = Selector.p11FiniteFrobeniusSelectorTrue

p37SelectorFalse : Selector.finiteFrobeniusSelector Matrix.prime37 ≡ false
p37SelectorFalse = Selector.p37FiniteFrobeniusSelectorFalse

p13SelectorTrue : Spectrum.allSupersingularSlotsFixed Matrix.prime13 ≡ true
p13SelectorTrue = P13.p13FiniteFrobeniusSelectorTrue

p43CountCoincidenceOnly :
  CountControls.p43BrandtClassCount ≡ CountControls.p43FrickeFixedCount
p43CountCoincidenceOnly = CountControls.p43BrandtAndFrickeCountsCoincide
