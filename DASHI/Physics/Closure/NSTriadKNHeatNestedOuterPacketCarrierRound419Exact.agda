module DASHI.Physics.Closure.NSTriadKNHeatNestedOuterPacketCarrierRound419Exact where

------------------------------------------------------------------------
-- ROUND419 / BIDI CARRIER WELD: R329/R336 OUTER INCIDENCE IS R98 PACKET CELL
--
-- The heat-factorized nested lane and the critical packet lane looked like
-- separate decompositions.  They are not separate at the outer interaction:
-- R329 stores an `outer : PhysicalTriadIncidence`, and R98's selected packet
-- power is defined on that exact carrier, selecting by `Physical.k outer`.
--
-- This owner makes that identity executable.  A literal R329 nested cell has
-- one canonical R98 packet-boundary scalar obtained by evaluating
-- `selectedOrderedPower` on its SAME outer incidence.  For an R336 signed
-- pairwise overlap, `sameFinalOutput` therefore implies the two packet selectors
-- see exactly the same final-output bit.  No permutation, reindexing, or proxy
-- incidence is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNStrongLowLiteralNestedKernelRound329Exact as R329
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPreTTStarAdapterRound336Exact as R336
import DASHI.Physics.Closure.NSTriadKNSelectedPacketProjectedPairingRound98Exact as R98

F : C3.RealField _
F = Rational.rationalRealField

nestedOuterPacketPower :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (O : Leray.RationalInverseNormOrder E I) →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (H : R142.HelicalHalfCalibration S) →
  (W : R294.SwapInvariantCellWeight F) →
  (selected : Z3.FourierMode → Bool) →
  R329.StrongLowLiteralNestedCell E I O system S L H W →
  ℚ
nestedOuterPacketPower E I O system S L H W selected C =
  R98.selectedOrderedPower
    E I selected (Audit.velocity system) (R329.outer C)

nestedOuterPacketPowerIsLiteralR98OnSameOuter :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (O : Leray.RationalInverseNormOrder E I) →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (H : R142.HelicalHalfCalibration S) →
  (W : R294.SwapInvariantCellWeight F) →
  (selected : Z3.FourierMode → Bool) →
  (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
  nestedOuterPacketPower E I O system S L H W selected C
  ≡ R98.selectedOrderedPower
      E I selected (Audit.velocity system) (R329.outer C)
nestedOuterPacketPowerIsLiteralR98OnSameOuter E I O system S L H W selected C = refl

sameFinalOutputImpliesSamePacketSelectorBit :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (O : Leray.RationalInverseNormOrder E I) →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (H : R142.HelicalHalfCalibration S) →
  (W : R294.SwapInvariantCellWeight F) →
  (selected : Z3.FourierMode → Bool) →
  (P : R336.HeatWeightedNestedPairwiseOverlap E I O system S L H W) →
  selected (Physical.k (R329.outer (R336.left P)))
  ≡ selected (Physical.k (R329.outer (R336.right P)))
sameFinalOutputImpliesSamePacketSelectorBit
  E I O system S L H W selected P =
  cong selected (R336.sameFinalOutput P)

round419HeatNestedAndPacketOuterCarrierDefinitionallySame : Bool
round419HeatNestedAndPacketOuterCarrierDefinitionallySame = true

round419R336SameOutputPreservesR98PacketSelector : Bool
round419R336SameOutputPreservesR98PacketSelector = true

round419NoProxyPacketIncidenceIntroduced : Bool
round419NoProxyPacketIncidenceIntroduced = true

round419HeatNestedAndPacketOuterCarrierDefinitionallySameIsTrue :
  round419HeatNestedAndPacketOuterCarrierDefinitionallySame ≡ true
round419HeatNestedAndPacketOuterCarrierDefinitionallySameIsTrue = refl
