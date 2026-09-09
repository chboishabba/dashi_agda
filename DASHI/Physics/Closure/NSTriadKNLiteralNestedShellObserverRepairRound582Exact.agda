module DASHI.Physics.Closure.NSTriadKNLiteralNestedShellObserverRepairRound582Exact where

------------------------------------------------------------------------
-- ROUND582 / INTROSPECTIVE REPAIR: R336 SHELL LABELS ARE NOT YET PHYSICAL
--
-- R336 correctly keeps a same-final-output signed nested overlap, but its
-- `leftShell` / `rightShell` fields are free Nat labels.  Neither R336 nor R29
-- relates those labels to a literal Fourier mode of the R329 nested cell.
-- Consequently the same physical pair can currently be relabelled arbitrarily
-- without changing either vector, its signed overlap, or its local envelope.
--
-- This is an observer defect, not an analytic theorem failure.
--
-- The canonical literal shell function already exists:
--
--   Shell.shellIndex : FourierMode -> Nat.
--
-- What is missing is the semantic choice of WHICH literal R329 mode indexes
-- the operator family whose cross-shell almost-orthogonality is being claimed.
-- A nested cell exposes at least the following source-native coordinates:
--
--   inner p, inner q, inner output = outer p, outer q, final output k.
--
-- We do not guess among them.  Instead this file makes that selector explicit,
-- realizes R336 shell labels through the canonical shell function, and defines
-- the actual separation seen by any future decay theorem.
--
-- Only after this repair does the phrase "shell-decaying local envelope" have
-- a typed same-object meaning.  No decay estimate is proved here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (∣_-_∣)
open import Data.Rational.Base using (ℚ; _≤_)

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
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- Existing R336 physical overlap is invariant under arbitrary shell relabel.
------------------------------------------------------------------------

relabelR336Shells :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F) →
  R336.HeatWeightedNestedPairwiseOverlap E I O system S L H W →
  Nat → Nat →
  R336.HeatWeightedNestedPairwiseOverlap E I O system S L H W
relabelR336Shells E I O system S L H W P leftLabel rightLabel =
  R336.heat-weighted-nested-pairwise-overlap
    (R336.left P)
    (R336.right P)
    leftLabel
    rightLabel
    (R336.sameFinalOutput P)
    (R336.localEnvelope P)
    (R336.signedOverlapBound P)

relabelKeepsSignedOverlap :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F)
  (P : R336.HeatWeightedNestedPairwiseOverlap E I O system S L H W)
  (leftLabel rightLabel : Nat) →
  R336.signedNestedOverlap E I O system S L H W
    (relabelR336Shells E I O system S L H W P leftLabel rightLabel)
  ≡ R336.signedNestedOverlap E I O system S L H W P
relabelKeepsSignedOverlap E I O system S L H W P leftLabel rightLabel = refl

relabelKeepsLocalEnvelope :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F)
  (P : R336.HeatWeightedNestedPairwiseOverlap E I O system S L H W)
  (leftLabel rightLabel : Nat) →
  R336.localEnvelope
    (relabelR336Shells E I O system S L H W P leftLabel rightLabel)
  ≡ R336.localEnvelope P
relabelKeepsLocalEnvelope E I O system S L H W P leftLabel rightLabel = refl

------------------------------------------------------------------------
-- Literal source-native mode coordinates available on one R329 nested cell.
------------------------------------------------------------------------

data NestedOperatorShellCoordinate582 : Set where
  innerLeft582 : NestedOperatorShellCoordinate582
  innerRight582 : NestedOperatorShellCoordinate582
  innerOutputOuterForcing582 : NestedOperatorShellCoordinate582
  outerPartner582 : NestedOperatorShellCoordinate582
  finalOutput582 : NestedOperatorShellCoordinate582

modeAtCoordinate582 :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F) →
  NestedOperatorShellCoordinate582 →
  R329.StrongLowLiteralNestedCell E I O system S L H W →
  Physical.FourierMode
modeAtCoordinate582 E I O system S L H W innerLeft582 C =
  Physical.p (R329.inner C)
modeAtCoordinate582 E I O system S L H W innerRight582 C =
  Physical.q (R329.inner C)
modeAtCoordinate582 E I O system S L H W innerOutputOuterForcing582 C =
  Physical.p (R329.outer C)
modeAtCoordinate582 E I O system S L H W outerPartner582 C =
  Physical.q (R329.outer C)
modeAtCoordinate582 E I O system S L H W finalOutput582 C =
  Physical.k (R329.outer C)

shellAtCoordinate582 :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F) →
  NestedOperatorShellCoordinate582 →
  R329.StrongLowLiteralNestedCell E I O system S L H W → Nat
shellAtCoordinate582 E I O system S L H W coordinate C =
  Shell.shellIndex (modeAtCoordinate582 E I O system S L H W coordinate C)

------------------------------------------------------------------------
-- Corrected pair carrier: one fixed physical operator-shell coordinate.
------------------------------------------------------------------------

record PhysicallyRealizedNestedShellPair582
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (W : R294.SwapInvariantCellWeight F)
    (coordinate : NestedOperatorShellCoordinate582) : Set where
  constructor physically-realized-nested-shell-pair582
  field
    overlap582 : R336.HeatWeightedNestedPairwiseOverlap E I O system S L H W
    leftShellRealized582 :
      R336.leftShell overlap582
      ≡ shellAtCoordinate582 E I O system S L H W coordinate (R336.left overlap582)
    rightShellRealized582 :
      R336.rightShell overlap582
      ≡ shellAtCoordinate582 E I O system S L H W coordinate (R336.right overlap582)

open PhysicallyRealizedNestedShellPair582 public

realizedSeparation582 :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F)
  (coordinate : NestedOperatorShellCoordinate582) →
  PhysicallyRealizedNestedShellPair582 E I O system S L H W coordinate → Nat
realizedSeparation582 E I O system S L H W coordinate P =
  ∣ shellAtCoordinate582 E I O system S L H W coordinate
      (R336.left (overlap582 P))
    - shellAtCoordinate582 E I O system S L H W coordinate
      (R336.right (overlap582 P)) ∣

------------------------------------------------------------------------
-- Future local decay must be indexed by the REALIZED separation.
-- This is still only a producer interface; no decay profile is inhabited here.
------------------------------------------------------------------------

record SeparationIndexedNestedEnvelope582
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (W : R294.SwapInvariantCellWeight F)
    (coordinate : NestedOperatorShellCoordinate582)
    (P : PhysicallyRealizedNestedShellPair582 E I O system S L H W coordinate) : Set where
  constructor separation-indexed-nested-envelope582
  field
    separationProfile582 : Nat → ℚ
    envelopeControlledAtRealizedSeparation582 :
      R336.localEnvelope (overlap582 P)
      ≤ separationProfile582
          (realizedSeparation582 E I O system S L H W coordinate P)

open SeparationIndexedNestedEnvelope582 public

------------------------------------------------------------------------
-- Introspective frontier.
------------------------------------------------------------------------

data NestedShellObserverResidual582 : Set where
  missingPhysicalOperatorShellRealization582 : NestedShellObserverResidual582
  missingSeparationIndexedLocalEnvelope582 : NestedShellObserverResidual582
  missingCutoffUniformSeparationMassSummation582 : NestedShellObserverResidual582

currentResidual582 : NestedShellObserverResidual582
currentResidual582 = missingPhysicalOperatorShellRealization582

round582R336FreeShellLabelsPhysicallyBound : Bool
round582R336FreeShellLabelsPhysicallyBound = false

round582ArbitraryRelabelPreservesPhysicalOverlap : Bool
round582ArbitraryRelabelPreservesPhysicalOverlap = true

round582CanonicalLiteralShellFunctionAvailable : Bool
round582CanonicalLiteralShellFunctionAvailable = Shell.literalShellFunctionConstructed

round582PhysicalOperatorShellCoordinateSelected : Bool
round582PhysicalOperatorShellCoordinateSelected = false

round582SeparationIndexedLocalEnvelopeClosed : Bool
round582SeparationIndexedLocalEnvelopeClosed = false

round582CutoffUniformSeparationMassSummationClosed : Bool
round582CutoffUniformSeparationMassSummationClosed = false

round582LeafAClosed : Bool
round582LeafAClosed = false

round582ClayPromotion : Bool
round582ClayPromotion = false

round582R336FreeShellLabelsPhysicallyBoundIsFalse :
  round582R336FreeShellLabelsPhysicallyBound ≡ false
round582R336FreeShellLabelsPhysicallyBoundIsFalse = refl

round582ArbitraryRelabelPreservesPhysicalOverlapIsTrue :
  round582ArbitraryRelabelPreservesPhysicalOverlap ≡ true
round582ArbitraryRelabelPreservesPhysicalOverlapIsTrue = refl

round582CanonicalLiteralShellFunctionAvailableIsTrue :
  round582CanonicalLiteralShellFunctionAvailable ≡ true
round582CanonicalLiteralShellFunctionAvailableIsTrue =
  Shell.literalShellFunctionConstructedIsTrue

round582ClayPromotionIsFalse : round582ClayPromotion ≡ false
round582ClayPromotionIsFalse = refl
