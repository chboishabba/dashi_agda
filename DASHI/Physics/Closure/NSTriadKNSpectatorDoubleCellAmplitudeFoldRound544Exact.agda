module DASHI.Physics.Closure.NSTriadKNSpectatorDoubleCellAmplitudeFoldRound544Exact where

------------------------------------------------------------------------
-- ROUND544 / SPECTATOR-WEIGHTED DOUBLE-MIXED CELL -> FOUR MIXED-CELL FOLDS
--
-- R387 gives pointwise
--
--   Ddouble(tau) = 2 A(tau) + 2 A(swap tau).
--
-- For any R294 swap-invariant weight W, swap is a permutation of the complete
-- physical output fibre.  Therefore the weighted double-cell fold is exactly
-- four copies of the weighted plus-minus mixed-cell fold.  This is the
-- amplitude-side companion to R542's forcing/commutator normalization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as R73
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNDoubleMixedAsSwapPairedPlusMinusRound387Exact as R387
import DASHI.Physics.Closure.NSTriadKNDoubleMixedPhysicalDampedTangentRound388Exact as R388

module Fold
    {r} {F : C3.RealField r}
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (W : R294.SwapInvariantCellWeight F) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem

  module D = R388.PhysicalDoubleMixed physicalSystem S

  system : Audit.FiniteComplex3GalerkinSystem F E I
  system = Field30.finiteSystem physicalSystem

  amplitude : Physical.PhysicalTriadIncidence → C3.Complex3 F
  amplitude tau =
    C3.complex3Scale (R294.weight W tau) (D.Pair.mixedCell tau)

  weightedDoubleCell : Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedDoubleCell tau =
    C3.complex3Scale (R294.weight W tau)
      (R225.doubleMixedCell S D.Pair.velocity tau)

  weightedSwapAmplitude : Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedSwapAmplitude tau =
    C3.complex3Scale (R294.weight W tau)
      (D.Pair.mixedCell (Symmetry.swapTriad tau))

  weightedSwapAmplitudeIsAmplitudeAfterSwap :
    (tau : Physical.PhysicalTriadIncidence) →
    weightedSwapAmplitude tau ≡ amplitude (Symmetry.swapTriad tau)
  weightedSwapAmplitudeIsAmplitudeAfterSwap tau =
    cong
      (λ selectedWeight →
        C3.complex3Scale selectedWeight
          (D.Pair.mixedCell (Symmetry.swapTriad tau)))
      (sym (R294.swapInvariant W tau))

  weightedDoubleCellPointwise :
    (tau : Physical.PhysicalTriadIncidence) →
    weightedDoubleCell tau
    ≡ C3.complex3Add
        (C3.complex3Add (amplitude tau) (amplitude tau))
        (C3.complex3Add
          (weightedSwapAmplitude tau) (weightedSwapAmplitude tau))
  weightedDoubleCellPointwise tau =
    let
      w = R294.weight W tau
      a = D.Pair.mixedCell tau
      as = D.Pair.mixedCell (Symmetry.swapTriad tau)
    in
    trans
      (cong (C3.complex3Scale w)
        (R387.doubleMixedIsSwapPairedPlusMinus S D.Pair.velocity tau))
      (trans
        (R73.complex3ScaleAdd w (R387.doublePlus a) (R387.doublePlus as))
        (cong₂ C3.complex3Add
          (R73.complex3ScaleAdd w a a)
          (R73.complex3ScaleAdd w as as)))

  foldSwapAmplitudeIsFoldAmplitude :
    (cutoff : Nat) (output : Z3.FourierMode) →
    R224.foldVector weightedSwapAmplitude
      (Output.physicalOutputFiber cutoff output)
    ≡ R224.foldVector amplitude
      (Output.physicalOutputFiber cutoff output)
  foldSwapAmplitudeIsFoldAmplitude cutoff output =
    trans
      (pointwise (Output.physicalOutputFiber cutoff output))
      (trans
        (sym
          (R224.foldMap amplitude Symmetry.swapTriad
            (Output.physicalOutputFiber cutoff output)))
        (R224.foldPermutationInvariant amplitude
          (R224.swapOutputFibrePermutation cutoff output)))
    where
    pointwise :
      (items : List Physical.PhysicalTriadIncidence) →
      R224.foldVector weightedSwapAmplitude items
      ≡ R224.foldVector (λ tau → amplitude (Symmetry.swapTriad tau)) items
    pointwise [] = refl
    pointwise (tau ∷ rest) =
      cong₂ C3.complex3Add
        (weightedSwapAmplitudeIsAmplitudeAfterSwap tau)
        (pointwise rest)

  foldPointwise :
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector weightedDoubleCell items
    ≡ R224.foldVector
        (λ tau → C3.complex3Add
          (C3.complex3Add (amplitude tau) (amplitude tau))
          (C3.complex3Add
            (weightedSwapAmplitude tau) (weightedSwapAmplitude tau))) items
  foldPointwise [] = refl
  foldPointwise (tau ∷ rest) =
    cong₂ C3.complex3Add
      (weightedDoubleCellPointwise tau)
      (foldPointwise rest)

  foldFourComponents :
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector
      (λ tau → C3.complex3Add
        (C3.complex3Add (amplitude tau) (amplitude tau))
        (C3.complex3Add
          (weightedSwapAmplitude tau) (weightedSwapAmplitude tau))) items
    ≡ C3.complex3Add
        (C3.complex3Add
          (R224.foldVector amplitude items)
          (R224.foldVector amplitude items))
        (C3.complex3Add
          (R224.foldVector weightedSwapAmplitude items)
          (R224.foldVector weightedSwapAmplitude items))
  foldFourComponents items =
    trans
      (R230.foldAdd
        (λ tau → C3.complex3Add (amplitude tau) (amplitude tau))
        (λ tau → C3.complex3Add
          (weightedSwapAmplitude tau) (weightedSwapAmplitude tau))
        items)
      (cong₂ C3.complex3Add
        (R230.foldAdd amplitude amplitude items)
        (R230.foldAdd weightedSwapAmplitude weightedSwapAmplitude items))

  fixedOutputWeightedDoubleCellIsFourAmplitudeFolds :
    (output : Z3.FourierMode) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output
        A = R224.foldVector amplitude items
    in
    R224.foldVector weightedDoubleCell items
    ≡ C3.complex3Add (C3.complex3Add A A) (C3.complex3Add A A)
  fixedOutputWeightedDoubleCellIsFourAmplitudeFolds output =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
      A = R224.foldVector amplitude items
    in
    trans
      (foldPointwise items)
      (trans
        (foldFourComponents items)
        (cong
          (λ Sfold → C3.complex3Add (C3.complex3Add A A)
            (C3.complex3Add Sfold Sfold))
          (foldSwapAmplitudeIsFoldAmplitude (Audit.cutoff system) output)))

round544WeightedDoubleCellFoldNormalizationClosed : Bool
round544WeightedDoubleCellFoldNormalizationClosed = true

round544IntroducesAnyAnalyticEstimate : Bool
round544IntroducesAnyAnalyticEstimate = false

round544SignedSpacetimeEstimateClosed : Bool
round544SignedSpacetimeEstimateClosed = false

round544ClayPromotion : Bool
round544ClayPromotion = false

round544WeightedDoubleCellFoldNormalizationClosedIsTrue :
  round544WeightedDoubleCellFoldNormalizationClosed ≡ true
round544WeightedDoubleCellFoldNormalizationClosedIsTrue = refl

round544IntroducesAnyAnalyticEstimateIsFalse :
  round544IntroducesAnyAnalyticEstimate ≡ false
round544IntroducesAnyAnalyticEstimateIsFalse = refl

round544ClayPromotionIsFalse : round544ClayPromotion ≡ false
round544ClayPromotionIsFalse = refl
