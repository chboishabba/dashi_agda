module DASHI.Physics.Closure.NSTriadKNR573HomochiralHeterochiralSplitExact where

------------------------------------------------------------------------
-- PERIODIC B / R573 LITERAL FOUR-CHANNEL SPLIT
--
-- The live R567 forcing square reaches R573 before any norm:
--
--   (++ + +-) + (-+ + --).
--
-- The preferred R571 Taylor/second-moment machinery is a HOMOCHIRAL theorem;
-- it must not be silently applied to the heterochiral (+-/-+) channels.
-- This owner performs the exact split on the literal R573 carrier:
--
--   fourSignInner = homochiralInner + heterochiralInner
--
-- and pushes it through the outer slot fold and the spectator weight.  This
-- is the representation theorem needed before the homochiral M2 payment and
-- the independent heterochiral HH->low route can be combined safely.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as R73
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as R82
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNNestedProjectedForcingSlotExpansionRound309Exact as R309
import DASHI.Physics.Closure.NSTriadKNNestedComponentwiseInnerCommutatorRound572Exact as R572
import DASHI.Physics.Closure.NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact as R573

module Split
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Inner = R572.ComponentwiseNested system S L velocityTransverse
  module C = Inner.C
  module Nested = R573.WeightedNested W S L H system velocityTransverse

  homochiralInner :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  homochiralInner tau =
    C3.complex3Add
      (C.multiplierDifferenceVector tau Helical.plus Helical.plus)
      (C.multiplierDifferenceVector tau Helical.minus Helical.minus)

  heterochiralInner :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  heterochiralInner tau =
    C3.complex3Add
      (C.multiplierDifferenceVector tau Helical.plus Helical.minus)
      (C.multiplierDifferenceVector tau Helical.minus Helical.plus)

  fourSignInnerIsHomoPlusHetero :
    (tau : Physical.PhysicalTriadIncidence) →
    Inner.fourSignInner tau
    ≡ C3.complex3Add (homochiralInner tau) (heterochiralInner tau)
  fourSignInnerIsHomoPlusHetero tau =
    R82.complex3Interchange
      (C.multiplierDifferenceVector tau Helical.plus Helical.plus)
      (C.multiplierDifferenceVector tau Helical.plus Helical.minus)
      (C.multiplierDifferenceVector tau Helical.minus Helical.plus)
      (C.multiplierDifferenceVector tau Helical.minus Helical.minus)

  homochiralSlot :
    (outer inner : Physical.PhysicalTriadIncidence) →
    C3.Complex3 F
  homochiralSlot outer inner =
    R145.slotKernel
      (R167.normalizedDirection E S (Physical.p outer))
      (R167.normalizedDirection E S (Physical.q outer))
      (homochiralInner inner)
      (Audit.velocity system (Physical.q outer))

  heterochiralSlot :
    (outer inner : Physical.PhysicalTriadIncidence) →
    C3.Complex3 F
  heterochiralSlot outer inner =
    R145.slotKernel
      (R167.normalizedDirection E S (Physical.p outer))
      (R167.normalizedDirection E S (Physical.q outer))
      (heterochiralInner inner)
      (Audit.velocity system (Physical.q outer))

  fourSignSlotIsHomoPlusHetero :
    (outer inner : Physical.PhysicalTriadIncidence) →
    R145.slotKernel
      (R167.normalizedDirection E S (Physical.p outer))
      (R167.normalizedDirection E S (Physical.q outer))
      (Inner.fourSignInner inner)
      (Audit.velocity system (Physical.q outer))
    ≡
    C3.complex3Add
      (homochiralSlot outer inner)
      (heterochiralSlot outer inner)
  fourSignSlotIsHomoPlusHetero outer inner =
    trans
      (cong
        (λ value →
          R145.slotKernel
            (R167.normalizedDirection E S (Physical.p outer))
            (R167.normalizedDirection E S (Physical.q outer))
            value
            (Audit.velocity system (Physical.q outer)))
        (fourSignInnerIsHomoPlusHetero inner))
      (R309.slotKernelAdditiveFirstAmplitude
        (R167.normalizedDirection E S (Physical.p outer))
        (R167.normalizedDirection E S (Physical.q outer))
        (homochiralInner inner)
        (heterochiralInner inner)
        (Audit.velocity system (Physical.q outer)))

  homochiralSlotFold :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  homochiralSlotFold outer =
    R224.foldVector
      (homochiralSlot outer)
      (Output.physicalOutputFiber
        (Audit.cutoff system) (Physical.p outer))

  heterochiralSlotFold :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  heterochiralSlotFold outer =
    R224.foldVector
      (heterochiralSlot outer)
      (Output.physicalOutputFiber
        (Audit.cutoff system) (Physical.p outer))

  nestedSlotFoldIsHomoPlusHetero :
    (outer : Physical.PhysicalTriadIncidence) →
    Nested.nestedSlotFold outer
    ≡
    C3.complex3Add
      (homochiralSlotFold outer)
      (heterochiralSlotFold outer)
  nestedSlotFoldIsHomoPlusHetero outer =
    let
      items = Output.physicalOutputFiber
        (Audit.cutoff system) (Physical.p outer)
      whole =
        λ inner →
          R145.slotKernel
            (R167.normalizedDirection E S (Physical.p outer))
            (R167.normalizedDirection E S (Physical.q outer))
            (Inner.fourSignInner inner)
            (Audit.velocity system (Physical.q outer))
      split =
        λ inner →
          C3.complex3Add
            (homochiralSlot outer inner)
            (heterochiralSlot outer inner)
    in
    trans
      (foldCong whole split items
        (λ inner → fourSignSlotIsHomoPlusHetero outer inner))
      (R230.foldAdd
        (homochiralSlot outer)
        (heterochiralSlot outer)
        items)
    where
    foldCong :
      (f g : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
      (items : List Physical.PhysicalTriadIncidence) →
      ((x : Physical.PhysicalTriadIncidence) → f x ≡ g x) →
      R224.foldVector f items ≡ R224.foldVector g items
    foldCong f g [] pointwise = refl
    foldCong f g (x ∷ xs) pointwise =
      cong₂ C3.complex3Add
        (pointwise x)
        (foldCong f g xs pointwise)

  homochiralWeightedCompanionCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  homochiralWeightedCompanionCell outer
    with Output.modeEqual (Physical.p outer) Z3.zeroMode
  ... | true = C3.complex3Zero F
  ... | false =
    C3.complex3Scale (R294.weight W outer)
      (C3.complex3Scale (C3.complexI F) (homochiralSlotFold outer))

  heterochiralWeightedCompanionCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  heterochiralWeightedCompanionCell outer
    with Output.modeEqual (Physical.p outer) Z3.zeroMode
  ... | true = C3.complex3Zero F
  ... | false =
    C3.complex3Scale (R294.weight W outer)
      (C3.complex3Scale (C3.complexI F) (heterochiralSlotFold outer))

  nestedWeightedCellIsHomoPlusHetero :
    (outer : Physical.PhysicalTriadIncidence) →
    Nested.nestedWeightedCompanionCell outer
    ≡
    C3.complex3Add
      (homochiralWeightedCompanionCell outer)
      (heterochiralWeightedCompanionCell outer)
  nestedWeightedCellIsHomoPlusHetero outer
    with Output.modeEqual (Physical.p outer) Z3.zeroMode
  ... | true = sym R573.zeroPlusZero
  ... | false =
    trans
      (cong
        (λ value →
          C3.complex3Scale (R294.weight W outer)
            (C3.complex3Scale (C3.complexI F) value))
        (nestedSlotFoldIsHomoPlusHetero outer))
      (trans
        (cong
          (C3.complex3Scale (R294.weight W outer))
          (sym
            (R73.complex3ScaleAdd
              (C3.complexI F)
              (homochiralSlotFold outer)
              (heterochiralSlotFold outer))))
        (sym
          (R73.complex3ScaleAdd
            (R294.weight W outer)
            (C3.complex3Scale
              (C3.complexI F) (homochiralSlotFold outer))
            (C3.complex3Scale
              (C3.complexI F) (heterochiralSlotFold outer)))))

r573LiteralFourSignHelicitySplitClosed : Bool
r573LiteralFourSignHelicitySplitClosed = true

r573HomochiralPartEligibleForRadialTaylorRoute : Bool
r573HomochiralPartEligibleForRadialTaylorRoute = true

r573HeterochiralPartSilentlyPromotedToRadialTaylor : Bool
r573HeterochiralPartSilentlyPromotedToRadialTaylor = false

r573SplitIntroducesNormOrCardinalityTax : Bool
r573SplitIntroducesNormOrCardinalityTax = false

clayPromotion : Bool
clayPromotion = false

r573LiteralFourSignHelicitySplitClosedIsTrue :
  r573LiteralFourSignHelicitySplitClosed ≡ true
r573LiteralFourSignHelicitySplitClosedIsTrue = refl

r573HeterochiralPartSilentlyPromotedToRadialTaylorIsFalse :
  r573HeterochiralPartSilentlyPromotedToRadialTaylor ≡ false
r573HeterochiralPartSilentlyPromotedToRadialTaylorIsFalse = refl
