{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact where

------------------------------------------------------------------------
-- ROUND414 / POSITIVE CONNECTING-DOMAIN SUM RETAINS SELECTED DISTANCE DECAY
--
-- This is the missing algebraic part of P0c after R404/R405.
--
-- If every surviving localization domain Y connects both selected source
-- supports, then Round411 gives
--
--   d_selected <= d_Y.
--
-- For any nonnegative antitone decay weight W this gives W(d_Y) <= W(d_sel).
-- Thus a positive outer family
--
--   shell_Y <= A_Y W(d_Y)
--
-- satisfies
--
--   sum_Y shell_Y <= (sum_Y A_Y) W(d_sel)
--                   <= A_src W(d_sel).
--
-- The proof below is finite ordered-real algebra.  It does not assume a
-- cardinality factor and it does not hide the amplitude sum in a final bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as Nat
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _+ℝ_ ; _*ℝ_ ; _≤ℝ_
  ; ≤ℝ-refl ; ≤ℝ-trans ; +-mono-≤ ; +-identityˡ
  ; *-distribʳ-+ ; mulMonotoneNonnegative ; mulZeroˡ )
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411

record AntitoneNonnegativeDecayWeight : Set₁ where
  field
    weight : Nat → ℝ
    weightNonnegative : ∀ distance → 0ℝ ≤ℝ weight distance
    weightAntitone : ∀ {near far} →
      Nat._≤_ near far →
      weight far ≤ℝ weight near

open AntitoneNonnegativeDecayWeight public

sumScaledRight :
  ∀ {A : Set}
    (values : A → ℝ) (xs : List A) factor →
  Resum.sumℝ (λ x → values x *ℝ factor) xs
  ≡ Resum.sumℝ values xs *ℝ factor
sumScaledRight values [] factor = sym
  (mulZeroˡ factor)
sumScaledRight values (x ∷ xs) factor
  rewrite sumScaledRight values xs factor =
  sym (*-distribʳ-+ (values x) (Resum.sumℝ values xs) factor)

sumNonnegative :
  ∀ {A : Set}
    (values : A → ℝ) (xs : List A) →
  (∀ x → 0ℝ ≤ℝ values x) →
  0ℝ ≤ℝ Resum.sumℝ values xs
sumNonnegative values xs pointwise =
  subst
    (λ lower → lower ≤ℝ Resum.sumℝ values xs)
    (sym (Resum.sumℝ-zero xs))
    (Resum.sumℝ-mono xs pointwise)

record ConnectingOuterSumData
    (Domain Term : Set)
    (geometry : R411.SelectedSupportConnectionGeometry Domain Term)
    (decay : AntitoneNonnegativeDecayWeight) : Set₁ where
  field
    localizedDomains : List Domain

    -- Domain is the already-filtered surviving/connecting family.
    everyLocalizedDomainConnects :
      ∀ domain → R411.domainConnectsBothSupports geometry domain

    domainAmplitude : Domain → ℝ
    domainAmplitudeNonnegative :
      ∀ domain → 0ℝ ≤ℝ domainAmplitude domain

    commonYShell : Domain → ℝ

    commonYShellBelowDomainDecay :
      ∀ domain →
      commonYShell domain
      ≤ℝ domainAmplitude domain
          *ℝ weight decay (R411.domainTreeDistance geometry domain)

    sourceAmplitude : ℝ
    amplitudeSumBelowSourceAmplitude :
      Resum.sumℝ domainAmplitude localizedDomains
      ≤ℝ sourceAmplitude

open ConnectingOuterSumData public

domainShellBelowSelectedDecay :
  ∀ {Domain Term geometry decay}
    (dataSet : ConnectingOuterSumData Domain Term geometry decay)
    domain →
  commonYShell dataSet domain
  ≤ℝ domainAmplitude dataSet domain
      *ℝ weight decay (R411.selectedConnectingDistance geometry)
domainShellBelowSelectedDecay {geometry = geometry} {decay = decay}
    dataSet domain =
  let
    decayOrder =
      weightAntitone decay
        (R411.supportConnectionForcesDistanceLower geometry domain
          (everyLocalizedDomainConnects dataSet domain))

    scaledDecay =
      mulMonotoneNonnegative
        (domainAmplitudeNonnegative dataSet domain)
        ≤ℝ-refl
        (weightNonnegative decay (R411.domainTreeDistance geometry domain))
        decayOrder
  in
  ≤ℝ-trans
    (commonYShellBelowDomainDecay dataSet domain)
    scaledDecay

connectingOuterSumBelowSelectedDecay :
  ∀ {Domain Term geometry decay}
    (dataSet : ConnectingOuterSumData Domain Term geometry decay) →
  Resum.sumℝ (commonYShell dataSet) (localizedDomains dataSet)
  ≤ℝ
  sourceAmplitude dataSet
    *ℝ weight decay (R411.selectedConnectingDistance geometry)
connectingOuterSumBelowSelectedDecay {geometry = geometry} {decay = decay}
    dataSet =
  let
    pointwise =
      Resum.sumℝ-mono
        (localizedDomains dataSet)
        (domainShellBelowSelectedDecay dataSet)

    factorized :
      Resum.sumℝ
        (λ domain →
          domainAmplitude dataSet domain
            *ℝ weight decay (R411.selectedConnectingDistance geometry))
        (localizedDomains dataSet)
      ≡
      Resum.sumℝ (domainAmplitude dataSet) (localizedDomains dataSet)
        *ℝ weight decay (R411.selectedConnectingDistance geometry)
    factorized =
      sumScaledRight
        (domainAmplitude dataSet)
        (localizedDomains dataSet)
        (weight decay (R411.selectedConnectingDistance geometry))

    sumAmplitudeNN =
      sumNonnegative
        (domainAmplitude dataSet)
        (localizedDomains dataSet)
        (domainAmplitudeNonnegative dataSet)

    amplitudeScaled =
      mulMonotoneNonnegative
        sumAmplitudeNN
        (amplitudeSumBelowSourceAmplitude dataSet)
        (weightNonnegative decay (R411.selectedConnectingDistance geometry))
        ≤ℝ-refl

    factoredBound =
      subst
        (λ middle →
          Resum.sumℝ (commonYShell dataSet) (localizedDomains dataSet)
          ≤ℝ middle)
        factorized
        pointwise
  in
  ≤ℝ-trans factoredBound amplitudeScaled

round414ConnectingOuterSumCompilerLevel : ProofLevel
round414ConnectingOuterSumCompilerLevel = machineChecked

-- Remaining source-counting input is now explicit:
-- produce per-domain nonnegative amplitudes whose finite sum is uniformly
-- bounded, and prove each common-Y shell retains the domain/tree decay weight.
-- The selected-distance extraction and factorization of the common decay are
-- compiler-owned above.
literalCMP116DomainAmplitudeAndTreeWeightSummabilityLevel : ProofLevel
literalCMP116DomainAmplitudeAndTreeWeightSummabilityLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
