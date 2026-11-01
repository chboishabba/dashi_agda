module DASHI.Physics.YangMills.BalabanClayGate4NewtonFourChannelQuarterExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Four-channel quantitative Newton closure.
--
-- J. M. Holtzman,
-- "Explicit epsilon and delta for the Implicit Function Theorem",
-- SIAM Review 12 (1970), 284--286. DOI: 10.1137/1012051.
--
-- The Federbush centre and Faddeev--Popov slice have different operators but
-- the same analytic ownership pattern: geometry, contour/transport, chart and
-- inverse-seed errors.  Bounding each channel by 1/16 gives the common 1/4
-- target used by the invariant-ball construction.
------------------------------------------------------------------------

record FourChannelQuarterAlgebra (Bound : Set) : Set₁ where
  field
    add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    oneSixteenth quarter : Bound

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

    fourSixteenthsMeaning :
      add oneSixteenth
        (add oneSixteenth
          (add oneSixteenth oneSixteenth))
      ≡ quarter

open FourChannelQuarterAlgebra public

record NewtonFourChannelBudget
    {Bound : Set} (algebra : FourChannelQuarterAlgebra Bound) : Set₁ where
  field
    geometry contourTransport chart inverseSeed total : Bound

    totalMeaning :
      total
      ≡ add algebra geometry
          (add algebra contourTransport
            (add algebra chart inverseSeed))

    geometryBelowSixteenth :
      LessEqual algebra geometry (oneSixteenth algebra)
    contourTransportBelowSixteenth :
      LessEqual algebra contourTransport (oneSixteenth algebra)
    chartBelowSixteenth :
      LessEqual algebra chart (oneSixteenth algebra)
    inverseSeedBelowSixteenth :
      LessEqual algebra inverseSeed (oneSixteenth algebra)

open NewtonFourChannelBudget public

newtonFourChannelTotalBelowQuarter :
  ∀ {Bound}
    {algebra : FourChannelQuarterAlgebra Bound}
    (budget : NewtonFourChannelBudget algebra) →
  LessEqual algebra
    (total budget)
    (quarter algebra)
newtonFourChannelTotalBelowQuarter {algebra = algebra} budget =
  subst
    (λ selected → LessEqual algebra selected (quarter algebra))
    (sym (totalMeaning budget))
    (subst
      (λ selected →
        LessEqual algebra
          (add algebra (geometry budget)
            (add algebra (contourTransport budget)
              (add algebra (chart budget) (inverseSeed budget))))
          selected)
      (fourSixteenthsMeaning algebra)
      (addMonotone algebra
        (geometryBelowSixteenth budget)
        (addMonotone algebra
          (contourTransportBelowSixteenth budget)
          (addMonotone algebra
            (chartBelowSixteenth budget)
            (inverseSeedBelowSixteenth budget)))))

record FederbushFaddeevPopovFourChannelClosure
    {Bound : Set} (algebra : FourChannelQuarterAlgebra Bound) : Set₁ where
  field
    federbushContraction federbushForcing :
      NewtonFourChannelBudget algebra
    faddeevPopovContraction faddeevPopovForcing :
      NewtonFourChannelBudget algebra

open FederbushFaddeevPopovFourChannelClosure public

federbushContractionBelowQuarter :
  ∀ {Bound} {algebra : FourChannelQuarterAlgebra Bound} →
  (closure : FederbushFaddeevPopovFourChannelClosure algebra) →
  LessEqual algebra
    (total (federbushContraction closure)) (quarter algebra)
federbushContractionBelowQuarter closure =
  newtonFourChannelTotalBelowQuarter (federbushContraction closure)

federbushForcingBelowQuarter :
  ∀ {Bound} {algebra : FourChannelQuarterAlgebra Bound} →
  (closure : FederbushFaddeevPopovFourChannelClosure algebra) →
  LessEqual algebra
    (total (federbushForcing closure)) (quarter algebra)
federbushForcingBelowQuarter closure =
  newtonFourChannelTotalBelowQuarter (federbushForcing closure)

faddeevPopovContractionBelowQuarter :
  ∀ {Bound} {algebra : FourChannelQuarterAlgebra Bound} →
  (closure : FederbushFaddeevPopovFourChannelClosure algebra) →
  LessEqual algebra
    (total (faddeevPopovContraction closure)) (quarter algebra)
faddeevPopovContractionBelowQuarter closure =
  newtonFourChannelTotalBelowQuarter (faddeevPopovContraction closure)

faddeevPopovForcingBelowQuarter :
  ∀ {Bound} {algebra : FourChannelQuarterAlgebra Bound} →
  (closure : FederbushFaddeevPopovFourChannelClosure algebra) →
  LessEqual algebra
    (total (faddeevPopovForcing closure)) (quarter algebra)
faddeevPopovForcingBelowQuarter closure =
  newtonFourChannelTotalBelowQuarter (faddeevPopovForcing closure)

newtonFourChannelQuarterArithmeticLevel : ProofLevel
newtonFourChannelQuarterArithmeticLevel = machineChecked

federbushFaddeevPopovFourChannelReuseLevel : ProofLevel
federbushFaddeevPopovFourChannelReuseLevel = machineChecked

physicalFederbushChannelEstimatesInputsLevel : ProofLevel
physicalFederbushChannelEstimatesInputsLevel = conditional

physicalFaddeevPopovChannelEstimatesInputsLevel : ProofLevel
physicalFaddeevPopovChannelEstimatesInputsLevel = conditional
