module DASHI.Analysis.RiemannG2LiteralResponseNormalizedAnalyticCoresExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core

------------------------------------------------------------------------
-- LITERAL-RESPONSE NORMALIZATION
--
-- The terminal consumers only require source-order upper bounds.  Therefore an
-- intermediate channel budget need not be a separately estimated larger scalar.
-- At one selected cutoff J we may choose
--
--   B_near(J) := D_near(J)
--
-- and use source-order reflexivity.  The independently transported far-shell
-- bound is retained, so the resulting Off budget is
--
--   B_off(J) := D_near(J) + B_far(J).
--
-- Likewise Gamma may use
--
--   B_Gamma(g) := D_Gamma(g)
--
-- with source-order reflexivity.  This does NOT make the final theorem free:
-- all quantitative burden is moved to the final independently proved strict
-- complement-margin theorem.  In particular no budget may be manufactured from
-- the final cluster = Off + Gamma balance identity.
------------------------------------------------------------------------

record NearResponseNormalizedOffCoreInput
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    chosenCutoff : Transport.Cutoff transport

    sourceOrderReflexive :
      (x : NearFar.Scalar S) -> NearFar._≤_ S x x

    independentOfFinalBalanceIdentity : Set
    independentOfFinalBalanceIdentityReceipt :
      independentOfFinalBalanceIdentity

    analyticReference : String

open NearResponseNormalizedOffCoreInput public

literalNearFarBudget :
  forall {S transport} ->
  NearResponseNormalizedOffCoreInput S transport ->
  NearFar.NearFarOffOrdinateBudget S
literalNearFarBudget {S = S} {transport = transport} input =
  NearFar.near-far-off-ordinate-budget
    (Transport.fullResponse transport
      (Transport.universalPoleQuotientTaper transport))
    (Transport.nearResponseAt transport (chosenCutoff input))
    (Transport.farRemainderAt transport (chosenCutoff input))
    (Transport.nearResponseAt transport (chosenCutoff input))
    (Transport.farBudgetAt transport (chosenCutoff input))
    (Transport.fullBelowNearPlusFarAt transport (chosenCutoff input))
    (sourceOrderReflexive input
      (Transport.nearResponseAt transport (chosenCutoff input)))
    (Transport.farUpperAt transport (chosenCutoff input))

literalOffBudget :
  forall {S transport} ->
  NearResponseNormalizedOffCoreInput S transport ->
  Transport.Taper transport ->
  NearFar.Scalar S
literalOffBudget {S = S} {transport = transport} input taper =
  NearFar.add S
    (Transport.nearResponseAt transport (chosenCutoff input))
    (Transport.farBudgetAt transport (chosenCutoff input))

compileLiteralOffTarget :
  forall {S transport} ->
  NearResponseNormalizedOffCoreInput S transport ->
  Off.PoleQuotientOffOrdinateBudgetTarget
compileLiteralOffTarget {S = S} {transport = transport} input =
  Off.pole-quotient-off-ordinate-budget-target
    (NearFar.Scalar S)
    (Transport.Taper transport)
    (Transport.fullResponse transport)
    (literalOffBudget input)
    (NearFar._≤_ S)
    (Transport.universalPoleQuotientTaper transport)
    (NearFar.compiledOffOrdinateUpper S (literalNearFarBudget input))

compileLiteralOffCore :
  forall {S transport} ->
  NearResponseNormalizedOffCoreInput S transport ->
  Core.OffAnalyticCore
compileLiteralOffCore {S = S} {transport = transport} input =
  Core.off-analytic-core
    (compileLiteralOffTarget input)
    (literalOffBudget input (Transport.universalPoleQuotientTaper transport))
    (sourceOrderReflexive input
      (literalOffBudget input (Transport.universalPoleQuotientTaper transport)))
    (analyticReference input)

literalOffAllowanceIsBudget :
  forall {S transport} ->
  (input : NearResponseNormalizedOffCoreInput S transport) ->
  let core = compileLiteralOffCore input
      target = Core.OffAnalyticCore.target core
  in Core.OffAnalyticCore.assignedOffAllowance core
     ≡ Off.OffOrdinateBudget target (Off.universalPoleQuotientTaper target)
literalOffAllowanceIsBudget input = refl

------------------------------------------------------------------------
-- GAMMA: RESPONSE ITSELF IS THE LEAST-PRIVILEGE SOURCE-ORDER UPPER.
------------------------------------------------------------------------

record ResponseNormalizedGammaCoreInput : Set₁ where
  field
    Scalar : Set
    Taper : Set
    _≤_ : Scalar -> Scalar -> Set

    gammaResponse : Taper -> Scalar
    universalPoleQuotientTaper : Taper

    sourceOrderReflexive : (x : Scalar) -> _≤_ x x

    independentOfFinalBalanceIdentity : Set
    independentOfFinalBalanceIdentityReceipt :
      independentOfFinalBalanceIdentity

    analyticReference : String

open ResponseNormalizedGammaCoreInput public

compileLiteralGammaTarget :
  ResponseNormalizedGammaCoreInput ->
  Gamma.PoleQuotientGammaBudgetTarget
compileLiteralGammaTarget input =
  Gamma.pole-quotient-gamma-budget-target
    (Scalar input)
    (Taper input)
    (gammaResponse input)
    (gammaResponse input)
    (_≤_ input)
    (universalPoleQuotientTaper input)
    (sourceOrderReflexive input
      (gammaResponse input (universalPoleQuotientTaper input)))

compileLiteralGammaCore :
  ResponseNormalizedGammaCoreInput ->
  Core.GammaAnalyticCore
compileLiteralGammaCore input =
  Core.gamma-analytic-core
    (compileLiteralGammaTarget input)
    (gammaResponse input (universalPoleQuotientTaper input))
    (sourceOrderReflexive input
      (gammaResponse input (universalPoleQuotientTaper input)))
    (analyticReference input)

literalGammaAllowanceIsBudget :
  (input : ResponseNormalizedGammaCoreInput) ->
  let core = compileLiteralGammaCore input
      target = Core.GammaAnalyticCore.target core
  in Core.GammaAnalyticCore.assignedGammaAllowance core
     ≡ Gamma.GammaBudget target (Gamma.universalPoleQuotientTaper target)
literalGammaAllowanceIsBudget input = refl

------------------------------------------------------------------------
-- PAIR COMPILER
------------------------------------------------------------------------

record LiteralResponseNormalizedCorePair
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    offInput : NearResponseNormalizedOffCoreInput S transport
    gammaInput : ResponseNormalizedGammaCoreInput
    pairReference : String

open LiteralResponseNormalizedCorePair public

compiledLiteralCores :
  forall {S transport} ->
  LiteralResponseNormalizedCorePair S transport ->
  Core.FinalPoleQuotientTwoAnalyticCores
compiledLiteralCores pair =
  Core.final-pole-quotient-two-analytic-cores
    (compileLiteralOffCore (offInput pair))
    (compileLiteralGammaCore (gammaInput pair))
    (pairReference pair)

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record LiteralResponseNormalizedBoundary : Set where
  constructor literal-response-normalized-boundary
  field
    separateFiniteNearUpperScalarRequired : Bool
    separateFiniteNearUpperScalarRequiredIsFalse :
      separateFiniteNearUpperScalarRequired ≡ false

    transportedFarShellUpperStillRequired : Bool
    transportedFarShellUpperStillRequiredIsTrue :
      transportedFarShellUpperStillRequired ≡ true

    separateGammaEnvelopeScalarRequired : Bool
    separateGammaEnvelopeScalarRequiredIsFalse :
      separateGammaEnvelopeScalarRequired ≡ false

    sourceOrderReflexivityStillRequired : Bool
    sourceOrderReflexivityStillRequiredIsTrue :
      sourceOrderReflexivityStillRequired ≡ true

    independentFinalComplementEstimateStillRequired : Bool
    independentFinalComplementEstimateStillRequiredIsTrue :
      independentFinalComplementEstimateStillRequired ≡ true

    finalBalanceMayManufactureComplementEstimate : Bool
    finalBalanceMayManufactureComplementEstimateIsFalse :
      finalBalanceMayManufactureComplementEstimate ≡ false

    channelCoresCompileWithoutSeparateUpperEnvelopes : Bool
    channelCoresCompileWithoutSeparateUpperEnvelopesIsTrue :
      channelCoresCompileWithoutSeparateUpperEnvelopes ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalLiteralResponseNormalizedBoundary :
  LiteralResponseNormalizedBoundary
canonicalLiteralResponseNormalizedBoundary =
  literal-response-normalized-boundary
    false refl
    true refl
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
    "The least-privilege source-order budgets may be the literal channel responses themselves. At the chosen cutoff, set B_near=D_near and retain only the independently transported far-shell budget, giving B_off=D_near+B_far. Set B_Gamma=D_Gamma. The resulting channel upper and allowance-fit fields are source-order reflexivity, not new harmonic/Gamma estimates. This does not evade the 8889 budget-circularity no-go: the final strict complement estimate must still be proved independently of cluster=Off+Gamma, on the same literal carrier. RH is not derived here."
