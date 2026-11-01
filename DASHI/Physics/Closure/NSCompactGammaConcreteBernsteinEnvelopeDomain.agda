module DASHI.Physics.Closure.NSCompactGammaConcreteBernsteinEnvelopeDomain where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion
open import DASHI.Physics.Closure.NSCompactGammaAdmissiblePreservation

------------------------------------------------------------------------
-- BE1--BE8: concrete Bernstein-to-envelope dependency chain.
--
-- The two inequalities formerly presented as opaque fields of
-- ConcreteBernsteinEnvelopeConnection are theorem outputs below.  The leaves
-- now name the actual shell, reconstruction, Tonelli, compact-Gamma decay,
-- geometric summation, and normalization obligations.
------------------------------------------------------------------------

record ConcreteBernsteinEnvelopeLeaves
    {t : Level}
    (A : AbsorptionArithmetic)
    {Time : Set t}
    (C : ThreeWayAdditiveCalculus A)
    (R : ConcreteReserveLeaves A Time)
    (F : RealFundamentalTheoremRealization A C R) : Set (lsuc t) where
  field
    ShellState : Set t
    shellState : Time → ShellState

    shellVelocityL2 shellVorticityL2 shellVorticityLInfinity :
      Nat → ShellState → Scalar A
    curlWeightedShell bernsteinWeightedShell : Nat → ShellState → Scalar A
    weightedShellSum vorticityLInfinity envelope : ShellState → Scalar A

    shellCoefficient : Nat → Scalar A
    coefficientSumBound : Scalar A

    weightedShellIntegral vorticityIntegral : Scalar A
    coefficientWeightedEnvelopeIntegral : Scalar A

    -- BE1: the shell curl derivative contributes one dyadic derivative.
    shellCurlEstimate : ∀ j τ →
      _≤_ A
        (shellVorticityL2 j (shellState τ))
        (curlWeightedShell j (shellState τ))

    -- BE2: shell Bernstein, followed by BE1, gives the 5/2-weighted shell.
    shellBernsteinEstimate : ∀ j τ →
      _≤_ A
        (shellVorticityLInfinity j (shellState τ))
        (bernsteinWeightedShell j (shellState τ))

    curlThenBernsteinFiveHalves : ∀ j τ →
      _≤_ A
        (bernsteinWeightedShell j (shellState τ))
        (curlWeightedShell j (shellState τ))

    curlWeightedShellMeaning : ∀ j state →
      curlWeightedShell j state ≡ shellVelocityL2 j state

    -- BE3: Littlewood--Paley reconstruction in a topology controlling L-infinity.
    vorticityReconstruction : ∀ τ →
      _≤_ A
        (vorticityLInfinity (shellState τ))
        (weightedShellSum (shellState τ))

    -- BE4: Tonelli/monotone convergence transports BE3 through time integration.
    integratedVorticityReconstruction :
      (∀ τ →
        _≤_ A
          (vorticityLInfinity (shellState τ))
          (weightedShellSum (shellState τ))) →
      _≤_ A vorticityIntegral weightedShellIntegral

    -- BE5: compact-Gamma shell decay, including the intended
    -- C 2^(-sigma |j-K|) coefficient in the selected scalar realization.
    compactGammaShellDecay : ∀ j τ →
      _≤_ A
        (curlWeightedShell j (shellState τ))
        (shellCoefficient j)

    shellCoefficientBelowEnvelope : ∀ j τ →
      _≤_ A
        (shellCoefficient j)
        (envelope (shellState τ))

    -- BE6: the geometric coefficient family is uniformly summable in K.
    geometricCoefficientSummation : ∀ τ →
      _≤_ A
        (weightedShellSum (shellState τ))
        (coefficientSumBound)

    coefficientSumBelowEnvelope : ∀ τ →
      _≤_ A coefficientSumBound (envelope (shellState τ))

    -- BE7: integrate the nonnegative shell series after BE5--BE6.
    integrateWeightedShellEnvelope :
      (∀ τ →
        _≤_ A
          (weightedShellSum (shellState τ))
          (envelope (shellState τ))) →
      _≤_ A weightedShellIntegral coefficientWeightedEnvelopeIntegral

    -- BE8: explicit normalization of C_sigma into the coercive rate.
    normalizeCoefficientIntoCoerciveRate :
      _≤_ A coefficientWeightedEnvelopeIntegral (coerciveIntegral F)

open ConcreteBernsteinEnvelopeLeaves public

BE1-shell-curl :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : ThreeWayAdditiveCalculus A}
    {R : ConcreteReserveLeaves A Time}
    {F : RealFundamentalTheoremRealization A C R} →
  (B : ConcreteBernsteinEnvelopeLeaves A C R F) → ∀ j τ →
  _≤_ A
    (shellVorticityL2 B j (shellState B τ))
    (curlWeightedShell B j (shellState B τ))
BE1-shell-curl B = shellCurlEstimate B

BE2-shell-Bernstein-five-halves :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : ThreeWayAdditiveCalculus A}
    {R : ConcreteReserveLeaves A Time}
    {F : RealFundamentalTheoremRealization A C R} →
  (B : ConcreteBernsteinEnvelopeLeaves A C R F) → ∀ j τ →
  _≤_ A
    (shellVorticityLInfinity B j (shellState B τ))
    (curlWeightedShell B j (shellState B τ))
BE2-shell-Bernstein-five-halves {A = A} B j τ =
  ≤-trans A
    (shellBernsteinEstimate B j τ)
    (curlThenBernsteinFiveHalves B j τ)

BE3-vorticity-reconstruction :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : ThreeWayAdditiveCalculus A}
    {R : ConcreteReserveLeaves A Time}
    {F : RealFundamentalTheoremRealization A C R} →
  (B : ConcreteBernsteinEnvelopeLeaves A C R F) → ∀ τ →
  _≤_ A
    (vorticityLInfinity B (shellState B τ))
    (weightedShellSum B (shellState B τ))
BE3-vorticity-reconstruction B = vorticityReconstruction B

BE4-integrated-vorticity-reconstruction :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : ThreeWayAdditiveCalculus A}
    {R : ConcreteReserveLeaves A Time}
    {F : RealFundamentalTheoremRealization A C R} →
  (B : ConcreteBernsteinEnvelopeLeaves A C R F) →
  _≤_ A (vorticityIntegral B) (weightedShellIntegral B)
BE4-integrated-vorticity-reconstruction B =
  integratedVorticityReconstruction B (BE3-vorticity-reconstruction B)

BE5-compactGamma-shell-decay :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : ThreeWayAdditiveCalculus A}
    {R : ConcreteReserveLeaves A Time}
    {F : RealFundamentalTheoremRealization A C R} →
  (B : ConcreteBernsteinEnvelopeLeaves A C R F) → ∀ j τ →
  _≤_ A
    (curlWeightedShell B j (shellState B τ))
    (envelope B (shellState B τ))
BE5-compactGamma-shell-decay {A = A} B j τ =
  ≤-trans A
    (compactGammaShellDecay B j τ)
    (shellCoefficientBelowEnvelope B j τ)

BE6-uniform-geometric-shell-sum :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : ThreeWayAdditiveCalculus A}
    {R : ConcreteReserveLeaves A Time}
    {F : RealFundamentalTheoremRealization A C R} →
  (B : ConcreteBernsteinEnvelopeLeaves A C R F) → ∀ τ →
  _≤_ A
    (weightedShellSum B (shellState B τ))
    (envelope B (shellState B τ))
BE6-uniform-geometric-shell-sum {A = A} B τ =
  ≤-trans A
    (geometricCoefficientSummation B τ)
    (coefficientSumBelowEnvelope B τ)

BE7-weighted-shell-below-coercive-envelope :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    {C : ThreeWayAdditiveCalculus A}
    {R : ConcreteReserveLeaves A Time}
    {F : RealFundamentalTheoremRealization A C R} →
  (B : ConcreteBernsteinEnvelopeLeaves A C R F) →
  _≤_ A (weightedShellIntegral B) (coerciveIntegral F)
BE7-weighted-shell-below-coercive-envelope {A = A} B =
  ≤-trans A
    (integrateWeightedShellEnvelope B
      (BE6-uniform-geometric-shell-sum B))
    (normalizeCoefficientIntoCoerciveRate B)

BE8-normalized-concrete-connection :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    (C : ThreeWayAdditiveCalculus A)
    (R : ConcreteReserveLeaves A Time)
    (F : RealFundamentalTheoremRealization A C R) →
  ConcreteBernsteinEnvelopeLeaves A C R F →
  ConcreteBernsteinEnvelopeConnection A C R F
BE8-normalized-concrete-connection C R F B = record
  { weightedShellIntegral = weightedShellIntegral B
  ; vorticityIntegral = vorticityIntegral B
  ; bernsteinShellSumBelowEnvelope =
      BE7-weighted-shell-below-coercive-envelope B
  ; vorticityReconstructionBelowShellSum =
      BE4-integrated-vorticity-reconstruction B
  }

------------------------------------------------------------------------
-- D1--D5: strict invariant-region domain and chain-rule consumption.
------------------------------------------------------------------------

record StrictThresholdDomain
    {s : Level}
    (O : OrderedScalar s)
    (B : CompactGammaThresholds O) : Set (lsuc s) where
  field
    Positive : Scalar O → Set s
    positiveAbove : ∀ {a b} → Positive a → _≤_ O a b → Positive b
    gammaFloorPositive : Positive (gammaFloor B)
    energyFloorPositive : Positive (energyFloor B)

open StrictThresholdDomain public

record BarrierRegularityStructure
    {s t : Level}
    (O : OrderedScalar s)
    (Time : Set t) : Set (lsuc (s ⊔ t)) where
  field
    reciprocal logarithm : Scalar O → Scalar O
    Bounded Regular : (Time → Scalar O) → Set (s ⊔ t)

open BarrierRegularityStructure public

record InvariantBarrierDomain
    {s t st sh : Level}
    {O : OrderedScalar s}
    {Time : Set t}
    {State : Set st}
    {Shell : Set sh}
    (S : CompactGammaSystem O State Shell)
    (B : CompactGammaThresholds O)
    (p : Path Time State)
    (K : Shell)
    (strict : StrictThresholdDomain O B)
    (regularity : BarrierRegularityStructure O Time) :
    Set (lsuc (s ⊔ t ⊔ st ⊔ sh)) where
  field
    completeness : FirstExitCompleteness S B p K
    noExitInputs : NoFirstExitInputs {S = S} {B = B} p K

    -- The strict upper barrier is the strict-margin consequence supplied by
    -- the no-first-exit proof, not an unrelated logarithm-domain assumption.
    StrictlyBelow : Scalar O → Scalar O → Set s
    strictOffPacketFromInvariant : ∀ τ →
      CompactGammaAdmissible S B K (at p τ) →
      StrictlyBelow
        (offPacketRatio S K (at p τ))
        (offPacketCeiling B)

    barrierGap : Time → Scalar O
    barrierGapMeaning : ∀ τ → Set s

    reciprocalPacketBounded reciprocalGammaBounded reciprocalBarrierBounded :
      Set (s ⊔ t)
    reciprocalPacketRegular reciprocalGammaRegular reciprocalBarrierRegular :
      Set (s ⊔ t)

    reciprocalPacketBoundedMeaning :
      reciprocalPacketBounded ≡
        Bounded regularity
          (λ τ → reciprocal regularity (packetEnergy S K (at p τ)))
    reciprocalGammaBoundedMeaning :
      reciprocalGammaBounded ≡
        Bounded regularity
          (λ τ → reciprocal regularity (gamma S K (at p τ)))
    reciprocalBarrierBoundedMeaning :
      reciprocalBarrierBounded ≡
        Bounded regularity
          (λ τ → reciprocal regularity (barrierGap τ))

    reciprocalPacketRegularMeaning :
      reciprocalPacketRegular ≡
        Regular regularity
          (λ τ → reciprocal regularity (packetEnergy S K (at p τ)))
    reciprocalGammaRegularMeaning :
      reciprocalGammaRegular ≡
        Regular regularity
          (λ τ → reciprocal regularity (gamma S K (at p τ)))
    reciprocalBarrierRegularMeaning :
      reciprocalBarrierRegular ≡
        Regular regularity
          (λ τ → reciprocal regularity (barrierGap τ))

open InvariantBarrierDomain public

invariant-admissible :
  ∀ {s t st sh}
    {O : OrderedScalar s} {Time : Set t} {State : Set st} {Shell : Set sh}
    {S : CompactGammaSystem O State Shell}
    {B : CompactGammaThresholds O}
    {p : Path Time State} {K : Shell}
    {strict : StrictThresholdDomain O B}
    {regularity : BarrierRegularityStructure O Time} →
  (D : InvariantBarrierDomain S B p K strict regularity) → ∀ τ →
  CompactGammaAdmissible S B K (at p τ)
invariant-admissible D =
  compactGammaInvariantRegion (completeness D) (noExitInputs D)

D1-packet-denominator-positive :
  ∀ {s t st sh}
    {O : OrderedScalar s} {Time : Set t} {State : Set st} {Shell : Set sh}
    {S : CompactGammaSystem O State Shell}
    {B : CompactGammaThresholds O}
    {p : Path Time State} {K : Shell}
    {strict : StrictThresholdDomain O B}
    {regularity : BarrierRegularityStructure O Time} →
  (D : InvariantBarrierDomain S B p K strict regularity) → ∀ τ →
  Positive strict (packetEnergy S K (at p τ))
D1-packet-denominator-positive D τ =
  positiveAbove _ (energyFloorPositive _)
    (packetEnergyAboveFloor (invariant-admissible D τ))

D2-gamma-positive :
  ∀ {s t st sh}
    {O : OrderedScalar s} {Time : Set t} {State : Set st} {Shell : Set sh}
    {S : CompactGammaSystem O State Shell}
    {B : CompactGammaThresholds O}
    {p : Path Time State} {K : Shell}
    {strict : StrictThresholdDomain O B}
    {regularity : BarrierRegularityStructure O Time} →
  (D : InvariantBarrierDomain S B p K strict regularity) → ∀ τ →
  Positive strict (gamma S K (at p τ))
D2-gamma-positive D τ =
  positiveAbove _ (gammaFloorPositive _)
    (gammaAboveFloor (invariant-admissible D τ))

D3-off-packet-strict-barrier :
  ∀ {s t st sh}
    {O : OrderedScalar s} {Time : Set t} {State : Set st} {Shell : Set sh}
    {S : CompactGammaSystem O State Shell}
    {B : CompactGammaThresholds O}
    {p : Path Time State} {K : Shell}
    {strict : StrictThresholdDomain O B}
    {regularity : BarrierRegularityStructure O Time} →
  (D : InvariantBarrierDomain S B p K strict regularity) → ∀ τ →
  StrictlyBelow D
    (offPacketRatio S K (at p τ))
    (offPacketCeiling B)
D3-off-packet-strict-barrier D τ =
  strictOffPacketFromInvariant D τ (invariant-admissible D τ)

record BarrierChainRule
    {s t st sh : Level}
    {O : OrderedScalar s}
    {Time : Set t}
    {State : Set st}
    {Shell : Set sh}
    {S : CompactGammaSystem O State Shell}
    {B : CompactGammaThresholds O}
    {p : Path Time State}
    {K : Shell}
    {strict : StrictThresholdDomain O B}
    {regularity : BarrierRegularityStructure O Time}
    (D : InvariantBarrierDomain S B p K strict regularity) :
    Set (lsuc (s ⊔ t ⊔ st ⊔ sh)) where
  field
    DerivativeIdentity : Time → Set (s ⊔ t)
    deriveWithInvariantDomain :
      (∀ τ → Positive strict (packetEnergy S K (at p τ))) →
      (∀ τ → Positive strict (gamma S K (at p τ))) →
      (∀ τ → StrictlyBelow D
        (offPacketRatio S K (at p τ)) (offPacketCeiling B)) →
      (∀ τ → DerivativeIdentity τ)

open BarrierChainRule public

D4-reciprocal-log-regularity :
  ∀ {s t st sh}
    {O : OrderedScalar s} {Time : Set t} {State : Set st} {Shell : Set sh}
    {S : CompactGammaSystem O State Shell}
    {B : CompactGammaThresholds O}
    {p : Path Time State} {K : Shell}
    {strict : StrictThresholdDomain O B}
    {regularity : BarrierRegularityStructure O Time} →
  (D : InvariantBarrierDomain S B p K strict regularity) →
  Set (s ⊔ t)
D4-reciprocal-log-regularity D =
  reciprocalPacketBounded D

D5-invariant-evidence-feeds-chain-rules :
  ∀ {s t st sh}
    {O : OrderedScalar s} {Time : Set t} {State : Set st} {Shell : Set sh}
    {S : CompactGammaSystem O State Shell}
    {B : CompactGammaThresholds O}
    {p : Path Time State} {K : Shell}
    {strict : StrictThresholdDomain O B}
    {regularity : BarrierRegularityStructure O Time} →
  (D : InvariantBarrierDomain S B p K strict regularity) →
  (chain : BarrierChainRule D) →
  ∀ τ → DerivativeIdentity chain τ
D5-invariant-evidence-feeds-chain-rules D chain =
  deriveWithInvariantDomain chain
    (D1-packet-denominator-positive D)
    (D2-gamma-positive D)
    (D3-off-packet-strict-barrier D)
