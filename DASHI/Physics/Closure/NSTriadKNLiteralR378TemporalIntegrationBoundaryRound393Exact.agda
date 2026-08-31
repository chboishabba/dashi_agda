module DASHI.Physics.Closure.NSTriadKNLiteralR378TemporalIntegrationBoundaryRound393Exact where

------------------------------------------------------------------------
-- ROUND393 / THE ACTUAL TEMPORAL LEAF AFTER THE R378 -> R392 SAME-OBJECT WELD
--
-- R392 has removed all finite carrier ambiguity: at every time the literal
-- global R378 Gram debt has the instantaneous shape
--
--   D(t) = -F'(t) + R(t).
--
-- What remains is ordinary real-time analysis, but it must still be stated on
-- these SAME observables.  This module isolates exactly that authority rather
-- than hiding it inside the scalar R303 payment record.
--
-- A realization supplies one interval integral, integrability of the literal
-- rates, integral linearity/negation, and the endpoint fundamental theorem for
-- the literal off-diagonal flux.  From those leaves we prove
--
--   integral D = F(0) - F(T) + integral R.
--
-- No endpoint estimate and no remainder estimate is used here.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record LiteralR378TemporalRealization {t : Level} (Time : Set t) : Set (lsuc t) where
  field
    initialTime finalTime : Time

    literalGlobalGramDebt : Time → ℚ
    literalOffDiagonalFlux : Time → ℚ
    literalOffDiagonalFluxTangent : Time → ℚ
    literalWeightedRemainder : Time → ℚ

    instantaneousR392Identity :
      (τ : Time) →
      literalGlobalGramDebt τ
      ≡ (0ℚ - literalOffDiagonalFluxTangent τ)
          + literalWeightedRemainder τ

    Integrable : (Time → ℚ) → Set
    Integral : (Time → ℚ) → ℚ

    gramDebtIntegrable : Integrable literalGlobalGramDebt
    fluxTangentIntegrable : Integrable literalOffDiagonalFluxTangent
    negatedFluxTangentIntegrable :
      Integrable (λ τ → 0ℚ - literalOffDiagonalFluxTangent τ)
    weightedRemainderIntegrable : Integrable literalWeightedRemainder

    integralCongruence :
      ∀ {f g} → ((τ : Time) → f τ ≡ g τ) → Integral f ≡ Integral g

    integralAdditive :
      ∀ {f g} → Integrable f → Integrable g →
      Integral (λ τ → f τ + g τ) ≡ Integral f + Integral g

    integralNegation :
      ∀ {f} → Integrable f →
      Integral (λ τ → 0ℚ - f τ) ≡ 0ℚ - Integral f

    offDiagonalFundamentalTheorem :
      Integral literalOffDiagonalFluxTangent
      ≡ literalOffDiagonalFlux finalTime - literalOffDiagonalFlux initialTime

open LiteralR378TemporalRealization public

literalR378IntegratedGramFluxIdentity :
  ∀ {t} {Time : Set t} →
  (R : LiteralR378TemporalRealization Time) →
  Integral R (literalGlobalGramDebt R)
  ≡
  literalOffDiagonalFlux R (initialTime R)
  - literalOffDiagonalFlux R (finalTime R)
  + Integral R (literalWeightedRemainder R)
literalR378IntegratedGramFluxIdentity {Time = Time} R =
  let
    pointwise :
      (τ : Time) →
      literalGlobalGramDebt R τ
      ≡ (0ℚ - literalOffDiagonalFluxTangent R τ)
          + literalWeightedRemainder R τ
    pointwise = instantaneousR392Identity R

    congruent = integralCongruence R pointwise

    add = integralAdditive R
      (negatedFluxTangentIntegrable R)
      (weightedRemainderIntegrable R)

    neg = integralNegation R (fluxTangentIntegrable R)
    ftc = offDiagonalFundamentalTheorem R
  in
  trans congruent
    (trans add
      (trans
        (cong (λ x → x + Integral R (literalWeightedRemainder R)) neg)
        (trans
          (cong
            (λ x → (0ℚ - x) + Integral R (literalWeightedRemainder R))
            ftc)
          (solve
            ( literalOffDiagonalFlux R (initialTime R)
            ∷ literalOffDiagonalFlux R (finalTime R)
            ∷ Integral R (literalWeightedRemainder R)
            ∷ [])))))

round393LiteralTemporalCarrierIdentified : Bool
round393LiteralTemporalCarrierIdentified = true

round393EndpointFundamentalTheoremStillAnalyticLeaf : Bool
round393EndpointFundamentalTheoremStillAnalyticLeaf = true

round393R303ScalarSubstitutionUsed : Bool
round393R303ScalarSubstitutionUsed = false

round393LiteralTemporalCarrierIdentifiedIsTrue :
  round393LiteralTemporalCarrierIdentified ≡ true
round393LiteralTemporalCarrierIdentifiedIsTrue = refl
