module DASHI.Physics.Closure.NSPeriodicCanonicalWallIMarginAdapter where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicWallIHarmonicCompletion as WallI
import DASHI.Physics.Closure.NSPeriodicNearTriadCutoffUniformCompletion as Near
import DASHI.Physics.Closure.NSPeriodicFarLowOfficialSchurCompletion as Low
import DASHI.Physics.Closure.NSPeriodicFarHighTailCompletion as High
import DASHI.Physics.Closure.NSPeriodicCanonicalStrictMarginCertificate as Canonical
import DASHI.Physics.Closure.NSPeriodicCanonicalStrictMarginInterpretation as Interpretation
import DASHI.Physics.Closure.NSPeriodicStrictDissipationMargin as Margin
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact Wall-I to strict-margin constructor.
--
-- The canonical scalar certificate assigns 1/4 to near triads and 1/8 to each
-- far tail, leaving 1/2 of normalized viscosity.  This module derives the
-- strict-margin record directly from the three official component estimates.
-- The only quantitative obligations are that their literal budgets fit those
-- canonical shares in the selected scalar interpretation.
------------------------------------------------------------------------

record CanonicalWallIMarginInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index Time State : Set i) : Set (lsuc i) where
  field
    wallI : WallI.PeriodicWallIHarmonicInputs A Index Time State

    interpretDyadic : Nat → Scalar A
    interpretAddition : ∀ m n →
      interpretDyadic (m + n) ≡
      _+_ A (interpretDyadic m) (interpretDyadic n)

    interpretedMarginNonnegative :
      _≤_ A (zero A)
        (interpretDyadic Canonical.canonicalStrictMargin)

    InterpretedMarginPositive : Set
    interpretedMarginPositive : InterpretedMarginPositive

    nearBudgetFitsCanonicalQuarter : ∀ q τ u →
      WallI.CommonAdmissible wallI q τ u →
      _≤_ A
        (Near.officialNearBudget (WallI.nearInputs wallI) q τ u)
        (interpretDyadic Canonical.canonicalNearPayment)

    farLowBudgetFitsCanonicalEighth : ∀ q τ u →
      WallI.CommonAdmissible wallI q τ u →
      _≤_ A
        (Low.radiusEightOfficialBudget (WallI.farLowInputs wallI) q τ u)
        (interpretDyadic Canonical.canonicalFarLowPayment)

    farHighBudgetFitsCanonicalEighth : ∀ q τ u →
      WallI.CommonAdmissible wallI q τ u →
      _≤_ A
        (High.radiusEightOfficialBudget (WallI.farHighInputs wallI) q τ u)
        (interpretDyadic Canonical.canonicalFarHighPayment)

open CanonicalWallIMarginInputs public

canonicalWallIMarginInterpretationAt :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  (C : CanonicalWallIMarginInputs A Index Time State) →
  ∀ q τ u →
  WallI.CommonAdmissible (wallI C) q τ u →
  Interpretation.CanonicalDyadicMarginInterpretation A
canonicalWallIMarginInterpretationAt {A = A} C q τ u admissible = record
  { interpretDyadic = interpretDyadic C
  ; interpretAddition = interpretAddition C
  ; nearTerm = Near.nearTotal (WallI.nearInputs (wallI C)) q τ u
  ; farLowTerm = Low.farLowOperator (WallI.farLowInputs (wallI C)) q τ u
  ; farHighTerm = High.farHighTotal (WallI.farHighInputs (wallI C)) q τ u
  ; nearFitsCanonicalQuarter =
      ≤-trans A
        (Near.periodicNearTriadCutoffUniformEstimate
          (WallI.nearInputs (wallI C)) q τ u
          (WallI.commonImpliesNear (wallI C) q τ u admissible))
        (nearBudgetFitsCanonicalQuarter C q τ u admissible)
  ; farLowFitsCanonicalEighth =
      ≤-trans A
        (Low.periodicFarLowOfficialRadiusEightEstimate
          (WallI.farLowInputs (wallI C)) q τ u
          (WallI.commonImpliesFarLow (wallI C) q τ u admissible))
        (farLowBudgetFitsCanonicalEighth C q τ u admissible)
  ; farHighFitsCanonicalEighth =
      ≤-trans A
        (High.periodicFarHighOfficialRadiusEightEstimate
          (WallI.farHighInputs (wallI C)) q τ u
          (WallI.commonImpliesFarHigh (wallI C) q τ u admissible))
        (farHighBudgetFitsCanonicalEighth C q τ u admissible)
  ; interpretedMarginNonnegative = interpretedMarginNonnegative C
  ; InterpretedMarginPositive = InterpretedMarginPositive C
  ; interpretedMarginPositive = interpretedMarginPositive C
  }

canonicalWallIStrictMarginAt :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  (C : CanonicalWallIMarginInputs A Index Time State) →
  ∀ q τ u →
  (admissible : WallI.CommonAdmissible (wallI C) q τ u) →
  Margin.PeriodicStrictDissipationMarginInputs A
canonicalWallIStrictMarginAt C q τ u admissible =
  Interpretation.canonicalInterpretationToStrictMarginInputs
    (canonicalWallIMarginInterpretationAt C q τ u admissible)

canonicalWallIComponentSumBelowViscosity :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  (C : CanonicalWallIMarginInputs A Index Time State) →
  ∀ q τ u →
  (admissible : WallI.CommonAdmissible (wallI C) q τ u) →
  _≤_ A
    (_+_ A
      (_+_ A
        (Near.nearTotal (WallI.nearInputs (wallI C)) q τ u)
        (Low.farLowOperator (WallI.farLowInputs (wallI C)) q τ u))
      (High.farHighTotal (WallI.farHighInputs (wallI C)) q τ u))
    (interpretDyadic C Canonical.canonicalViscosityBudget)
canonicalWallIComponentSumBelowViscosity C q τ u admissible =
  Interpretation.canonicalInterpretedNonlinearBelowViscosity
    (canonicalWallIMarginInterpretationAt C q τ u admissible)

canonicalWallINonlinearBelowViscosity :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  (C : CanonicalWallIMarginInputs A Index Time State) →
  ∀ q τ u →
  (admissible : WallI.CommonAdmissible (wallI C) q τ u) →
  _≤_ A
    (WallI.nonlinearTotal (wallI C) q τ u)
    (interpretDyadic C Canonical.canonicalViscosityBudget)
canonicalWallINonlinearBelowViscosity {A = A} C q τ u admissible =
  subst
    (λ lhs →
      _≤_ A lhs
        (interpretDyadic C Canonical.canonicalViscosityBudget))
    (sym (WallI.exactNonlinearDecomposition (wallI C) q τ u))
    (canonicalWallIComponentSumBelowViscosity C q τ u admissible)

canonicalWallIPositiveHalfMargin :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  (C : CanonicalWallIMarginInputs A Index Time State) →
  InterpretedMarginPositive C
canonicalWallIPositiveHalfMargin = interpretedMarginPositive

------------------------------------------------------------------------
-- Status: the exact positive half-margin now follows from the three official
-- component estimates plus their canonical share comparisons.  No additional
-- scalar feasibility problem remains after those cutoff-uniform comparisons.
------------------------------------------------------------------------

canonicalWallIMarginAdapterLevel : ProofLevel
canonicalWallIMarginAdapterLevel = machineChecked
