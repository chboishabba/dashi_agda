module DASHI.Physics.Closure.NSCompactGammaHighestAlphaExpenditureCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption

------------------------------------------------------------------------
-- Highest-alpha compact-Gamma completion lane.
--
-- The earlier Bernstein/BKM owner deliberately leaves B4 and B5 as abstract
-- analytic witness types.  This module exposes the strongest algebraic form of
-- those two leaves: an integrated potential balance, a split of the total escape
-- into the coercive envelope expenditure and the absorbable dissipation part,
-- and a replenishment estimate.  The finite envelope, weighted-shell and
-- vorticity expenditures are then theorems, not independent inputs.
--
-- Analytic work still has to establish the four displayed hypotheses for the
-- selected Navier--Stokes/compact-Gamma carrier.  No BKM theorem, vorticity
-- integral, or high-Sobolev persistence statement appears among them.
------------------------------------------------------------------------

record HighestAlphaExpenditureData
    {l : Level}
    (A : AbsorptionArithmetic) : Set (lsuc l) where
  field
    --------------------------------------------------------------------
    -- Integrated B4 data.

    potentialInitial : Scalar A
    potentialFinal : Scalar A

    -- This is c_Gamma * integral E_Gamma.  Keeping the coercivity factor
    -- inside the quantity avoids subtraction and division in the generic
    -- ordered-additive carrier.
    coerciveEnvelopeExpenditure : Scalar A

    -- The part paid for by the energy/dissipation inequality.
    absorbedDissipationExpenditure : Scalar A

    totalEscape : Scalar A
    replenishment : Scalar A
    forcingAndTimeRemainder : Scalar A

    potentialFinalNonnegative :
      _≤_ A (zero A) potentialFinal

    -- Integrated differential balance:
    --   Phi(0) + replenishment = Phi(T) + totalEscape.
    integratedPotentialBalance :
      _+_ A potentialInitial replenishment ≡
      _+_ A potentialFinal totalEscape

    -- The total escape separates the wanted envelope expenditure from the
    -- absorbable dissipation contribution.
    totalEscapeSplits :
      totalEscape ≡
      _+_ A coerciveEnvelopeExpenditure
        absorbedDissipationExpenditure

    -- Energy/dissipation control absorbs the second part, leaving only fixed
    -- forcing and finite-time remainder.
    replenishmentAbsorbedByDissipation :
      _≤_ A replenishment
        (_+_ A absorbedDissipationExpenditure
          forcingAndTimeRemainder)

    --------------------------------------------------------------------
    -- B6/B7 transport data.  These are monotone reconstruction statements,
    -- not finiteness assumptions.

    weightedShellExpenditure : Scalar A
    vorticityExpenditure : Scalar A

    weightedShellBelowEnvelope :
      _≤_ A weightedShellExpenditure coerciveEnvelopeExpenditure

    vorticityBelowWeightedShell :
      _≤_ A vorticityExpenditure weightedShellExpenditure

    --------------------------------------------------------------------
    -- B8 is consumed only after B4--B7 have produced the bound.

    Continuation : Set l
    invokeBKMFromBound :
      _≤_ A vorticityExpenditure
        (_+_ A potentialInitial forcingAndTimeRemainder) →
      Continuation

open HighestAlphaExpenditureData public

asAbsorptionInputs :
  ∀ {l} {A : AbsorptionArithmetic} →
  HighestAlphaExpenditureData {l} A →
  CompactGammaAbsorptionInputs A
asAbsorptionInputs D = record
  { initialPotential = potentialInitial D
  ; finalPotential = potentialFinal D
  ; escapeSupply = totalEscape D
  ; replenishment = replenishment D
  ; thetaEscape = absorbedDissipationExpenditure D
  ; marginEscape = coerciveEnvelopeExpenditure D
  ; remainderConstant = forcingAndTimeRemainder D
  ; finalPotentialNonnegative = potentialFinalNonnegative D
  ; potentialBalance = integratedPotentialBalance D
  ; replenishmentAbsorbed = replenishmentAbsorbedByDissipation D
  ; escapeSplitsMarginAndAbsorbedPart = totalEscapeSplits D
  }

------------------------------------------------------------------------
-- B5: finite compact-Gamma envelope expenditure, derived from B4 and energy.
------------------------------------------------------------------------

finite-coercive-envelope-expenditure :
  ∀ {l} {A : AbsorptionArithmetic} →
  (D : HighestAlphaExpenditureData {l} A) →
  _≤_ A
    (coerciveEnvelopeExpenditure D)
    (_+_ A (potentialInitial D) (forcingAndTimeRemainder D))
finite-coercive-envelope-expenditure {A = A} D =
  absorbedReplenishmentBoundsEscapeMargin A (asAbsorptionInputs D)

------------------------------------------------------------------------
-- B6: finite Bernstein-weighted shell expenditure.
------------------------------------------------------------------------

finite-weighted-shell-expenditure :
  ∀ {l} {A : AbsorptionArithmetic} →
  (D : HighestAlphaExpenditureData {l} A) →
  _≤_ A
    (weightedShellExpenditure D)
    (_+_ A (potentialInitial D) (forcingAndTimeRemainder D))
finite-weighted-shell-expenditure {A = A} D =
  ≤-trans A
    (weightedShellBelowEnvelope D)
    (finite-coercive-envelope-expenditure D)

------------------------------------------------------------------------
-- B7: finite vorticity time expenditure.
------------------------------------------------------------------------

finite-vorticity-time-expenditure :
  ∀ {l} {A : AbsorptionArithmetic} →
  (D : HighestAlphaExpenditureData {l} A) →
  _≤_ A
    (vorticityExpenditure D)
    (_+_ A (potentialInitial D) (forcingAndTimeRemainder D))
finite-vorticity-time-expenditure {A = A} D =
  ≤-trans A
    (vorticityBelowWeightedShell D)
    (finite-weighted-shell-expenditure D)

------------------------------------------------------------------------
-- B8: BKM occurs only at the endpoint.
------------------------------------------------------------------------

highest-alpha-bkm-continuation :
  ∀ {l} {A : AbsorptionArithmetic} →
  (D : HighestAlphaExpenditureData {l} A) →
  Continuation D
highest-alpha-bkm-continuation D =
  invokeBKMFromBound D (finite-vorticity-time-expenditure D)

------------------------------------------------------------------------
-- Dependency audit: the decisive path is represented by constructors rather
-- than comments or booleans.
------------------------------------------------------------------------

data HighestAlphaStage : Set where
  invariantRegionAndPacketStage : HighestAlphaStage
  integratedDifferentialStage : HighestAlphaStage
  energyAbsorptionStage : HighestAlphaStage
  envelopeExpenditureStage : HighestAlphaStage
  weightedShellExpenditureStage : HighestAlphaStage
  vorticityExpenditureStage : HighestAlphaStage
  bkmEndpointStage : HighestAlphaStage

data DirectDependency : HighestAlphaStage → HighestAlphaStage → Set where
  packet-to-differential :
    DirectDependency invariantRegionAndPacketStage integratedDifferentialStage
  differential-to-absorption :
    DirectDependency integratedDifferentialStage energyAbsorptionStage
  absorption-to-envelope :
    DirectDependency energyAbsorptionStage envelopeExpenditureStage
  envelope-to-shell :
    DirectDependency envelopeExpenditureStage weightedShellExpenditureStage
  shell-to-vorticity :
    DirectDependency weightedShellExpenditureStage vorticityExpenditureStage
  vorticity-to-bkm :
    DirectDependency vorticityExpenditureStage bkmEndpointStage

-- There is intentionally no constructor whose source is bkmEndpointStage.
-- Hence BKM cannot feed any earlier analytic or expenditure stage through this
-- dependency relation.
