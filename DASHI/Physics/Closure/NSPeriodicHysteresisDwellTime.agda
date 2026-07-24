module DASHI.Physics.Closure.NSPeriodicHysteresisDwellTime where

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicHysteresisSeparation as Separation
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Positive dwell-time reduction from hysteresis and a score modulus.
--
-- At the first switch, its winner beats the future winner by the hysteresis
-- gap.  At the next switch, the future winner beats the old winner by the same
-- gap.  The separation theorem then forces two gaps below two score moduli.
-- If the interval is shorter than the candidate dwell time, the PDE score
-- modulus contradicts that inequality.  Thus no consecutive switches can be
-- closer than the dwell threshold.
------------------------------------------------------------------------

record HysteresisDwellTimeInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Time State : Set i) : Set (lsuc i) where
  field
    ConsecutiveSwitches : Time → Time → State → Set i
    ShorterThanDwell : Time → Time → Set i

    separationData : ∀ first second u →
      ConsecutiveSwitches first second u →
      Separation.PeriodicHysteresisSeparationInputs A

    shortIntervalModulusContradiction : ∀ first second u
      (switches : ConsecutiveSwitches first second u) →
      ShorterThanDwell first second →
      let H = separationData first second u switches in
      (_≤_ A
        (_+_ A
          (Separation.hysteresisGap H)
          (Separation.hysteresisGap H))
        (_+_ A
          (Separation.scoreModulus H)
          (Separation.scoreModulus H)) → ⊥)

open HysteresisDwellTimeInputs public

consecutiveSwitchesCannotBeShorterThanDwell :
  ∀ {i} {A : AbsorptionArithmetic} {Time State : Set i} →
  (D : HysteresisDwellTimeInputs A Time State) →
  ∀ first second u →
  ConsecutiveSwitches D first second u →
  ShorterThanDwell D first second →
  ⊥
consecutiveSwitchesCannotBeShorterThanDwell D first second u switches short =
  Separation.hysteresisGapExcludesImmediateBackSwitch H
    (shortIntervalModulusContradiction D first second u switches short)
  where
  H = separationData D first second u switches

record PositiveDwellTime
    {i : Level}
    {Time State : Set i}
    (ConsecutiveSwitches : Time → Time → State → Set i)
    (ShorterThanDwell : Time → Time → Set i) : Set (lsuc i) where
  field
    separated : ∀ first second u →
      ConsecutiveSwitches first second u →
      ShorterThanDwell first second →
      ⊥

open PositiveDwellTime public

hysteresisAndModulusGivePositiveDwell :
  ∀ {i} {A : AbsorptionArithmetic} {Time State : Set i} →
  (D : HysteresisDwellTimeInputs A Time State) →
  PositiveDwellTime
    (ConsecutiveSwitches D)
    (ShorterThanDwell D)
hysteresisAndModulusGivePositiveDwell D = record
  { separated = consecutiveSwitchesCannotBeShorterThanDwell D }

record PositiveDwellLocalFinitenessInputs
    {i : Level}
    (Time State : Set i) : Set (lsuc i) where
  field
    ConsecutiveSwitches : Time → Time → State → Set i
    ShorterThanDwell : Time → Time → Set i
    LocallyFiniteSwitching : Set i

    positiveDwellImpliesLocallyFinite :
      PositiveDwellTime ConsecutiveSwitches ShorterThanDwell →
      LocallyFiniteSwitching

open PositiveDwellLocalFinitenessInputs public

hysteresisDwellGivesLocalFiniteness :
  ∀ {i} {A : AbsorptionArithmetic} {Time State : Set i} →
  (D : HysteresisDwellTimeInputs A Time State) →
  (L : PositiveDwellLocalFinitenessInputs Time State) →
  ConsecutiveSwitches L ≡ ConsecutiveSwitches D →
  ShorterThanDwell L ≡ ShorterThanDwell D →
  LocallyFiniteSwitching L
hysteresisDwellGivesLocalFiniteness D L switchesMatch shortMatch =
  positiveDwellImpliesLocallyFinite L transported
  where
  transported :
    PositiveDwellTime (ConsecutiveSwitches L) (ShorterThanDwell L)
  transported rewrite switchesMatch | shortMatch =
    hysteresisAndModulusGivePositiveDwell D

------------------------------------------------------------------------
-- Status: the no-chattering route is reduced to a uniform score-modulus bound
-- and the standard positive-dwell-to-local-finiteness theorem for compact time
-- intervals.  No separate combinatorial switch-count assumption is needed.
------------------------------------------------------------------------

hysteresisDwellTimeLevel : ProofLevel
hysteresisDwellTimeLevel = machineChecked
