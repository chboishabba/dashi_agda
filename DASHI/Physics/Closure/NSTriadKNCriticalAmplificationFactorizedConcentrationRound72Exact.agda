module DASHI.Physics.Closure.NSTriadKNCriticalAmplificationFactorizedConcentrationRound72Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite Cauchy--Schwarz inequality; DOI not applicable.
--
-- ROUND72 / AMPLIFICATION -> EFFECTIVE-COMPLEXITY CONCENTRATION
--
-- Compose three already-exact pieces:
--
--  (1) Round69: critical excess mu forces mu <= remainder_n, with no ambient
--      Xi<=K assumption;
--  (2) a SAME-OBJECT identity remainder_n = triadicSignedSum(atoms);
--  (3) Round72's factorization overlay on those exact atoms.
--
-- The resulting theorem is
--
--      mu^2 <= overlayCharge * overlayEffectiveComplexity.
--
-- This strictly generalises Round71's
--
--      mu^2 <= (#atoms) * triadicConcentrationMass.
--
-- The open PDE theorem is now sharper: construct the actual localized
-- trajectory atoms, identify the critical remainder with their triadic signed
-- grouping, and produce a PHYSICAL factorization overlay whose charge is
-- budgeted and whose effective complexity is sufficiently controlled.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

import DASHI.Physics.Closure.NSTriadKNCriticalAmplificationForcesRemainderRound69Exact as Amplification
import DASHI.Physics.Closure.NSTriadKNCriticalRatioNormalizationRound63Exact as C1
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured
import DASHI.Physics.Closure.NSTriadKNCriticalRemainderTriadicCauchyRound71Exact as R71
import DASHI.Physics.Closure.NSTriadKNStructuredTriadicFactorizationOverlayRound72Exact as Overlay

criticalAmplificationForcesFactorizedConcentration :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    (step : Amplification.CriticalRatioStepDecomposition positiveBlock)
    (n : Nat) (mu : ℚ)
    (atoms : List Structured.LocalizedPDEAtom)
    (overlay : Overlay.TriadicFactorizationOverlay atoms) →
  0ℚ ≤ mu →
  Amplification.inherited step n + mu
    ≤ C1.normalizedCriticalRatio positiveBlock (Agda.Builtin.Nat.suc n) →
  Amplification.remainder step n ≡ R71.triadicSignedSum atoms →
  L2.square mu
    ≤ Overlay.overlayCharge overlay * Overlay.overlayEffectiveComplexity overlay
criticalAmplificationForcesFactorizedConcentration
    step n mu atoms overlay muNN excess remainderExact =
  let
    muBelowRemainder : mu ≤ Amplification.remainder step n
    muBelowRemainder =
      Amplification.criticalAmplificationForcesRemainder step n mu excess

    muBelowSum : mu ≤ R71.triadicSignedSum atoms
    muBelowSum = subst (mu ≤_) remainderExact muBelowRemainder

    sumNN : 0ℚ ≤ R71.triadicSignedSum atoms
    sumNN = ℚP.≤-trans muNN muBelowSum

    squareBelow :
      L2.square mu ≤ L2.square (R71.triadicSignedSum atoms)
    squareBelow =
      L2.nonnegativeProductMonotone
        muNN muNN sumNN sumNN muBelowSum muBelowSum
  in
  ℚP.≤-trans squareBelow (Overlay.overlayCauchy overlay)

round72AmplificationToFactorizedConcentrationConstructed : Bool
round72AmplificationToFactorizedConcentrationConstructed = true

round72AmplificationTheoremUsesAmbientXiBound : Bool
round72AmplificationTheoremUsesAmbientXiBound = false

round72PhysicalRemainderAndEnergyOverlayConstructed : Bool
round72PhysicalRemainderAndEnergyOverlayConstructed = false

round72AmplificationToFactorizedConcentrationConstructedIsTrue :
  round72AmplificationToFactorizedConcentrationConstructed ≡ true
round72AmplificationToFactorizedConcentrationConstructedIsTrue = refl

round72AmplificationTheoremUsesAmbientXiBoundIsFalse :
  round72AmplificationTheoremUsesAmbientXiBound ≡ false
round72AmplificationTheoremUsesAmbientXiBoundIsFalse = refl
