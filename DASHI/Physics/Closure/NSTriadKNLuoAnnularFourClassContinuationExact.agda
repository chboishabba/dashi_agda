module DASHI.Physics.Closure.NSTriadKNLuoAnnularFourClassContinuationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin;
-- Raphael Danchin.
-- Bony DOI: 10.24033/asens.1404.
-- Bahouri--Chemin--Danchin DOI: 10.1007/978-3-642-16830-7.
--
-- Author: James Serrin.
-- Title: "On the Interior Regularity of Weak Solutions of the Navier--Stokes
-- Equations".
-- DOI: 10.1007/BF00253344.
--
-- Author: Terence Tao.
-- Title: "254A, Notes 1: Local Well-Posedness of the Navier-Stokes
-- Equations".
-- DOI: not assigned.
--
-- PURPOSE
-- Assemble the actual growing-annulus high-high theorem with the checked
-- centered low-high and repaired high-low terminal theorems.  Only the
-- comparable-shell class remains supplied as an explicit analytic input.
--
-- Every class is normalized against one shared critical and output envelope.
-- With coefficient one for each class, the existing radical-free four-class
-- theorem gives
--
--   |N_q|^2 <= 16 A_q^2 E_q^2.
--
-- The existing 1/64 continuation theorem is then obtained from
--
--   16 A_q^2 <= 1/4096.
--
-- No critical smallness or comparable-shell estimate is asserted automatic.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoLowHighSixThreeTerminalExact as LH
import DASHI.Physics.Closure.NSTriadKNLuoHighLowDerivativePlacementTerminalExact as HL
import DASHI.Physics.Closure.NSTriadKNLuoGrowingDyadicAnnulusHighHighTerminalExact as HH
import DASHI.Physics.Closure.NSTriadKNLuoRound14SquaredFourClassClosureExact as Four
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicGalerkinFourClassContinuationExact as Continue

record AnnularFourClassData (shell : Nat) : Set₁ where
  constructor annular-four-class-data
  field
    lowHighData : LH.LowHighSixThreeTerminalData
    highLowData : HL.HighLowDerivativePlacementTerminalData
    highHighData : HH.AnnularHighHighTerminalData shell

    comparableInteraction : ℚ
    criticalEnvelopeSquared outputEnvelopeSquared : ℚ
    outputEnvelopeNonnegative : 0ℚ ≤ outputEnvelopeSquared

    lowHighCriticalMeaning :
      LH.criticalEnvelopeSquared lowHighData ≡ criticalEnvelopeSquared
    lowHighOutputMeaning :
      LH.outputEnvelopeSquared lowHighData ≡ outputEnvelopeSquared

    highLowCriticalMeaning :
      HL.criticalEnvelopeSquared highLowData ≡ criticalEnvelopeSquared
    highLowOutputMeaning :
      HL.outputEnvelopeSquared highLowData ≡ outputEnvelopeSquared

    highHighCriticalMeaning :
      HH.criticalEnvelopeSquared highHighData ≡ criticalEnvelopeSquared
    highHighOutputMeaning :
      HH.outputEnvelopeSquared highHighData ≡ outputEnvelopeSquared

    comparableSquareBound :
      L2.square comparableInteraction
      ≤ criticalEnvelopeSquared * outputEnvelopeSquared

open AnnularFourClassData public

lowHighInteraction :
  ∀ {shell : Nat} → AnnularFourClassData shell → ℚ
lowHighInteraction dataSet =
  L2.pairDot (LH.terminalPairs (lowHighData dataSet))

highLowInteraction :
  ∀ {shell : Nat} → AnnularFourClassData shell → ℚ
highLowInteraction dataSet =
  L2.pairDot (HL.terminalPairs (highLowData dataSet))

highHighInteraction :
  ∀ {shell : Nat} → AnnularFourClassData shell → ℚ
highHighInteraction dataSet =
  HH.highHighInteraction (highHighData dataSet)

lowHighLocalSquareBound :
  ∀ {shell : Nat}
    (dataSet : AnnularFourClassData shell) →
  L2.square (lowHighInteraction dataSet)
  ≤ LH.criticalEnvelopeSquared (lowHighData dataSet)
    * LH.outputEnvelopeSquared (lowHighData dataSet)
lowHighLocalSquareBound dataSet =
  subst
    (λ lower →
      lower
      ≤ LH.criticalEnvelopeSquared (lowHighData dataSet)
        * LH.outputEnvelopeSquared (lowHighData dataSet))
    (LH.interactionMeaning (lowHighData dataSet))
    (LH.lowHighSixThreeTerminalSquareBound (lowHighData dataSet))

highLowLocalSquareBound :
  ∀ {shell : Nat}
    (dataSet : AnnularFourClassData shell) →
  L2.square (highLowInteraction dataSet)
  ≤ HL.criticalEnvelopeSquared (highLowData dataSet)
    * HL.outputEnvelopeSquared (highLowData dataSet)
highLowLocalSquareBound dataSet =
  subst
    (λ lower →
      lower
      ≤ HL.criticalEnvelopeSquared (highLowData dataSet)
        * HL.outputEnvelopeSquared (highLowData dataSet))
    (HL.interactionMeaning (highLowData dataSet))
    (HL.highLowDerivativePlacementTerminalSquareBound
      (highLowData dataSet))

lowHighSharedSquareBound :
  ∀ {shell : Nat}
    (dataSet : AnnularFourClassData shell) →
  L2.square (lowHighInteraction dataSet)
  ≤ criticalEnvelopeSquared dataSet * outputEnvelopeSquared dataSet
lowHighSharedSquareBound dataSet
  rewrite lowHighCriticalMeaning dataSet
        | lowHighOutputMeaning dataSet =
  lowHighLocalSquareBound dataSet

highLowSharedSquareBound :
  ∀ {shell : Nat}
    (dataSet : AnnularFourClassData shell) →
  L2.square (highLowInteraction dataSet)
  ≤ criticalEnvelopeSquared dataSet * outputEnvelopeSquared dataSet
highLowSharedSquareBound dataSet
  rewrite highLowCriticalMeaning dataSet
        | highLowOutputMeaning dataSet =
  highLowLocalSquareBound dataSet

highHighSharedSquareBound :
  ∀ {shell : Nat}
    (dataSet : AnnularFourClassData shell) →
  L2.square (highHighInteraction dataSet)
  ≤ criticalEnvelopeSquared dataSet * outputEnvelopeSquared dataSet
highHighSharedSquareBound dataSet
  rewrite highHighCriticalMeaning dataSet
        | highHighOutputMeaning dataSet =
  HH.annularHighHighTerminalSquareBound (highHighData dataSet)

unitCoefficient : ℚ
unitCoefficient = 1ℚ

attachUnitCoefficient :
  (interaction critical output : ℚ) →
  L2.square interaction ≤ critical * output →
  L2.square interaction
  ≤ unitCoefficient * critical * output
attachUnitCoefficient interaction critical output bound =
  let
    unitMeaning : unitCoefficient * critical * output ≡ critical * output
    unitMeaning = solve (critical ∷ output ∷ [])
  in
  subst
    (λ upper → L2.square interaction ≤ upper)
    (sym unitMeaning)
    bound

asFourClassBudget :
  ∀ {shell : Nat} →
  AnnularFourClassData shell → Four.SquaredFourClassBudget
asFourClassBudget dataSet =
  Four.squared-four-class-budget
    (lowHighInteraction dataSet)
    (highLowInteraction dataSet)
    (comparableInteraction dataSet)
    (highHighInteraction dataSet)
    unitCoefficient
    unitCoefficient
    unitCoefficient
    unitCoefficient
    (criticalEnvelopeSquared dataSet)
    (outputEnvelopeSquared dataSet)
    (attachUnitCoefficient
      (lowHighInteraction dataSet)
      (criticalEnvelopeSquared dataSet)
      (outputEnvelopeSquared dataSet)
      (lowHighSharedSquareBound dataSet))
    (attachUnitCoefficient
      (highLowInteraction dataSet)
      (criticalEnvelopeSquared dataSet)
      (outputEnvelopeSquared dataSet)
      (highLowSharedSquareBound dataSet))
    (attachUnitCoefficient
      (comparableInteraction dataSet)
      (criticalEnvelopeSquared dataSet)
      (outputEnvelopeSquared dataSet)
      (comparableSquareBound dataSet))
    (attachUnitCoefficient
      (highHighInteraction dataSet)
      (criticalEnvelopeSquared dataSet)
      (outputEnvelopeSquared dataSet)
      (highHighSharedSquareBound dataSet))

coefficientSumIsFour :
  ∀ {shell : Nat}
    (dataSet : AnnularFourClassData shell) →
  Four.coefficientSum (asFourClassBudget dataSet) ≡ Four.four
coefficientSumIsFour dataSet = solve []

annularFourClassSquareBound :
  ∀ {shell : Nat}
    (dataSet : AnnularFourClassData shell) →
  L2.square (Four.totalInteraction (asFourClassBudget dataSet))
  ≤ Four.four *
      (Four.four
        * criticalEnvelopeSquared dataSet
        * outputEnvelopeSquared dataSet)
annularFourClassSquareBound dataSet =
  let
    assembled = Four.squaredFourClassTerminalAssembly
      (asFourClassBudget dataSet)
  in
  subst
    (λ coefficientSum →
      L2.square (Four.totalInteraction (asFourClassBudget dataSet))
      ≤ Four.four
        * (coefficientSum
          * criticalEnvelopeSquared dataSet
          * outputEnvelopeSquared dataSet))
    (coefficientSumIsFour dataSet)
    assembled

record AnnularContinuationData (shell : Nat) : Set₁ where
  constructor annular-continuation-data
  field
    fourClassData : AnnularFourClassData shell
    criticalSmallness :
      Four.four
        * (Four.four
          * criticalEnvelopeSquared fourClassData)
      ≤ Continue.oneOver4096

open AnnularContinuationData public

asContinuationBudget :
  ∀ {shell : Nat} →
  AnnularContinuationData shell →
  Continue.PeriodicGalerkinContinuationBudget
asContinuationBudget dataSet =
  Continue.periodic-galerkin-continuation-budget
    (asFourClassBudget (fourClassData dataSet))
    (outputEnvelopeNonnegative (fourClassData dataSet))
    (subst
      (λ coefficientSum →
        Four.four
          * (coefficientSum
            * criticalEnvelopeSquared (fourClassData dataSet))
        ≤ Continue.oneOver4096)
      (sym (coefficientSumIsFour (fourClassData dataSet)))
      (criticalSmallness dataSet))

annularTerminalSmallnessSquared :
  ∀ {shell : Nat}
    (dataSet : AnnularContinuationData shell) →
  L2.square
    (Four.totalInteraction
      (asFourClassBudget (fourClassData dataSet)))
  ≤ Continue.oneOver4096
    * outputEnvelopeSquared (fourClassData dataSet)
annularTerminalSmallnessSquared dataSet =
  Continue.periodicGalerkinTerminalSmallnessSquared
    (asContinuationBudget dataSet)
