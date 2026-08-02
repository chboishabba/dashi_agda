module DASHI.Physics.Closure.NSTriadKNOutputRelocationConditionalCutoffUniformClosure where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Jean-Michel Bony; Hajer
-- Bahouri; Jean-Yves Chemin; Raphael Danchin; Augustin-Louis Cauchy; DASHI
-- repository contributors.
-- Title: "A Multilinear Schur Test and Multiplier Operators"; "Calcul
-- symbolique et propagation des singularites pour les equations aux derivees
-- partielles non lineaires"; "Fourier Analysis and Nonlinear Partial
-- Differential Equations"; and "Conditional cutoff-uniform closure of the
-- output-relocation archetype".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; Annales
-- scientifiques de l'Ecole Normale Superieure 14 (1981); Springer, 2011;
-- DASHI formal development, 2026.
-- DOI: 10.1006/jfan.2001.3804; 10.24033/asens.1404;
-- 10.1007/978-3-642-16830-7; the repository closure theorem has no DOI.
-- Uses: the unit-weight Schur reduction, the exact positive factorised kernel,
-- rational geometric summation, and finite two-sided signed domination.
-- Relationship: proves the entire cutoff-independent shell and signed-form
-- conclusion from one concrete bridge record.  The bridge contains exactly
-- the remaining repository-specific facts: the two H^s shell-factor
-- comparisons and the literal coefficient's pointwise two-sided domination.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; -_; _≤_)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant
import DASHI.Physics.Closure.NSTriadKNOutputRelocationUnitWeightShellSchur as ShellSchur
import DASHI.Physics.Closure.NSTriadKNRationalFiniteSignedMajorant as Signed

record ConcreteOutputRelocationShellBridge : Set where
  constructor shell-bridge
  field
    lowFactor gapFactor : Nat → ℚ
    signedCoefficient : Nat → Nat → ℚ

    lowFactorNonnegative : ∀ lowShell → 0ℚ ≤ lowFactor lowShell
    gapFactorNonnegative : ∀ gap → 0ℚ ≤ gapFactor gap

    lowShellDominatedByQuarter : ∀ lowShell →
      lowFactor lowShell ≤ Geo.pow Geo.quarter lowShell
    gapDominatedByThirtySecond : ∀ gap →
      gapFactor gap ≤ Geo.pow Geo.thirtySecond gap

    signedCoefficientUpper : ∀ lowShell gap →
      signedCoefficient lowShell gap
      ≤ lowFactor lowShell * gapFactor gap
    signedCoefficientLower : ∀ lowShell gap →
      - (lowFactor lowShell * gapFactor gap)
      ≤ signedCoefficient lowShell gap

open ConcreteOutputRelocationShellBridge public

bridgeMajorant :
  ConcreteOutputRelocationShellBridge → Nat → Nat → ℚ
bridgeMajorant bridge lowShell gap =
  lowFactor bridge lowShell * gapFactor bridge gap

bridgeMajorantNonnegative : ∀ bridge lowShell gap →
  0ℚ ≤ bridgeMajorant bridge lowShell gap
bridgeMajorantNonnegative bridge lowShell gap =
  let
    instance
      lowIsNonnegative =
        ℚₚ.nonNegative (lowFactorNonnegative bridge lowShell)
      gapIsNonnegative =
        ℚₚ.nonNegative (gapFactorNonnegative bridge gap)
  in
  ℚₚ.nonNegative⁻¹
    (lowFactor bridge lowShell * gapFactor bridge gap)

bridgeFactorizedKernel :
  ConcreteOutputRelocationShellBridge → Majorant.PositiveFactorizedKernel
bridgeFactorizedKernel bridge = Majorant.factorized-kernel
  (bridgeMajorant bridge)
  (lowFactor bridge)
  (gapFactor bridge)
  (bridgeMajorantNonnegative bridge)
  (lowFactorNonnegative bridge)
  (gapFactorNonnegative bridge)
  (λ lowShell gap → ℚₚ.≤-refl)
  (lowShellDominatedByQuarter bridge)
  (gapDominatedByThirtySecond bridge)

bridgeMajorantCutoffBound : ∀ bridge lowCutoff gapCutoff →
  Majorant.rectangleSum
    (bridgeMajorant bridge) lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds
bridgeMajorantCutoffBound bridge =
  Majorant.kernelRectangleBound (bridgeFactorizedKernel bridge)

bridgeSignedFamily :
  ConcreteOutputRelocationShellBridge → Signed.SignedKernelMajorized
bridgeSignedFamily bridge = Signed.signed-majorized
  (signedCoefficient bridge)
  (bridgeMajorant bridge)
  (signedCoefficientUpper bridge)
  (signedCoefficientLower bridge)

bridgeUniformSignedBound :
  ConcreteOutputRelocationShellBridge → Signed.UniformSignedKernelBound
bridgeUniformSignedBound bridge = Signed.uniform-bound
  (bridgeSignedFamily bridge)
  Geo.oneTwentyEightNinetyThirds
  (bridgeMajorantCutoffBound bridge)

outputRelocationConditionalUpperBound : ∀ bridge lowCutoff gapCutoff →
  Majorant.rectangleSum
    (signedCoefficient bridge) lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds
outputRelocationConditionalUpperBound bridge =
  Signed.uniformSignedUpper (bridgeUniformSignedBound bridge)

outputRelocationConditionalLowerBound : ∀ bridge lowCutoff gapCutoff →
  - Geo.oneTwentyEightNinetyThirds
  ≤ Majorant.rectangleSum
      (signedCoefficient bridge) lowCutoff gapCutoff
outputRelocationConditionalLowerBound bridge =
  Signed.uniformSignedLower (bridgeUniformSignedBound bridge)

record ConditionalOutputRelocationArchetypeTheorem
    (bridge : ConcreteOutputRelocationShellBridge) : Set where
  constructor archetype-theorem
  field
    outputShellCondition : ∀ lowCutoff gapCutoff →
      Majorant.rectangleSum
        (bridgeMajorant bridge) lowCutoff gapCutoff
      ≤ Geo.oneTwentyEightNinetyThirds
    firstAdjointShellCondition : ∀ lowCutoff gapCutoff →
      Majorant.rectangleSum
        (bridgeMajorant bridge) lowCutoff gapCutoff
      ≤ Geo.oneTwentyEightNinetyThirds
    secondAdjointShellCondition : ∀ lowCutoff gapCutoff →
      Majorant.rectangleSum
        (bridgeMajorant bridge) lowCutoff gapCutoff
      ≤ Geo.oneTwentyEightNinetyThirds
    signedUpper : ∀ lowCutoff gapCutoff →
      Majorant.rectangleSum
        (signedCoefficient bridge) lowCutoff gapCutoff
      ≤ Geo.oneTwentyEightNinetyThirds
    signedLower : ∀ lowCutoff gapCutoff →
      - Geo.oneTwentyEightNinetyThirds
      ≤ Majorant.rectangleSum
          (signedCoefficient bridge) lowCutoff gapCutoff

open ConditionalOutputRelocationArchetypeTheorem public

conditionalOutputRelocationArchetypeTheorem : ∀ bridge →
  ConditionalOutputRelocationArchetypeTheorem bridge
conditionalOutputRelocationArchetypeTheorem bridge = archetype-theorem
  (bridgeMajorantCutoffBound bridge)
  (bridgeMajorantCutoffBound bridge)
  (bridgeMajorantCutoffBound bridge)
  (outputRelocationConditionalUpperBound bridge)
  (outputRelocationConditionalLowerBound bridge)

record ConditionalClosureReceipt : Set where
  constructor receipt
  field
    threeUnitWeightShellConditionsClosed :
      ShellSchur.outputRelocationThreeUnitWeightShellSchurConditionsClosed
      ≡ true
    positiveKernelSummable :
      Majorant.outputRelocationPositiveKernelCutoffUniformlySummable
      ≡ true
    finiteSignedDominationClosed :
      Signed.finiteTwoSidedTriangleDominationClosed ≡ true

open ConditionalClosureReceipt public

conditionalClosureReceipt : ConditionalClosureReceipt
conditionalClosureReceipt = receipt
  ShellSchur.outputRelocationThreeUnitWeightShellSchurConditionsClosedIsTrue
  Majorant.outputRelocationPositiveKernelCutoffUniformlySummableIsTrue
  Signed.finiteTwoSidedTriangleDominationClosedIsTrue

outputRelocationConditionalArchetypeTheoremClosed : Bool
outputRelocationConditionalArchetypeTheoremClosed = true

outputRelocationAllDownstreamOfShellBridgeClosed : Bool
outputRelocationAllDownstreamOfShellBridgeClosed = true

outputRelocationConcreteShellBridgeInhabited : Bool
outputRelocationConcreteShellBridgeInhabited = false

outputRelocationConcreteCutoffUniformArchetypeClosed : Bool
outputRelocationConcreteCutoffUniformArchetypeClosed = false

outputRelocationConditionalArchetypeTheoremClosedIsTrue :
  outputRelocationConditionalArchetypeTheoremClosed ≡ true
outputRelocationConditionalArchetypeTheoremClosedIsTrue = refl

outputRelocationAllDownstreamOfShellBridgeClosedIsTrue :
  outputRelocationAllDownstreamOfShellBridgeClosed ≡ true
outputRelocationAllDownstreamOfShellBridgeClosedIsTrue = refl

outputRelocationConcreteShellBridgeInhabitedIsFalse :
  outputRelocationConcreteShellBridgeInhabited ≡ false
outputRelocationConcreteShellBridgeInhabitedIsFalse = refl

outputRelocationConcreteCutoffUniformArchetypeClosedIsFalse :
  outputRelocationConcreteCutoffUniformArchetypeClosed ≡ false
outputRelocationConcreteCutoffUniformArchetypeClosedIsFalse = refl
