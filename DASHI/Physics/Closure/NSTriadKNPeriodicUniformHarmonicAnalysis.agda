module DASHI.Physics.Closure.NSTriadKNPeriodicUniformHarmonicAnalysis where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Venue/year: Grundlehren der mathematischen Wissenschaften 343,
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
-- Uses: Chapter 2, Littlewood--Paley theory, Bernstein inequalities,
-- paraproducts and Fourier multipliers.
-- Relationship: adapts standard estimates to the periodic duplicate-free
-- finite Fourier carrier, with constants quantified outside the cutoff.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator estimates and the Euler and Navier-Stokes equations".
-- Venue/year: Communications on Pure and Applied Mathematics 41 (1988),
-- 891--907.
-- DOI: 10.1002/cpa.3160410704.
-- Uses: multiplier-commutator gain.
-- Relationship: adapts the commutator mechanism to dyadic shell fibres.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)
import Data.Integer.Base as Int
open import Data.Nat.Base using (_≤_)

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = 2 * pow2 n

twice threeTimes fiveTimes : Nat → Nat
twice n = n + n
threeTimes n = n + (n + n)
fiveTimes n = n + (n + (n + (n + n)))

record PeriodicUniformHarmonicAnalysis {c s : Level} :
    Set (lsuc (c ⊔ s)) where
  field
    Cutoff : Set c
    State : Set s
    Mode : Set s
    Vector : Set s

    physicalL2Squared fourierL2Squared :
      Cutoff → State → Nat

    shellL2Squared shellLInfinitySquared
      shellVorticityLInfinitySquared :
      Nat → Cutoff → State → Nat

    shellVorticityL2Squared :
      Nat → Cutoff → State → Nat

    shellLatticeCount : Nat → Cutoff → Nat

    convolutionOutputSquared convolutionInputSquared :
      Cutoff → State → Nat

    schurInputSquared schurOutputSquared :
      Cutoff → State → Nat
    shellRowAbsoluteSum shellColumnAbsoluteSum :
      Nat → Cutoff → State → Nat

    commutatorRemainderSquared
      commutatorInputSquared
      farHighTailSquared
      farHighSobolevSquared :
      Nat → Cutoff → State → Nat

    parsevalConstantSq bernsteinConstantSq biotSavartConstantSq :
      Nat
    shellCountConstant youngConstantSq : Nat
    rowSchurConstant columnSchurConstant schurOperatorConstantSq : Nat
    commutatorConstantSq tailConstantSq : Nat

    periodicParseval : ∀ N state →
      physicalL2Squared N state ≡ fourierL2Squared N state

    periodicPlancherel : ∀ N state →
      physicalL2Squared N state
      ≤ parsevalConstantSq * fourierL2Squared N state

    CutoffMember : Cutoff → Mode → Set
    ShellMember : Nat → Mode → Set
    shellIndex : Mode → Nat
    modeWeight : Mode → Nat

    dyadicShellsPairwiseDisjoint : ∀ j l mode →
      (j ≡ l → ⊥) →
      ShellMember j mode →
      ShellMember l mode →
      ⊥
    dyadicShellsCoverCutoffModes : ∀ N mode →
      CutoffMember N mode →
      ShellMember (shellIndex mode) mode
    shellSupportWeightLower : ∀ j mode →
      ShellMember j mode →
      pow2 j ≤ modeWeight mode
    shellSupportWeightUpper : ∀ j mode →
      ShellMember j mode →
      modeWeight mode ≤ pow2 (suc j)

    duplicateFreeIntegerShellCount : ∀ j N →
      shellLatticeCount j N
      ≤ shellCountConstant * pow2 (threeTimes j)

    lerayProjection : Mode → Vector → Vector
    vectorPairing vectorL2Squared : Vector → Vector → Nat
    curl biotSavart : Mode → Vector → Vector

    lerayProjectionIdempotent : ∀ mode vector →
      lerayProjection mode (lerayProjection mode vector)
      ≡ lerayProjection mode vector
    lerayProjectionSelfAdjoint : ∀ mode u v →
      vectorPairing (lerayProjection mode u) v
      ≡ vectorPairing u (lerayProjection mode v)
    lerayProjectionL2Contraction : ∀ mode vector →
      vectorL2Squared (lerayProjection mode vector)
        (lerayProjection mode vector)
      ≤ vectorL2Squared vector vector
    periodicBiotSavartIdentity : ∀ mode vector →
      biotSavart mode (curl mode vector)
      ≡ lerayProjection mode vector

    shellBiotSavartUniform : ∀ j N state →
      pow2 (twice j) * shellL2Squared j N state
      ≤ biotSavartConstantSq * shellVorticityL2Squared j N state

    shellBernsteinL2ToLInfinity : ∀ j N state →
      shellLInfinitySquared j N state
      ≤
      bernsteinConstantSq
      * pow2 (threeTimes j)
      * shellL2Squared j N state

    shellVorticityBernstein : ∀ j N state →
      shellVorticityLInfinitySquared j N state
      ≤
      bernsteinConstantSq
      * pow2 (fiveTimes j)
      * shellL2Squared j N state

    integerLatticeYoungConvolution : ∀ N state →
      convolutionOutputSquared N state
      ≤ youngConstantSq * convolutionInputSquared N state

    integerShellWeightedConvolutionUniform : ∀ N state →
      convolutionOutputSquared N state
      ≤ youngConstantSq * convolutionInputSquared N state

    Triad : Set
    triadOutput triadLeft triadRight : Triad → Mode
    multiplierMagnitude : Mode → Nat
    triadWeightConstant : Nat
    triadShellWeightEquivalence : ∀ triad →
      multiplierMagnitude (triadOutput triad)
      ≤
      triadWeightConstant
      * (multiplierMagnitude (triadLeft triad)
      + multiplierMagnitude (triadRight triad))

    fullShellRowSchurUniform : ∀ j N state →
      shellRowAbsoluteSum j N state ≤ rowSchurConstant
    fullShellColumnSchurUniform : ∀ l N state →
      shellColumnAbsoluteSum l N state ≤ columnSchurConstant

    fullShellSchurOperatorBound : ∀ N state →
      schurOutputSquared N state
      ≤ schurOperatorConstantSq * schurInputSquared N state

    multiplierWeight : Mode → Int.ℤ
    multiplierDifference : Mode → Mode → Int.ℤ
    multiplierDifferenceMagnitude modeRadius
      multiplierGradientEnvelope : Mode → Mode → Nat
    multiplierDifferenceExactIdentity : ∀ triad →
      multiplierDifference (triadOutput triad) (triadRight triad)
      ≡
      Int._+_
        (multiplierWeight (triadOutput triad))
        (Int.-_ (multiplierWeight (triadRight triad)))
    lowHighMultiplierDifferenceGain : ∀ triad →
      multiplierDifferenceMagnitude
        (triadOutput triad) (triadRight triad)
      ≤
      modeRadius (triadLeft triad) (triadRight triad)
      * multiplierGradientEnvelope
          (triadLeft triad) (triadRight triad)
    commutatorValue directWeightedValue transportedWeightedValue :
      Triad → Int.ℤ
    lowHighMultiplierCommutatorIdentity : ∀ triad →
      commutatorValue triad
      ≡
      Int._+_
        (directWeightedValue triad)
        (Int.-_ (transportedWeightedValue triad))

    farLowCommutatorGainsRadius : ∀ radius N state →
      commutatorRemainderSquared radius N state
      ≤
      commutatorConstantSq
      * commutatorInputSquared radius N state

    farHighSobolevTailGainsRadius : ∀ radius N state →
      farHighTailSquared radius N state
      ≤ tailConstantSq * farHighSobolevSquared radius N state

    analyticTail analyticTailMajorant :
      Nat → Nat → Nat
    uniformAnalyticTailDecay : ∀ alpha radius →
      analyticTail alpha radius
      ≤ analyticTailMajorant alpha radius

open PeriodicUniformHarmonicAnalysis public

record CutoffIndependentHarmonicConstants
    {c s : Level}
    (H : PeriodicUniformHarmonicAnalysis {c} {s}) : Set where
  constructor constants-outside-cutoff
  field
    parseval bernstein biotSavart shellCount young
      rowSchur columnSchur schur commutator tail : Nat

allHarmonicConstantsIndependentOfCutoff :
  ∀ {c s} (H : PeriodicUniformHarmonicAnalysis {c} {s}) →
  CutoffIndependentHarmonicConstants H
allHarmonicConstantsIndependentOfCutoff H =
  constants-outside-cutoff
    (parsevalConstantSq H)
    (bernsteinConstantSq H)
    (biotSavartConstantSq H)
    (shellCountConstant H)
    (youngConstantSq H)
    (rowSchurConstant H)
    (columnSchurConstant H)
    (schurOperatorConstantSq H)
    (commutatorConstantSq H)
    (tailConstantSq H)

uniformHarmonicAnalysisTheoremSurfaceImplemented : Bool
uniformHarmonicAnalysisTheoremSurfaceImplemented = true

uniformHarmonicAnalysisTheoremSurfaceImplementedIsTrue :
  uniformHarmonicAnalysisTheoremSurfaceImplemented ≡ true
uniformHarmonicAnalysisTheoremSurfaceImplementedIsTrue = refl

uniformHarmonicAnalysisPackageClosed : Bool
uniformHarmonicAnalysisPackageClosed = false

uniformHarmonicAnalysisPackageClosedIsFalse :
  uniformHarmonicAnalysisPackageClosed ≡ false
uniformHarmonicAnalysisPackageClosedIsFalse = refl
