module DASHI.Physics.Closure.NSZ3QuantitativeSchurWitnesses where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (_≤_; _+_; _*_; _^_; suc)
open import Relation.Nullary using (¬_)

import DASHI.Analysis.FiniteWeightedKernelSums as Sums
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSCompactGammaFullShellSchur as FullShell
import DASHI.Physics.Closure.NSCutoffUniformIntegerShellSchur as SC
import DASHI.Physics.Closure.NSZ3CutoffUniformIntegerShellSchur as Z3SC

------------------------------------------------------------------------
-- Concrete quantitative witness leaves for the Z^3 full-shell Schur lane.
--
-- Unlike the generic SC1--SC9 surfaces, every predicate below is tied to an
-- actual finite enumeration, an actual list length, or an actual row/column
-- fold of the full-shell kernel.  The module does not postulate the hard
-- inequalities: it packages precisely the witnesses required to prove them.
------------------------------------------------------------------------

record Z3FiniteEnumeration {i : Level} : Set (lsuc i) where
  field
    shellModes : Nat → List Z3.FourierMode
    cutoffShellModes : Nat → Nat → List Z3.FourierMode

    Occurs : List Z3.FourierMode → Z3.FourierMode → Set i
    NoDuplicates : List Z3.FourierMode → Set i
    length : List Z3.FourierMode → Nat

    Shell : Nat → Z3.FourierMode → Set i
    InCutoffCube : Nat → Z3.FourierMode → Set i

    shellSound :
      ∀ j k → Occurs (shellModes j) k → Shell j k
    shellComplete :
      ∀ j k → Shell j k → Occurs (shellModes j) k
    shellNoDuplicates :
      ∀ j → NoDuplicates (shellModes j)

    cutoffShellSound :
      ∀ j N k → Occurs (cutoffShellModes j N) k →
      Shell j k
    cutoffShellCutoffSound :
      ∀ j N k → Occurs (cutoffShellModes j N) k →
      InCutoffCube N k
    cutoffShellComplete :
      ∀ j N k → Shell j k → InCutoffCube N k →
      Occurs (cutoffShellModes j N) k
    cutoffShellNoDuplicates :
      ∀ j N → NoDuplicates (cutoffShellModes j N)

open Z3FiniteEnumeration public

------------------------------------------------------------------------
-- 1. Dyadic shell cardinality.
------------------------------------------------------------------------

record Z3DyadicShellCardinalityWitness
    {i : Level}
    (E : Z3FiniteEnumeration {i = i}) : Set (lsuc i) where
  field
    shellConstant : Nat
    shellConstantPositive : 1 ≤ shellConstant

    dyadicShellCardinality :
      ∀ j →
      length E (shellModes E j) ≤
      shellConstant * (2 ^ (3 * j))

open Z3DyadicShellCardinalityWitness public

------------------------------------------------------------------------
-- 2. Weighted shell sums and radial tails.
------------------------------------------------------------------------

record Z3WeightedRadialWitness
    {i : Level}
    (E : Z3FiniteEnumeration {i = i}) : Set (lsuc i) where
  field
    weightedModeValue : Nat → Z3.FourierMode → Nat
    weightedShellFold : Nat → Nat → Nat
    radialTailFold : Nat → Nat → Nat

    weightedShellFoldIsEnumeration :
      ∀ sigma j → Set i
    radialTailFoldIsEnumeration :
      ∀ sigma J → Set i

    weightedConstant : Nat → Nat
    weightedShellBound :
      ∀ sigma j →
      weightedShellFold sigma j ≤
      weightedConstant sigma * (2 ^ ((3 + sigma) * j))

    SigmaAboveDimension : Nat → Set i
    radialConstant : Nat → Nat
    radialTailBound :
      ∀ sigma J → SigmaAboveDimension sigma →
      radialTailFold sigma J ≤ radialConstant sigma

open Z3WeightedRadialWitness public

------------------------------------------------------------------------
-- 3. Exact cutoff-stable enumeration.
------------------------------------------------------------------------

record Z3CutoffStableEnumerationWitness
    {i : Level}
    (E : Z3FiniteEnumeration {i = i}) : Set (lsuc i) where
  field
    CutoffContainsShell : Nat → Nat → Set i

    cutoffContainsShellSound :
      ∀ j N → CutoffContainsShell j N →
      ∀ k → Shell E j k → InCutoffCube E N k

    cutoffEnumerationStable :
      ∀ j N → CutoffContainsShell j N →
      cutoffShellModes E j N ≡ shellModes E j

    cutoffEmbedding :
      ∀ j N N′ → N ≤ N′ →
      ∀ k → Occurs E (cutoffShellModes E j N) k →
      Occurs E (cutoffShellModes E j N′) k

open Z3CutoffStableEnumerationWitness public

------------------------------------------------------------------------
-- 4. Shell-pair intersection counting.
------------------------------------------------------------------------

record Z3ShellPairCountingWitness
    {i : Level}
    (E : Z3FiniteEnumeration {i = i}) : Set (lsuc i) where
  field
    resonantPairsAt :
      Nat → Nat → Nat → Z3.FourierMode → List Z3SC.Z3ResonantPair

    OccursPair :
      List Z3SC.Z3ResonantPair → Z3SC.Z3ResonantPair → Set i
    NoPairDuplicates : List Z3SC.Z3ResonantPair → Set i
    pairLength : List Z3SC.Z3ResonantPair → Nat

    pairSound :
      ∀ a b N k interaction →
      OccursPair (resonantPairsAt a b N k) interaction →
      Z3SC.Z3Resonant k interaction

    leftShellSound :
      ∀ a b N k interaction →
      OccursPair (resonantPairsAt a b N k) interaction →
      Shell E a (Z3SC.left interaction)

    rightShellSound :
      ∀ a b N k interaction →
      OccursPair (resonantPairsAt a b N k) interaction →
      Shell E b (Z3SC.right interaction)

    pairNoDuplicates :
      ∀ a b N k → NoPairDuplicates (resonantPairsAt a b N k)

    intersectionConstant : Nat
    shellPairIntersectionBound :
      ∀ a b N k →
      pairLength (resonantPairsAt a b N k) ≤
      intersectionConstant * (2 ^ (2 * a))

open Z3ShellPairCountingWitness public

------------------------------------------------------------------------
-- 5. Angular/polarization majorant.
------------------------------------------------------------------------

record Z3AngularPolarizationWitness
    {s i : Level}
    (Scalar : Set s)
    (F : FullShell.FullShellFourierFamily
      {i = i} Z3SC.Z3ResonantPair Z3.FourierMode Scalar) :
    Set (lsuc (s ⊔ i)) where
  field
    angularConstant : Scalar

    angularMajorant :
      ∀ K N interaction →
      FullShell.OccursPair F
        (FullShell.pairs (FullShell.pairDataAt F K N)) interaction →
      FullShell._≤_ (FullShell.pairDataAt F K N)
        (FullShell.localFourierResponse F K N interaction)
        angularConstant

    parallelConfigurationCovered :
      ∀ K N interaction → Set i
    antiparallelConfigurationCovered :
      ∀ K N interaction → Set i
    degenerateConfigurationCovered :
      ∀ K N interaction → Set i

open Z3AngularPolarizationWitness public

------------------------------------------------------------------------
-- 6. Weighted convolution summability.
------------------------------------------------------------------------

record Z3WeightedConvolutionSummabilityWitness
    {s i : Level}
    (Scalar : Set s)
    (E : Z3FiniteEnumeration {i = i}) : Set (lsuc (s ⊔ i)) where
  field
    _≤s_ : Scalar → Scalar → Set s
    shellConvolution :
      Nat → Nat → Nat → Nat → Nat → Nat → Z3.FourierMode → Scalar
    shellMajorant : Nat → Nat → Nat → Nat → Nat → Nat → Scalar

    shellConvolutionBound :
      ∀ alpha beta gamma K a b k →
      Shell E K k →
      _≤s_
        (shellConvolution alpha beta gamma K a b k)
        (shellMajorant alpha beta gamma K a b)

    globalConvolution : Nat → Nat → Z3.FourierMode → Scalar
    globalConstant : Nat → Nat → Scalar
    globalSummability :
      ∀ beta gamma k →
      _≤s_ (globalConvolution beta gamma k)
            (globalConstant beta gamma)

open Z3WeightedConvolutionSummabilityWitness public

------------------------------------------------------------------------
-- 7. Cutoff-independent row and column constants.
------------------------------------------------------------------------

record Z3CutoffIndependentSchurConstants
    {s i : Level}
    (Scalar : Set s)
    (F : FullShell.FullShellFourierFamily
      {i = i} Z3SC.Z3ResonantPair Z3.FourierMode Scalar) :
    Set (lsuc (s ⊔ i)) where
  field
    rowConstant columnConstant : Scalar

    rowBound :
      ∀ K N target →
      FullShell._≤_ (FullShell.fullShellKernelAt F K N)
        (Sums.rowWeightedSum (FullShell.fullShellKernelAt F K N) target)
        (FullShell.multiply (FullShell.fullShellKernelAt F K N)
          rowConstant
          (FullShell.rowWeight (FullShell.fullShellKernelAt F K N) target))

    columnBound :
      ∀ K N source →
      FullShell._≤_ (FullShell.fullShellKernelAt F K N)
        (Sums.columnWeightedSum (FullShell.fullShellKernelAt F K N) source)
        (FullShell.multiply (FullShell.fullShellKernelAt F K N)
          columnConstant
          (FullShell.colWeight (FullShell.fullShellKernelAt F K N) source))

    SmallerCarrier : Nat → Z3.FourierMode → Set i
    cutoffKernelExtension :
      ∀ K N N′ → N ≤ N′ →
      ∀ target source →
      SmallerCarrier N target → SmallerCarrier N source →
      FullShell.kernel (FullShell.fullShellKernelAt F K N) target source ≡
      FullShell.kernel (FullShell.fullShellKernelAt F K N′) target source

open Z3CutoffIndependentSchurConstants public

z3CutoffUniformKernelFromWitnesses :
  ∀ {s i}
    {Scalar : Set s}
    {F : FullShell.FullShellFourierFamily
      {i = i} Z3SC.Z3ResonantPair Z3.FourierMode Scalar} →
  Z3CutoffIndependentSchurConstants Scalar F →
  SC.CutoffUniformFullShellKernel F
z3CutoffUniformKernelFromWitnesses W = record
  { rowBudget = rowConstant W
  ; columnBudget = columnConstant W
  ; rowEstimate = rowBound W
  ; columnEstimate = columnBound W
  ; SmallerCarrier = SmallerCarrier W
  ; cutoffKernelExtension = cutoffKernelExtension W
  }

------------------------------------------------------------------------
-- Complete witness bundle.  Inhabiting this record supplies every requested
-- quantitative leaf and promotes the row/column witnesses to SC6--SC8.
------------------------------------------------------------------------

record Z3CompleteQuantitativeWitnesses
    {s i : Level}
    (Scalar : Set s)
    (F : FullShell.FullShellFourierFamily
      {i = i} Z3SC.Z3ResonantPair Z3.FourierMode Scalar) :
    Set (lsuc (s ⊔ i)) where
  field
    enumeration : Z3FiniteEnumeration {i = i}
    dyadicCardinality : Z3DyadicShellCardinalityWitness enumeration
    weightedRadial : Z3WeightedRadialWitness enumeration
    cutoffStability : Z3CutoffStableEnumerationWitness enumeration
    shellPairCounting : Z3ShellPairCountingWitness enumeration
    angularPolarization : Z3AngularPolarizationWitness Scalar F
    convolutionSummability :
      Z3WeightedConvolutionSummabilityWitness Scalar enumeration
    cutoffIndependentConstants :
      Z3CutoffIndependentSchurConstants Scalar F

open Z3CompleteQuantitativeWitnesses public
