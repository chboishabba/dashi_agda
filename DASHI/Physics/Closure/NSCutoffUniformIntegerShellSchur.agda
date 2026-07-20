module DASHI.Physics.Closure.NSCutoffUniformIntegerShellSchur where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)
open import Data.Nat renaming (_≤_ to _≤ⁿ_)
open import Relation.Nullary using (¬_)

import DASHI.Physics.Closure.NSCompactGammaFullShellSchur as FullShell

------------------------------------------------------------------------
-- Cutoff-uniform integer-shell Schur programme (SC1--SC9).
--
-- The existing full-shell owner constructs an exact finite kernel from the
-- pair-incidence fold.  This module separates the genuinely uniform analytic
-- leaves from that finite representation and exposes the final squared Schur
-- estimate as a theorem.
--
-- No cardinality, convolution, or cutoff statement below is represented by a
-- Boolean receipt.  Concrete Z^3 instances must provide proof-relevant
-- witnesses for every quantified shell, cutoff, target, source, and pair.
------------------------------------------------------------------------

record IntegerShellEnumeration
    {m i : Level}
    (Mode : Set m) : Set (lsuc (m ⊔ i)) where
  field
    Shell : Nat → Mode → Set i
    normIndex : Mode → Nat
    bracketWeight : Nat → Mode → Nat

    shellCardinality : Nat → Nat
    shellCardinalityConstant : Nat

    -- SC1: # A_j <= C_shell 2^(3j), with the dyadic expression owned by
    -- the concrete arithmetic instance.
    DyadicShellCardinalityBound : Nat → Nat → Nat → Set i
    dyadicShellCardinalityBound :
      ∀ j →
      DyadicShellCardinalityBound
        (shellCardinality j) shellCardinalityConstant j

    weightedShellSum : Nat → Nat → Nat
    WeightedShellBound : Nat → Nat → Nat → Set i
    weightedShellBound :
      ∀ sigma j →
      WeightedShellBound sigma j (weightedShellSum sigma j)

    radialTail : Nat → Nat → Nat
    SigmaAboveDimension : Nat → Set i
    RadialTailBound : Nat → Nat → Nat → Set i
    radialTailBound :
      ∀ sigma J →
      SigmaAboveDimension sigma →
      RadialTailBound sigma J (radialTail sigma J)

    -- SC2: literal stabilization of shell enumeration above the largest
    -- participating radius.
    cutoffShell : Nat → Nat → Mode → Set i
    shellCutoffStable :
      ∀ j N →
      2 ≤ⁿ N →
      (∀ k → Shell j k → cutoffShell j N k) →
      ∀ k → cutoffShell j N k → Shell j k

    Fold : Set i
    largestParticipatingShell : Fold → Nat
    foldAtCutoff : Fold → Nat → Set i
    foldCutoffStable :
      ∀ fold N →
      largestParticipatingShell fold ≤ⁿ N →
      foldAtCutoff fold N

open IntegerShellEnumeration public

record ResonantPairEnumeration
    {m p i : Level}
    (Mode : Set m)
    (Pair : Set p)
    (E : IntegerShellEnumeration {i = i} Mode) :
    Set (lsuc (m ⊔ p ⊔ i)) where
  field
    add : Mode → Mode → Mode
    subtract : Mode → Mode → Mode
    leftMode rightMode : Pair → Mode

    Resonant : Mode → Pair → Set i
    parameterize :
      ∀ k p → Resonant k p → rightMode p ≡ subtract k (leftMode p)
    reconstruct :
      ∀ k p → rightMode p ≡ subtract k (leftMode p) → Resonant k p

    -- SC3: shell-pair incidence and exact finite enumeration.
    ShellPair : Nat → Nat → Mode → Pair → Set i
    pairListAt : Nat → Nat → Nat → Mode → Set i
    pairEnumerationSound :
      ∀ a b N k pair →
      pairListAt a b N k →
      ShellPair a b k pair
    pairEnumerationComplete :
      ∀ a b N k pair →
      ShellPair a b k pair →
      pairListAt a b N k
    pairEnumerationNoDuplicates :
      ∀ a b N k pair →
      (left right : pairListAt a b N k) →
      left ≡ right

    CutoffAdmissiblePair : Nat → Pair → Set i
    cutoffRestrictionExact :
      ∀ a b N k pair →
      pairListAt a b N k →
      CutoffAdmissiblePair N pair

    -- SC4: every denominator-bearing mode is nonzero on admissible pairs.
    zeroMode : Mode
    InteractionAdmissible : Pair → Set i
    leftDenominatorNonzero :
      ∀ a b k pair →
      ShellPair a b k pair →
      InteractionAdmissible pair →
      ¬ (leftMode pair ≡ zeroMode)
    rightDenominatorNonzero :
      ∀ a b k pair →
      ShellPair a b k pair →
      InteractionAdmissible pair →
      ¬ (rightMode pair ≡ zeroMode)
    targetDenominatorNonzero :
      ∀ a b k pair →
      ShellPair a b k pair →
      InteractionAdmissible pair →
      ¬ (k ≡ zeroMode)

open ResonantPairEnumeration public

record WeightedShellConvolution
    {m p s i : Level}
    {Mode : Set m}
    {Pair : Set p}
    (Scalar : Set s)
    (E : IntegerShellEnumeration {i = i} Mode)
    (R : ResonantPairEnumeration Mode Pair E) :
    Set (lsuc (m ⊔ p ⊔ s ⊔ i)) where
  field
    _≤_ : Scalar → Scalar → Set s
    shellConvolution : Nat → Nat → Nat → Nat → Nat → Nat → Mode → Scalar
    theta : Nat → Nat → Nat → Nat → Nat → Nat → Scalar
    convolutionConstant : Nat → Nat → Nat → Scalar

    -- SC5: exact weighted shell convolution for the selected exponents.
    weightedShellConvolutionBound :
      ∀ alpha beta gamma K a b k →
      Shell E K k →
      _≤_
        (shellConvolution alpha beta gamma K a b k)
        (theta alpha beta gamma K a b)

    decayExponent : Nat → Nat → Nat → Nat
    globalConvolution : Nat → Nat → Mode → Scalar
    globalConvolutionBound :
      ∀ beta gamma k →
      _≤_
        (globalConvolution beta gamma k)
        (convolutionConstant beta gamma)

    Endpoint : Nat → Nat → Set i
    EndpointLogarithmicBound : Nat → Nat → Mode → Set i
    endpointLogarithmicBound :
      ∀ beta gamma k →
      Endpoint beta gamma →
      EndpointLogarithmicBound beta gamma k

open WeightedShellConvolution public

record CutoffUniformFullShellKernel
    {p m s i : Level}
    {Pair : Set p}
    {Mode : Set m}
    {Scalar : Set s}
    (F : FullShell.FullShellFourierFamily {i = i} Pair Mode Scalar) :
    Set (lsuc (p ⊔ m ⊔ s ⊔ i)) where
  field
    rowBudget : Scalar
    columnBudget : Scalar

    -- SC6 and SC7, with constants independent of K and N by construction.
    rowEstimate :
      ∀ K N target →
      FullShell._≤_ (FullShell.fullShellKernelAt F K N)
        (FullShell.rowWeightedSum (FullShell.fullShellKernelAt F K N) target)
        (FullShell.multiply (FullShell.fullShellKernelAt F K N)
          rowBudget
          (FullShell.rowWeight (FullShell.fullShellKernelAt F K N) target))

    columnEstimate :
      ∀ K N source →
      FullShell._≤_ (FullShell.fullShellKernelAt F K N)
        (FullShell.columnWeightedSum (FullShell.fullShellKernelAt F K N) source)
        (FullShell.multiply (FullShell.fullShellKernelAt F K N)
          columnBudget
          (FullShell.colWeight (FullShell.fullShellKernelAt F K N) source))

    -- SC8: the smaller-cutoff kernel is literally the restriction of the
    -- larger one on the smaller carrier.
    SmallerCarrier : Nat → Mode → Set i
    cutoffKernelExtension :
      ∀ K N₁ N₂ →
      N₁ ≤ⁿ N₂ →
      ∀ k ell →
      SmallerCarrier N₁ k →
      SmallerCarrier N₁ ell →
      FullShell.kernel (FullShell.fullShellKernelAt F K N₁) k ell ≡
      FullShell.kernel (FullShell.fullShellKernelAt F K N₂) k ell

open CutoffUniformFullShellKernel public

record SquaredSchurAction
    {p m s i v : Level}
    {Pair : Set p}
    {Mode : Set m}
    {Scalar : Set s}
    (F : FullShell.FullShellFourierFamily {i = i} Pair Mode Scalar)
    (Vector : Set v) : Set (lsuc (p ⊔ m ⊔ s ⊔ i ⊔ v)) where
  field
    normSquared : Nat → Nat → Vector → Scalar
    applyKernel : Nat → Nat → Vector → Vector
    multiplyScalar : Scalar → Scalar → Scalar
    _≤²_ : Scalar → Scalar → Set s

    -- The domain-neutral weighted Schur inequality.  This is the one algebraic
    -- implication used after SC6 and SC7; all analytic content remains in the
    -- row and column estimates.
    rowColumnImpliesSquaredBound :
      ∀ K N rowConstant columnConstant →
      (∀ target →
        FullShell._≤_ (FullShell.fullShellKernelAt F K N)
          (FullShell.rowWeightedSum (FullShell.fullShellKernelAt F K N) target)
          (FullShell.multiply (FullShell.fullShellKernelAt F K N)
            rowConstant
            (FullShell.rowWeight (FullShell.fullShellKernelAt F K N) target))) →
      (∀ source →
        FullShell._≤_ (FullShell.fullShellKernelAt F K N)
          (FullShell.columnWeightedSum (FullShell.fullShellKernelAt F K N) source)
          (FullShell.multiply (FullShell.fullShellKernelAt F K N)
            columnConstant
            (FullShell.colWeight (FullShell.fullShellKernelAt F K N) source))) →
      ∀ f →
      _≤²_
        (normSquared K N (applyKernel K N f))
        (multiplyScalar
          (multiplyScalar rowConstant columnConstant)
          (normSquared K N f))

open SquaredSchurAction public

-- SC9: uniform full-shell Schur theorem, squared form.
uniformFullShellSchurSquared :
  ∀ {p m s i v}
    {Pair : Set p}
    {Mode : Set m}
    {Scalar : Set s}
    {F : FullShell.FullShellFourierFamily {i = i} Pair Mode Scalar}
    {Vector : Set v} →
  (U : CutoffUniformFullShellKernel F) →
  (A : SquaredSchurAction F Vector) →
  ∀ K N f →
  _≤²_ A
    (normSquared A K N (applyKernel A K N f))
    (multiplyScalar A
      (multiplyScalar A (rowBudget U) (columnBudget U))
      (normSquared A K N f))
uniformFullShellSchurSquared U A K N =
  rowColumnImpliesSquaredBound A K N
    (rowBudget U)
    (columnBudget U)
    (rowEstimate U K N)
    (columnEstimate U K N)

schurConstantSquared :
  ∀ {p m s i}
    {Pair : Set p}
    {Mode : Set m}
    {Scalar : Set s}
    {F : FullShell.FullShellFourierFamily {i = i} Pair Mode Scalar} →
  CutoffUniformFullShellKernel F → Scalar
schurConstantSquared U =
  FullShell.multiply (FullShell.fullShellKernelAt _ 0 0)
    (rowBudget U)
    (columnBudget U)

record CutoffUniformIntegerShellSchurProgram
    {p m s i v : Level}
    (Pair : Set p)
    (Mode : Set m)
    (Scalar : Set s)
    (Vector : Set v)
    (F : FullShell.FullShellFourierFamily {i = i} Pair Mode Scalar) :
    Set (lsuc (p ⊔ m ⊔ s ⊔ i ⊔ v)) where
  field
    integerShells : IntegerShellEnumeration {i = i} Mode
    resonantPairs : ResonantPairEnumeration Mode Pair integerShells
    convolution : WeightedShellConvolution Scalar integerShells resonantPairs
    cutoffUniformKernel : CutoffUniformFullShellKernel F
    squaredAction : SquaredSchurAction F Vector

open CutoffUniformIntegerShellSchurProgram public
