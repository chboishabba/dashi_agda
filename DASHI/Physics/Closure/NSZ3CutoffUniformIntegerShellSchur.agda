module DASHI.Physics.Closure.NSZ3CutoffUniformIntegerShellSchur where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Builtin.List using (List)
open import Data.Nat renaming (_≤_ to _≤ⁿ_)
open import Relation.Nullary using (¬_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSCompactGammaFullShellSchur as FullShell
import DASHI.Physics.Closure.NSCutoffUniformIntegerShellSchur as SC

------------------------------------------------------------------------
-- Concrete Z^3 carrier for SC1--SC9.
--
-- This module removes the remaining carrier-level ambiguity from the generic
-- programme.  Modes are literally FourierMode = Z^3, resonant pairs literally
-- carry two Fourier modes, and resonance is literally p + q = k.
--
-- The deep lattice-counting and analytic inequalities are still proof fields,
-- but they are now quantified over these concrete objects and are assembled by
-- one constructor into the existing SC1--SC9 endpoint.  No Boolean receipts or
-- unrelated scalar summaries can inhabit the package.
------------------------------------------------------------------------

record Z3ResonantPair : Set where
  constructor pair
  field
    left right : Z3.FourierMode

open Z3ResonantPair public

subtractMode : Z3.FourierMode → Z3.FourierMode → Z3.FourierMode
subtractMode k p = Z3.addMode k (Z3.negateMode p)

Z3Resonant : Z3.FourierMode → Z3ResonantPair → Set
Z3Resonant k interaction =
  Z3.addMode (left interaction) (right interaction) ≡ k

------------------------------------------------------------------------
-- SC1--SC2: concrete integer-shell enumeration evidence.
------------------------------------------------------------------------

record Z3ShellEvidence {i : Level} : Set (lsuc i) where
  field
    Shell : Nat → Z3.FourierMode → Set i
    normIndex : Z3.FourierMode → Nat
    bracketWeight : Nat → Z3.FourierMode → Nat

    shellCardinality : Nat → Nat
    shellCardinalityConstant : Nat

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

    cutoffShell : Nat → Nat → Z3.FourierMode → Set i
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

open Z3ShellEvidence public

z3IntegerShellEnumeration :
  ∀ {i} →
  Z3ShellEvidence {i = i} →
  SC.IntegerShellEnumeration {i = i} Z3.FourierMode
z3IntegerShellEnumeration E = record
  { Shell = Shell E
  ; normIndex = normIndex E
  ; bracketWeight = bracketWeight E
  ; shellCardinality = shellCardinality E
  ; shellCardinalityConstant = shellCardinalityConstant E
  ; DyadicShellCardinalityBound = DyadicShellCardinalityBound E
  ; dyadicShellCardinalityBound = dyadicShellCardinalityBound E
  ; weightedShellSum = weightedShellSum E
  ; WeightedShellBound = WeightedShellBound E
  ; weightedShellBound = weightedShellBound E
  ; radialTail = radialTail E
  ; SigmaAboveDimension = SigmaAboveDimension E
  ; RadialTailBound = RadialTailBound E
  ; radialTailBound = radialTailBound E
  ; cutoffShell = cutoffShell E
  ; shellCutoffStable = shellCutoffStable E
  ; Fold = Fold E
  ; largestParticipatingShell = largestParticipatingShell E
  ; foldAtCutoff = foldAtCutoff E
  ; foldCutoffStable = foldCutoffStable E
  }

------------------------------------------------------------------------
-- SC3--SC4: exact resonant-pair enumeration and zero-mode exclusion.
------------------------------------------------------------------------

record Z3ResonantPairEvidence
    {i : Level}
    (shells : Z3ShellEvidence {i = i}) : Set (lsuc i) where
  field
    parameterize :
      ∀ k interaction →
      Z3Resonant k interaction →
      right interaction ≡ subtractMode k (left interaction)

    reconstruct :
      ∀ k interaction →
      right interaction ≡ subtractMode k (left interaction) →
      Z3Resonant k interaction

    ShellPair : Nat → Nat → Z3.FourierMode → Z3ResonantPair → Set i
    pairListAt : Nat → Nat → Nat → Z3.FourierMode → Z3ResonantPair → Set i

    pairEnumerationSound :
      ∀ a b N k interaction →
      pairListAt a b N k interaction →
      ShellPair a b k interaction

    pairEnumerationComplete :
      ∀ a b N k interaction →
      ShellPair a b k interaction →
      pairListAt a b N k interaction

    pairEnumerationNoDuplicates :
      ∀ a b N k interaction →
      (first second : pairListAt a b N k interaction) →
      first ≡ second

    CutoffAdmissiblePair : Nat → Z3ResonantPair → Set i
    cutoffRestrictionExact :
      ∀ a b N k interaction →
      pairListAt a b N k interaction →
      CutoffAdmissiblePair N interaction

    InteractionAdmissible : Z3ResonantPair → Set i

    leftDenominatorNonzero :
      ∀ a b k interaction →
      ShellPair a b k interaction →
      InteractionAdmissible interaction →
      ¬ (left interaction ≡ Z3.zeroMode)

    rightDenominatorNonzero :
      ∀ a b k interaction →
      ShellPair a b k interaction →
      InteractionAdmissible interaction →
      ¬ (right interaction ≡ Z3.zeroMode)

    targetDenominatorNonzero :
      ∀ a b k interaction →
      ShellPair a b k interaction →
      InteractionAdmissible interaction →
      ¬ (k ≡ Z3.zeroMode)

open Z3ResonantPairEvidence public

z3ResonantPairEnumeration :
  ∀ {i}
    {shells : Z3ShellEvidence {i = i}} →
  Z3ResonantPairEvidence shells →
  SC.ResonantPairEnumeration
    Z3.FourierMode Z3ResonantPair
    (z3IntegerShellEnumeration shells)
z3ResonantPairEnumeration {shells = shells} E = record
  { add = Z3.addMode
  ; subtract = subtractMode
  ; leftMode = left
  ; rightMode = right
  ; Resonant = Z3Resonant
  ; parameterize = parameterize E
  ; reconstruct = reconstruct E
  ; ShellPair = ShellPair E
  ; pairListAt = pairListAt E
  ; pairEnumerationSound = pairEnumerationSound E
  ; pairEnumerationComplete = pairEnumerationComplete E
  ; pairEnumerationNoDuplicates = pairEnumerationNoDuplicates E
  ; CutoffAdmissiblePair = CutoffAdmissiblePair E
  ; cutoffRestrictionExact = cutoffRestrictionExact E
  ; zeroMode = Z3.zeroMode
  ; InteractionAdmissible = InteractionAdmissible E
  ; leftDenominatorNonzero = leftDenominatorNonzero E
  ; rightDenominatorNonzero = rightDenominatorNonzero E
  ; targetDenominatorNonzero = targetDenominatorNonzero E
  }

------------------------------------------------------------------------
-- SC5: concrete weighted shell convolution over Z^3 resonant pairs.
------------------------------------------------------------------------

record Z3WeightedConvolutionEvidence
    {s i : Level}
    (Scalar : Set s)
    (shells : Z3ShellEvidence {i = i})
    (pairs : Z3ResonantPairEvidence shells) :
    Set (lsuc (s ⊔ i)) where
  field
    _≤_ : Scalar → Scalar → Set s
    shellConvolution :
      Nat → Nat → Nat → Nat → Nat → Nat → Z3.FourierMode → Scalar
    theta : Nat → Nat → Nat → Nat → Nat → Nat → Scalar
    convolutionConstant : Nat → Nat → Nat → Scalar

    weightedShellConvolutionBound :
      ∀ alpha beta gamma K a b k →
      Shell shells K k →
      _≤_
        (shellConvolution alpha beta gamma K a b k)
        (theta alpha beta gamma K a b)

    decayExponent : Nat → Nat → Nat → Nat
    globalConvolution : Nat → Nat → Z3.FourierMode → Scalar
    globalConvolutionBound :
      ∀ beta gamma k →
      _≤_
        (globalConvolution beta gamma k)
        (convolutionConstant beta gamma)

    Endpoint : Nat → Nat → Set i
    EndpointLogarithmicBound : Nat → Nat → Z3.FourierMode → Set i
    endpointLogarithmicBound :
      ∀ beta gamma k →
      Endpoint beta gamma →
      EndpointLogarithmicBound beta gamma k

open Z3WeightedConvolutionEvidence public

z3WeightedShellConvolution :
  ∀ {s i}
    {Scalar : Set s}
    {shells : Z3ShellEvidence {i = i}}
    {pairs : Z3ResonantPairEvidence shells} →
  Z3WeightedConvolutionEvidence Scalar shells pairs →
  SC.WeightedShellConvolution Scalar
    (z3IntegerShellEnumeration shells)
    (z3ResonantPairEnumeration pairs)
z3WeightedShellConvolution E = record
  { _≤_ = _≤_ E
  ; shellConvolution = shellConvolution E
  ; theta = theta E
  ; convolutionConstant = convolutionConstant E
  ; weightedShellConvolutionBound = weightedShellConvolutionBound E
  ; decayExponent = decayExponent E
  ; globalConvolution = globalConvolution E
  ; globalConvolutionBound = globalConvolutionBound E
  ; Endpoint = Endpoint E
  ; EndpointLogarithmicBound = EndpointLogarithmicBound E
  ; endpointLogarithmicBound = endpointLogarithmicBound E
  }

------------------------------------------------------------------------
-- SC6--SC9: exact full-shell kernel, cutoff restriction, and Schur action.
------------------------------------------------------------------------

record Z3SC1ToSC9Evidence
    {s i v : Level}
    (Scalar : Set s)
    (Vector : Set v)
    (F : FullShell.FullShellFourierFamily
      {i = i} Z3ResonantPair Z3.FourierMode Scalar) :
    Set (lsuc (s ⊔ i ⊔ v)) where
  field
    shells : Z3ShellEvidence {i = i}
    resonantPairs : Z3ResonantPairEvidence shells
    convolution : Z3WeightedConvolutionEvidence Scalar shells resonantPairs

    cutoffUniformKernel : SC.CutoffUniformFullShellKernel F
    squaredAction : SC.SquaredSchurAction F Vector

open Z3SC1ToSC9Evidence public

z3CutoffUniformIntegerShellSchurProgram :
  ∀ {s i v}
    {Scalar : Set s}
    {Vector : Set v}
    {F : FullShell.FullShellFourierFamily
      {i = i} Z3ResonantPair Z3.FourierMode Scalar} →
  Z3SC1ToSC9Evidence Scalar Vector F →
  SC.CutoffUniformIntegerShellSchurProgram
    Z3ResonantPair Z3.FourierMode Scalar Vector F
z3CutoffUniformIntegerShellSchurProgram E = record
  { integerShells = z3IntegerShellEnumeration (shells E)
  ; resonantPairs = z3ResonantPairEnumeration (resonantPairs E)
  ; convolution = z3WeightedShellConvolution (convolution E)
  ; cutoffUniformKernel = cutoffUniformKernel E
  ; squaredAction = squaredAction E
  }

z3UniformFullShellSchurSquared :
  ∀ {s i v}
    {Scalar : Set s}
    {Vector : Set v}
    {F : FullShell.FullShellFourierFamily
      {i = i} Z3ResonantPair Z3.FourierMode Scalar} →
  (E : Z3SC1ToSC9Evidence Scalar Vector F) →
  ∀ K N f →
  SC._≤²_ (squaredAction E)
    (SC.normSquared (squaredAction E) K N
      (SC.applyKernel (squaredAction E) K N f))
    (SC.multiplyScalar (squaredAction E)
      (SC.multiplyScalar (squaredAction E)
        (SC.rowBudget (cutoffUniformKernel E))
        (SC.columnBudget (cutoffUniformKernel E)))
      (SC.normSquared (squaredAction E) K N f))
z3UniformFullShellSchurSquared E =
  SC.uniformFullShellSchurSquared
    (cutoffUniformKernel E)
    (squaredAction E)
