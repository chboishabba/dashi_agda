module DASHI.Physics.Closure.NSTriadKNCauchyResolvedGramOperatorRound477Exact where

------------------------------------------------------------------------
-- ROUND477 / CAUCHY-RESOLVED FIXED-OUTPUT GRAM OPERATOR
--
-- Lean sibling provenance supplied 2026-09-07:
--   RequestProject/NavierStokes/OperatorSchurBlockCancellation.lean
--   RequestProject/NavierStokes/TransverseFrameSplit.lean
--
-- R473/R475 correctly formalise arbitrary diagonal coefficient weighting of the
-- bare signed R383 Gram matrix.  The Lean critical consumer is sharper: its
-- scalar polarization forms carry the nonseparable Cauchy kernel
--
--                 1 / (lambda_i + lambda_j).
--
-- This owner puts that pair kernel into the quadratic form explicitly.  The
-- normalization is carried only through the division-free receipt
--
--   resolventWeight i j * (rate i + rate j) = 1.
--
-- No analytic estimate is asserted here.  We prove the exact helical ++/--
-- decomposition of the resolved quadratic form and the concrete coefficient
-- l2 mass.  The only remaining producer leaves are the two scalar resolved-form
-- GramOperatorBounds.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNGramOperatorBoundConsumerRound471Exact as R471
import DASHI.Physics.Closure.NSTriadKNWeightedHelicalGramOperatorSplitRound475Exact as R475

F : C3.RealField _
F = Rational.rationalRealField

record CauchyResolvedCellFamily (Index : Set) : Set where
  constructor cauchy-resolved-cell-family
  field
    indices : List Index
    cell : Index → C3.Complex3 F
    rate : Index → ℚ
    resolventWeight : Index → Index → ℚ

    resolventSymmetric : ∀ i j → resolventWeight i j ≡ resolventWeight j i
    resolventLaw : ∀ i j →
      resolventWeight i j * (rate i + rate j) ≡ 1ℚ

open CauchyResolvedCellFamily public

resolvedAtom :
  ∀ {Index} →
  CauchyResolvedCellFamily Index →
  (Index → ℚ) → Index → Index → ℚ
resolvedAtom family coefficient i j =
  coefficient i * coefficient j
    * (resolventWeight family i j
      * R179.realHermitianCross (cell family i) (cell family j))

resolvedRow :
  ∀ {Index} →
  CauchyResolvedCellFamily Index →
  (Index → ℚ) → Index → List Index → ℚ
resolvedRow family coefficient i [] = 0ℚ
resolvedRow family coefficient i (j ∷ rest) =
  resolvedAtom family coefficient i j
    + resolvedRow family coefficient i rest

resolvedQuadraticFrom :
  ∀ {Index} →
  CauchyResolvedCellFamily Index →
  (Index → ℚ) → List Index → ℚ
resolvedQuadraticFrom family coefficient [] = 0ℚ
resolvedQuadraticFrom family coefficient (i ∷ rest) =
  resolvedRow family coefficient i (indices family)
    + resolvedQuadraticFrom family coefficient rest

resolvedQuadratic :
  ∀ {Index} →
  CauchyResolvedCellFamily Index →
  (Index → ℚ) → ℚ
resolvedQuadratic family coefficient =
  resolvedQuadraticFrom family coefficient (indices family)

coefficientMassAtom :
  ∀ {Index} →
  CauchyResolvedCellFamily Index →
  (Index → ℚ) → Index → ℚ
coefficientMassAtom family coefficient i =
  (coefficient i * coefficient i) * L2.complex3NormSquared (cell family i)

coefficientMassFrom :
  ∀ {Index} →
  CauchyResolvedCellFamily Index →
  (Index → ℚ) → List Index → ℚ
coefficientMassFrom family coefficient [] = 0ℚ
coefficientMassFrom family coefficient (i ∷ rest) =
  coefficientMassAtom family coefficient i
    + coefficientMassFrom family coefficient rest

coefficientMass :
  ∀ {Index} →
  CauchyResolvedCellFamily Index →
  (Index → ℚ) → ℚ
coefficientMass family coefficient =
  coefficientMassFrom family coefficient (indices family)

ResolvedGramOperatorBound :
  ∀ {Index} → CauchyResolvedCellFamily Index → ℚ → Set
ResolvedGramOperatorBound {Index} family A =
  R471.GramOperatorBound
    (Index → ℚ)
    (resolvedQuadratic family)
    (coefficientMass family)
    A

plusFamily :
  ∀ {Index}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode) →
  CauchyResolvedCellFamily Index → CauchyResolvedCellFamily Index
plusFamily E I S k family = record
  { indices = indices family
  ; cell = λ i → Helical.helicalProjectorPlus E I S k (cell family i)
  ; rate = rate family
  ; resolventWeight = resolventWeight family
  ; resolventSymmetric = resolventSymmetric family
  ; resolventLaw = resolventLaw family
  }

minusFamily :
  ∀ {Index}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode) →
  CauchyResolvedCellFamily Index → CauchyResolvedCellFamily Index
minusFamily E I S k family = record
  { indices = indices family
  ; cell = λ i → Helical.helicalProjectorMinus E I S k (cell family i)
  ; rate = rate family
  ; resolventWeight = resolventWeight family
  ; resolventSymmetric = resolventSymmetric family
  ; resolventLaw = resolventLaw family
  }

record AllIndexedTransverse
    {Index : Set}
    (E : C3.IntegerEmbedding F)
    (k : Z3.FourierMode)
    (family : CauchyResolvedCellFamily Index) : Set where
  constructor all-indexed-transverse
  field
    cellTransverse : (i : Index) → Helical.Transverse E k (cell family i)

open AllIndexedTransverse public

resolvedAtomHelicalSplit :
  ∀ {Index}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (family : CauchyResolvedCellFamily Index)
    (transverse : AllIndexedTransverse E k family)
    (coefficient : Index → ℚ)
    (i j : Index) →
  resolvedAtom family coefficient i j
  ≡ resolvedAtom (plusFamily E I S k family) coefficient i j
      + resolvedAtom (minusFamily E I S k family) coefficient i j
resolvedAtomHelicalSplit E I S L k family transverse coefficient i j =
  let
    u = cell family i
    v = cell family j
    up = Helical.helicalProjectorPlus E I S k u
    um = Helical.helicalProjectorMinus E I S k u
    vp = Helical.helicalProjectorPlus E I S k v
    vm = Helical.helicalProjectorMinus E I S k v

    uSplit : C3.complex3Add up um ≡ u
    uSplit = Helical.velocityHelicalDecomposition L k u (cellTransverse transverse i)

    vSplit : C3.complex3Add vp vm ≡ v
    vSplit = Helical.velocityHelicalDecomposition L k v (cellTransverse transverse j)

    expandedFour :
      R179.realHermitianCross
        (C3.complex3Add up um) (C3.complex3Add vp vm)
      ≡
      (R179.realHermitianCross up vp + R179.realHermitianCross up vm)
        + (R179.realHermitianCross um vp + R179.realHermitianCross um vm)
    expandedFour =
      trans
        (R291.realCrossAddLeft up um (C3.complex3Add vp vm))
        (cong₂ _+_
          (R291.realCrossAddRight up vp vm)
          (R291.realCrossAddRight um vp vm))

    plusMinusZero : R179.realHermitianCross up vm ≡ 0ℚ
    plusMinusZero = R287.outputPlusMinusRealGramZero E I S L k u v

    minusPlusZero : R179.realHermitianCross um vp ≡ 0ℚ
    minusPlusZero = R287.outputMinusPlusRealGramZero E I S L k u v

    mixedReduced :
      (R179.realHermitianCross up vp + R179.realHermitianCross up vm)
        + (R179.realHermitianCross um vp + R179.realHermitianCross um vm)
      ≡ R179.realHermitianCross up vp + R179.realHermitianCross um vm
    mixedReduced rewrite plusMinusZero | minusPlusZero =
      solve
        (R179.realHermitianCross up vp
          ∷ R179.realHermitianCross um vm ∷ [])

    gramSplit :
      R179.realHermitianCross u v
      ≡ R179.realHermitianCross up vp + R179.realHermitianCross um vm
    gramSplit =
      trans
        (cong₂ R179.realHermitianCross (sym uSplit) (sym vSplit))
        (trans expandedFour mixedReduced)

    scalar = coefficient i * coefficient j
    w = resolventWeight family i j
  in
  trans
    (cong (λ cross → scalar * (w * cross)) gramSplit)
    (solve
      (scalar ∷ w
        ∷ R179.realHermitianCross up vp
        ∷ R179.realHermitianCross um vm ∷ []))

resolvedRowHelicalSplit :
  ∀ {Index}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (family : CauchyResolvedCellFamily Index)
    (transverse : AllIndexedTransverse E k family)
    (coefficient : Index → ℚ)
    (i : Index)
    (js : List Index) →
  resolvedRow family coefficient i js
  ≡ resolvedRow (plusFamily E I S k family) coefficient i js
      + resolvedRow (minusFamily E I S k family) coefficient i js
resolvedRowHelicalSplit E I S L k family transverse coefficient i [] = solve []
resolvedRowHelicalSplit E I S L k family transverse coefficient i (j ∷ rest) =
  let
    head = resolvedAtomHelicalSplit E I S L k family transverse coefficient i j
    tail = resolvedRowHelicalSplit E I S L k family transverse coefficient i rest
    hp = resolvedAtom (plusFamily E I S k family) coefficient i j
    hm = resolvedAtom (minusFamily E I S k family) coefficient i j
    tp = resolvedRow (plusFamily E I S k family) coefficient i rest
    tm = resolvedRow (minusFamily E I S k family) coefficient i rest
  in
  trans (cong₂ _+_ head tail) (solve (hp ∷ hm ∷ tp ∷ tm ∷ []))

resolvedQuadraticFromHelicalSplit :
  ∀ {Index}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (family : CauchyResolvedCellFamily Index)
    (transverse : AllIndexedTransverse E k family)
    (coefficient : Index → ℚ)
    (is : List Index) →
  resolvedQuadraticFrom family coefficient is
  ≡ resolvedQuadraticFrom (plusFamily E I S k family) coefficient is
      + resolvedQuadraticFrom (minusFamily E I S k family) coefficient is
resolvedQuadraticFromHelicalSplit E I S L k family transverse coefficient [] = solve []
resolvedQuadraticFromHelicalSplit E I S L k family transverse coefficient (i ∷ rest) =
  let
    head = resolvedRowHelicalSplit E I S L k family transverse coefficient i (indices family)
    tail = resolvedQuadraticFromHelicalSplit E I S L k family transverse coefficient rest
    hp = resolvedRow (plusFamily E I S k family) coefficient i (indices family)
    hm = resolvedRow (minusFamily E I S k family) coefficient i (indices family)
    tp = resolvedQuadraticFrom (plusFamily E I S k family) coefficient rest
    tm = resolvedQuadraticFrom (minusFamily E I S k family) coefficient rest
  in
  trans (cong₂ _+_ head tail) (solve (hp ∷ hm ∷ tp ∷ tm ∷ []))

resolvedQuadraticHelicalSplit :
  ∀ {Index}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (family : CauchyResolvedCellFamily Index)
    (transverse : AllIndexedTransverse E k family)
    (coefficient : Index → ℚ) →
  resolvedQuadratic family coefficient
  ≡ resolvedQuadratic (plusFamily E I S k family) coefficient
      + resolvedQuadratic (minusFamily E I S k family) coefficient
resolvedQuadraticHelicalSplit E I S L k family transverse coefficient =
  resolvedQuadraticFromHelicalSplit
    E I S L k family transverse coefficient (indices family)

coefficientMassFromHelicalSplit :
  ∀ {Index}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (family : CauchyResolvedCellFamily Index)
    (transverse : AllIndexedTransverse E k family)
    (coefficient : Index → ℚ)
    (is : List Index) →
  coefficientMassFrom family coefficient is
  ≡ coefficientMassFrom (plusFamily E I S k family) coefficient is
      + coefficientMassFrom (minusFamily E I S k family) coefficient is
coefficientMassFromHelicalSplit E I S L k family transverse coefficient [] = solve []
coefficientMassFromHelicalSplit E I S L k family transverse coefficient (i ∷ rest) =
  let
    c2 = coefficient i * coefficient i
    normSplit = R475.l2NormHelicalSplit
      E I S L k (cell family i) (cellTransverse transverse i)

    head :
      coefficientMassAtom family coefficient i
      ≡ coefficientMassAtom (plusFamily E I S k family) coefficient i
        + coefficientMassAtom (minusFamily E I S k family) coefficient i
    head =
      trans
        (cong (c2 *_) normSplit)
        (solve
          (c2
            ∷ L2.complex3NormSquared
                (Helical.helicalProjectorPlus E I S k (cell family i))
            ∷ L2.complex3NormSquared
                (Helical.helicalProjectorMinus E I S k (cell family i)) ∷ []))

    tail = coefficientMassFromHelicalSplit
      E I S L k family transverse coefficient rest
    hp = coefficientMassAtom (plusFamily E I S k family) coefficient i
    hm = coefficientMassAtom (minusFamily E I S k family) coefficient i
    tp = coefficientMassFrom (plusFamily E I S k family) coefficient rest
    tm = coefficientMassFrom (minusFamily E I S k family) coefficient rest
  in
  trans (cong₂ _+_ head tail) (solve (hp ∷ hm ∷ tp ∷ tm ∷ []))

coefficientMassHelicalSplit :
  ∀ {Index}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (family : CauchyResolvedCellFamily Index)
    (transverse : AllIndexedTransverse E k family)
    (coefficient : Index → ℚ) →
  coefficientMass family coefficient
  ≡ coefficientMass (plusFamily E I S k family) coefficient
      + coefficientMass (minusFamily E I S k family) coefficient
coefficientMassHelicalSplit E I S L k family transverse coefficient =
  coefficientMassFromHelicalSplit
    E I S L k family transverse coefficient (indices family)

resolvedPhysicalHelicalSplit :
  ∀ {Index}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (family : CauchyResolvedCellFamily Index)
    (transverse : AllIndexedTransverse E k family) →
  R471.TwoPolarizationSplit
    (Index → ℚ)
    (resolvedQuadratic family)
    (resolvedQuadratic (plusFamily E I S k family))
    (resolvedQuadratic (minusFamily E I S k family))
    (coefficientMass family)
    (coefficientMass (plusFamily E I S k family))
    (coefficientMass (minusFamily E I S k family))
resolvedPhysicalHelicalSplit E I S L k family transverse = record
  { R471.gramSplit = resolvedQuadraticHelicalSplit E I S L k family transverse
  ; R471.massSplit = coefficientMassHelicalSplit E I S L k family transverse
  }

scalarResolvedBoundsCompile :
  ∀ {Index}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (family : CauchyResolvedCellFamily Index)
    (transverse : AllIndexedTransverse E k family)
    (A : ℚ) →
  ResolvedGramOperatorBound (plusFamily E I S k family) A →
  ResolvedGramOperatorBound (minusFamily E I S k family) A →
  ResolvedGramOperatorBound family A
scalarResolvedBoundsCompile E I S L k family transverse A plusBound minusBound =
  R471.twoPolarizationBoundsCompile
    (resolvedPhysicalHelicalSplit E I S L k family transverse)
    plusBound minusBound

round477CauchyPairKernelExplicit : Bool
round477CauchyPairKernelExplicit = true

round477ResolventNormalizationDivisionFree : Bool
round477ResolventNormalizationDivisionFree = true

round477ResolvedHelicalGramSplitClosed : Bool
round477ResolvedHelicalGramSplitClosed = true

round477ResolvedConcreteMassSplitClosed : Bool
round477ResolvedConcreteMassSplitClosed = true

round477TwoScalarResolvedBoundsCompile : Bool
round477TwoScalarResolvedBoundsCompile = true

round477PhysicalPlusResolvedBoundClosed : Bool
round477PhysicalPlusResolvedBoundClosed = false

round477PhysicalMinusResolvedBoundClosed : Bool
round477PhysicalMinusResolvedBoundClosed = false

round477PackageAClosed : Bool
round477PackageAClosed = false

round477ClayPromotion : Bool
round477ClayPromotion = false

round477PhysicalPlusResolvedBoundClosedIsFalse :
  round477PhysicalPlusResolvedBoundClosed ≡ false
round477PhysicalPlusResolvedBoundClosedIsFalse = refl

round477PhysicalMinusResolvedBoundClosedIsFalse :
  round477PhysicalMinusResolvedBoundClosed ≡ false
round477PhysicalMinusResolvedBoundClosedIsFalse = refl
