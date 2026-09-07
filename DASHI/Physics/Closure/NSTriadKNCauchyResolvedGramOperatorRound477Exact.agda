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
-- This owner therefore puts that pair kernel into the quadratic form explicitly.
-- The normalization is carried only through the division-free receipt
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
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287
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

resolvedQuadratic :
  ∀ {Index} →
  CauchyResolvedCellFamily Index →
  (Index → ℚ) → ℚ
resolvedQuadratic family coefficient =
  go (indices family)
  where
  go : List _ → ℚ
  go [] = 0ℚ
  go (i ∷ rest) =
    resolvedRow family coefficient i (indices family) + go rest

coefficientMassAtom :
  ∀ {Index} →
  CauchyResolvedCellFamily Index →
  (Index → ℚ) → Index → ℚ
coefficientMassAtom family coefficient i =
  (coefficient i * coefficient i) * L2.complex3NormSquared (cell family i)

coefficientMass :
  ∀ {Index} →
  CauchyResolvedCellFamily Index →
  (Index → ℚ) → ℚ
coefficientMass family coefficient = go (indices family)
  where
  go : List _ → ℚ
  go [] = 0ℚ
  go (i ∷ rest) = coefficientMassAtom family coefficient i + go rest

ResolvedGramOperatorBound :
  ∀ {Index} → CauchyResolvedCellFamily Index → ℚ → Set
ResolvedGramOperatorBound family A =
  R471.GramOperatorBound
    (_ → ℚ)
    (resolvedQuadratic family)
    (coefficientMass family)
    A

------------------------------------------------------------------------
-- Helical component families at one fixed output.
------------------------------------------------------------------------

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

    uSplit = Helical.velocityHelicalDecomposition L k u (cellTransverse transverse i)
    vSplit = Helical.velocityHelicalDecomposition L k v (cellTransverse transverse j)

    expanded :
      R179.realHermitianCross u v
      ≡ R179.realHermitianCross up vp + R179.realHermitianCross um vm
    expanded =
      trans
        (cong₂ R179.realHermitianCross (sym uSplit) (sym vSplit))
        (trans
          (R291Like up um vp vm)
          (mixedVanish up um vp vm))

    scalar = coefficient i * coefficient j
    w = resolventWeight family i j
  in
  trans
    (cong (λ cross → scalar * (w * cross)) expanded)
    (solve
      (scalar ∷ w
        ∷ R179.realHermitianCross up vp
        ∷ R179.realHermitianCross um vm ∷ []))
  where
  R291Like :
    (up um vp vm : C3.Complex3 F) →
    R179.realHermitianCross (C3.complex3Add up um) (C3.complex3Add vp vm)
    ≡
    (R179.realHermitianCross up vp + R179.realHermitianCross up vm)
      + (R179.realHermitianCross um vp + R179.realHermitianCross um vm)
  R291Like up um vp vm =
    trans
      (R291.realCrossAddLeft up um (C3.complex3Add vp vm))
      (cong₂ _+_
        (R291.realCrossAddRight up vp vm)
        (R291.realCrossAddRight um vp vm))

  mixedVanish :
    (up um vp vm : C3.Complex3 F) →
    (R179.realHermitianCross up vp + R179.realHermitianCross up vm)
      + (R179.realHermitianCross um vp + R179.realHermitianCross um vm)
    ≡ R179.realHermitianCross up vp + R179.realHermitianCross um vm
  mixedVanish up um vp vm
    rewrite R287.outputPlusMinusRealGramZero E I S L k (cell family i) (cell family j)
          | R287.outputMinusPlusRealGramZero E I S L k (cell family i) (cell family j) =
    solve
      (R179.realHermitianCross up vp
        ∷ R179.realHermitianCross um vm ∷ [])

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
  go (indices family)
  where
  go : (is : List _) →
    localQuadratic family coefficient is
    ≡ localQuadratic (plusFamily E I S k family) coefficient is
      + localQuadratic (minusFamily E I S k family) coefficient is
  go [] = solve []
  go (i ∷ rest) =
    let
      head = resolvedRowHelicalSplit E I S L k family transverse coefficient i (indices family)
      tail = go rest
      hp = resolvedRow (plusFamily E I S k family) coefficient i (indices family)
      hm = resolvedRow (minusFamily E I S k family) coefficient i (indices family)
      tp = localQuadratic (plusFamily E I S k family) coefficient rest
      tm = localQuadratic (minusFamily E I S k family) coefficient rest
    in
    trans (cong₂ _+_ head tail) (solve (hp ∷ hm ∷ tp ∷ tm ∷ []))

  localQuadratic :
    CauchyResolvedCellFamily Index → (Index → ℚ) → List Index → ℚ
  localQuadratic fam c [] = 0ℚ
  localQuadratic fam c (i ∷ rest) =
    resolvedRow fam c i (indices fam) + localQuadratic fam c rest

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
  go (indices family)
  where
  localMass : CauchyResolvedCellFamily Index → (Index → ℚ) → List Index → ℚ
  localMass fam c [] = 0ℚ
  localMass fam c (i ∷ rest) =
    coefficientMassAtom fam c i + localMass fam c rest

  headSplit : (i : Index) →
    coefficientMassAtom family coefficient i
    ≡ coefficientMassAtom (plusFamily E I S k family) coefficient i
      + coefficientMassAtom (minusFamily E I S k family) coefficient i
  headSplit i =
    let
      c2 = coefficient i * coefficient i
      massSplit = R475.l2NormHelicalSplit
        E I S L k (cell family i) (cellTransverse transverse i)
    in
    trans
      (cong (c2 *_) massSplit)
      (solve
        (c2
          ∷ L2.complex3NormSquared
              (Helical.helicalProjectorPlus E I S k (cell family i))
          ∷ L2.complex3NormSquared
              (Helical.helicalProjectorMinus E I S k (cell family i)) ∷ []))

  go : (is : List Index) →
    localMass family coefficient is
    ≡ localMass (plusFamily E I S k family) coefficient is
      + localMass (minusFamily E I S k family) coefficient is
  go [] = solve []
  go (i ∷ rest) =
    let
      head = headSplit i
      tail = go rest
      hp = coefficientMassAtom (plusFamily E I S k family) coefficient i
      hm = coefficientMassAtom (minusFamily E I S k family) coefficient i
      tp = localMass (plusFamily E I S k family) coefficient rest
      tm = localMass (minusFamily E I S k family) coefficient rest
    in
    trans (cong₂ _+_ head tail) (solve (hp ∷ hm ∷ tp ∷ tm ∷ []))

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
