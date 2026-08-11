module DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- DASHI CONTRIBUTION
--
-- The selected-background residual has already been proved to contract in a
-- finite l1 norm.  The inverse estimate needed next does not require taking a
-- Neumann-series limit in Q.  For any finite vector equation
--
--      x + R x = y
--
-- with
--
--      ||R x||_1 <= q ||x||_1,
--
-- finite triangle algebra gives
--
--      (1-q) ||x||_1 <= ||y||_1.
--
-- At q=1/6 this gives the exact rational reopening bound
--
--      ||x||_1 <= (6/5) ||y||_1.
--
-- In particular the homogeneous equation has zero l1 norm.  A proof-bearing
-- finite selector then turns zero l1 norm into pointwise zero, so strict
-- contraction supplies genuine kernel triviality on a complete finite carrier.
-- This is the hard quantitative part of finite reopening and uses neither a
-- completeness assumption nor an infinite sum.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as Mass

Vector : Set → Set
Vector Index = Index → ℚ

vectorDifference : ∀ {Index : Set} → Vector Index → Vector Index → Vector Index
vectorDifference left right index = left index - right index

vectorL1DifferenceUpper :
  ∀ {Index : Set} (indices : List Index) left right →
  L1.vectorL1 indices (vectorDifference left right)
  ≤ L1.vectorL1 indices left + L1.vectorL1 indices right
vectorL1DifferenceUpper indices left right =
  let
    pointwise = Schur.sumPointwiseBelow indices _ _
      (λ index → ℚP.∣p-q∣≤∣p∣+∣q∣ (left index) (right index))

    sumExact :
      Sums.sumRational indices
        (λ index → ∣ left index ∣ + ∣ right index ∣)
      ≡ L1.vectorL1 indices left + L1.vectorL1 indices right
    sumExact = Mass.sumAddExact indices
      (λ index → ∣ left index ∣)
      (λ index → ∣ right index ∣)
  in
  subst
    (λ upper →
      L1.vectorL1 indices (vectorDifference left right) ≤ upper)
    sumExact pointwise

IdentityPlusResidualEquation :
  ∀ {Index : Set} →
  (Vector Index → Vector Index) → Vector Index → Vector Index → Set
IdentityPlusResidualEquation residual solution source =
  ∀ row → solution row + residual solution row ≡ source row

solutionEqualsSourceMinusResidual :
  ∀ {Index : Set}
    (residual : Vector Index → Vector Index)
    solution source →
  IdentityPlusResidualEquation residual solution source →
  ∀ row → solution row ≡ source row - residual solution row
solutionEqualsSourceMinusResidual residual solution source equation row =
  let
    x = solution row
    r = residual solution row
    y = source row
  in
  trans
    (sym (ℚRing.solve-∀ x r : (x + r) - r ≡ x))
    (cong (_- r) (equation row))

solutionL1ReopeningUpper :
  ∀ {Index : Set}
    (indices : List Index)
    (residual : Vector Index → Vector Index)
    solution source →
  IdentityPlusResidualEquation residual solution source →
  L1.vectorL1 indices solution
  ≤ L1.vectorL1 indices source
      + L1.vectorL1 indices (residual solution)
solutionL1ReopeningUpper indices residual solution source equation =
  let
    pointwise = solutionEqualsSourceMinusResidual
      residual solution source equation

    exact :
      L1.vectorL1 indices solution
      ≡ L1.vectorL1 indices
          (vectorDifference source (residual solution))
    exact = Sums.sumRationalCong indices _ _
      (λ row → cong ∣_∣ (pointwise row))
  in
  subst
    (λ lower →
      lower ≤ L1.vectorL1 indices source
        + L1.vectorL1 indices (residual solution))
    (sym exact)
    (vectorL1DifferenceUpper indices source (residual solution))

reopeningGapBound : ∀ solutionNorm sourceNorm q →
  solutionNorm ≤ sourceNorm + q * solutionNorm →
  (1ℚ - q) * solutionNorm ≤ sourceNorm
reopeningGapBound solutionNorm sourceNorm q upper =
  let
    shifted :
      solutionNorm + - (q * solutionNorm)
      ≤ (sourceNorm + q * solutionNorm) + - (q * solutionNorm)
    shifted = ℚP.+-monoˡ-≤ (- (q * solutionNorm)) upper

    leftExact :
      solutionNorm + - (q * solutionNorm)
      ≡ (1ℚ - q) * solutionNorm
    leftExact = ℚRing.solve-∀ solutionNorm q

    rightExact :
      (sourceNorm + q * solutionNorm) + - (q * solutionNorm)
      ≡ sourceNorm
    rightExact = ℚRing.solve-∀ sourceNorm solutionNorm q
  in
  subst
    (λ left → left ≤ sourceNorm)
    leftExact
    (subst
      (λ right →
        solutionNorm + - (q * solutionNorm) ≤ right)
      rightExact shifted)

oneSixth sixFifths fiveSixths : ℚ
oneSixth = + 1 / 6
sixFifths = + 6 / 5
fiveSixths = + 5 / 6

oneSixthGapExact : 1ℚ - oneSixth ≡ fiveSixths
oneSixthGapExact = ℚRing.solve []

sixFifthsFiveSixthsExact :
  sixFifths * fiveSixths ≡ 1ℚ
sixFifthsFiveSixthsExact = ℚRing.solve []

oneSixthReopeningBound :
  ∀ {Index : Set}
    (indices : List Index)
    (residual : Vector Index → Vector Index)
    solution source →
  IdentityPlusResidualEquation residual solution source →
  L1.vectorL1 indices (residual solution)
    ≤ oneSixth * L1.vectorL1 indices solution →
  L1.vectorL1 indices solution
    ≤ sixFifths * L1.vectorL1 indices source
oneSixthReopeningBound
    indices residual solution source equation residualContraction =
  let
    xNorm = L1.vectorL1 indices solution
    yNorm = L1.vectorL1 indices source
    rNorm = L1.vectorL1 indices (residual solution)

    triangle : xNorm ≤ yNorm + rNorm
    triangle = solutionL1ReopeningUpper
      indices residual solution source equation

    replaceResidual : yNorm + rNorm ≤ yNorm + oneSixth * xNorm
    replaceResidual = ℚP.+-monoʳ-≤ yNorm residualContraction

    beforeGap : xNorm ≤ yNorm + oneSixth * xNorm
    beforeGap = ℚP.≤-trans triangle replaceResidual

    gapRaw : (1ℚ - oneSixth) * xNorm ≤ yNorm
    gapRaw = reopeningGapBound xNorm yNorm oneSixth beforeGap

    gap : fiveSixths * xNorm ≤ yNorm
    gap = subst
      (λ lower → lower ≤ yNorm)
      (cong (_* xNorm) oneSixthGapExact)
      gapRaw

    scaled :
      sixFifths * (fiveSixths * xNorm)
      ≤ sixFifths * yNorm
    scaled = Norm.scaleNonnegative sixFifths
      (ℚP.nonNegative⁻¹ sixFifths) gap

    leftExact :
      sixFifths * (fiveSixths * xNorm) ≡ xNorm
    leftExact =
      trans
        (sym (ℚP.*-assoc sixFifths fiveSixths xNorm))
        (trans
          (cong (_* xNorm) sixFifthsFiveSixthsExact)
          (ℚP.*-identityˡ xNorm))
  in
  subst
    (λ lower → lower ≤ sixFifths * yNorm)
    leftExact scaled

zeroVector : ∀ {Index : Set} → Vector Index
zeroVector _ = 0ℚ

zeroVectorL1Exact :
  ∀ {Index : Set} (indices : List Index) →
  L1.vectorL1 indices zeroVector ≡ 0ℚ
zeroVectorL1Exact indices =
  trans
    (Sums.sumRationalCong indices
      (λ _ → ∣ 0ℚ ∣) (λ _ → 0ℚ) (λ _ → refl))
    (sumZero indices)
  where
    sumZero : ∀ {A : Set} (values : List A) →
      Sums.sumRational values (λ _ → 0ℚ) ≡ 0ℚ
    sumZero [] = refl
    sumZero (_ ∷ values)
      rewrite sumZero values = refl

vectorL1Nonnegative :
  ∀ {Index : Set} (indices : List Index) vector →
  0ℚ ≤ L1.vectorL1 indices vector
vectorL1Nonnegative indices vector =
  Schur.sumNonnegative indices (λ index → ∣ vector index ∣)
    (λ index → ℚP.0≤∣p∣ (vector index))

selectorFactorBelowAbsolute :
  ∀ {Index : Set}
    (selector : Basis.FiniteSelector Index)
    (vector : Vector Index) target candidate →
  ∣ vector candidate ∣
    * Basis.kronecker (Basis.decide selector) candidate target
  ≤ ∣ vector candidate ∣
selectorFactorBelowAbsolute selector vector target candidate
  with Basis.decide selector candidate target
... | yes refl =
  subst
    (λ left → left ≤ ∣ vector target ∣)
    (ℚRing.solve-∀ (∣ vector target ∣) :
      ∣ vector target ∣ * 1ℚ ≡ ∣ vector target ∣)
    ℚP.≤-refl
... | no _ =
  subst
    (λ left → left ≤ ∣ vector candidate ∣)
    (ℚRing.solve-∀ (∣ vector candidate ∣) :
      ∣ vector candidate ∣ * 0ℚ ≡ 0ℚ)
    (ℚP.0≤∣p∣ (vector candidate))

finiteSelectorCoordinateBelowL1 :
  ∀ {Index : Set}
    (selector : Basis.FiniteSelector Index)
    (vector : Vector Index) target →
  ∣ vector target ∣
  ≤ L1.vectorL1 (Basis.elements selector) vector
finiteSelectorCoordinateBelowL1 selector vector target =
  let
    selected :
      Sums.sumRational (Basis.elements selector)
        (λ candidate →
          ∣ vector candidate ∣
          * Basis.kronecker (Basis.decide selector) candidate target)
      ≤ Sums.sumRational (Basis.elements selector)
          (λ candidate → ∣ vector candidate ∣)
    selected = Schur.sumPointwiseBelow
      (Basis.elements selector) _ _
      (selectorFactorBelowAbsolute selector vector target)

    exact :
      Sums.sumRational (Basis.elements selector)
        (λ candidate →
          ∣ vector candidate ∣
          * Basis.kronecker (Basis.decide selector) candidate target)
      ≡ ∣ vector target ∣
    exact = Basis.selectorExact selector (λ candidate → ∣ vector candidate ∣) target
  in
  subst
    (λ lower → lower ≤ L1.vectorL1 (Basis.elements selector) vector)
    exact selected

finiteSelectorL1ZeroPointwise :
  ∀ {Index : Set}
    (selector : Basis.FiniteSelector Index)
    (vector : Vector Index) →
  L1.vectorL1 (Basis.elements selector) vector ≡ 0ℚ →
  ∀ target → vector target ≡ 0ℚ
finiteSelectorL1ZeroPointwise selector vector normZero target =
  let
    absoluteBelowNorm = finiteSelectorCoordinateBelowL1 selector vector target

    absoluteBelowZero : ∣ vector target ∣ ≤ 0ℚ
    absoluteBelowZero = subst
      (λ upper → ∣ vector target ∣ ≤ upper)
      normZero absoluteBelowNorm

    absoluteZero : ∣ vector target ∣ ≡ 0ℚ
    absoluteZero = ℚP.≤-antisym
      absoluteBelowZero (ℚP.0≤∣p∣ (vector target))
  in
  ℚP.∣p∣≡0⇒p≡0 (vector target) absoluteZero

oneSixthHomogeneousReopeningZeroNorm :
  ∀ {Index : Set}
    (indices : List Index)
    (residual : Vector Index → Vector Index)
    solution →
  IdentityPlusResidualEquation residual solution zeroVector →
  L1.vectorL1 indices (residual solution)
    ≤ oneSixth * L1.vectorL1 indices solution →
  L1.vectorL1 indices solution ≡ 0ℚ
oneSixthHomogeneousReopeningZeroNorm
    indices residual solution equation residualContraction =
  let
    upper :
      L1.vectorL1 indices solution
      ≤ sixFifths * L1.vectorL1 indices zeroVector
    upper = oneSixthReopeningBound
      indices residual solution zeroVector equation residualContraction

    upperZero : L1.vectorL1 indices solution ≤ 0ℚ
    upperZero = subst
      (λ right → L1.vectorL1 indices solution ≤ right)
      (trans
        (cong (sixFifths *_) (zeroVectorL1Exact indices))
        (ℚRing.solve [] : sixFifths * 0ℚ ≡ 0ℚ))
      upper
  in
  ℚP.≤-antisym upperZero (vectorL1Nonnegative indices solution)

oneSixthHomogeneousReopeningPointwiseZero :
  ∀ {Index : Set}
    (selector : Basis.FiniteSelector Index)
    (residual : Vector Index → Vector Index)
    solution →
  IdentityPlusResidualEquation residual solution zeroVector →
  L1.vectorL1 (Basis.elements selector) (residual solution)
    ≤ oneSixth * L1.vectorL1 (Basis.elements selector) solution →
  ∀ target → solution target ≡ 0ℚ
oneSixthHomogeneousReopeningPointwiseZero
    selector residual solution equation residualContraction =
  finiteSelectorL1ZeroPointwise selector solution
    (oneSixthHomogeneousReopeningZeroNorm
      (Basis.elements selector) residual solution equation residualContraction)

finiteStrictContractionReopeningLevel : ProofLevel
finiteStrictContractionReopeningLevel = machineChecked

finiteOneSixthReopeningSixFifthsLevel : ProofLevel
finiteOneSixthReopeningSixFifthsLevel = machineChecked

finiteSelectorL1DefinitenessLevel : ProofLevel
finiteSelectorL1DefinitenessLevel = machineChecked
