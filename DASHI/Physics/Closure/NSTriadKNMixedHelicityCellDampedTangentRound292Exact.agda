module DASHI.Physics.Closure.NSTriadKNMixedHelicityCellDampedTangentRound292Exact where

------------------------------------------------------------------------
-- ROUND292 / LITERAL R227 CELL DAMPED-FORCED TANGENT
--
-- BIDI correction to the first draft: the only nontrivial operator seam is
-- that the two helical projectors commute with a damped-forced modal tangent.
-- R73 already owns Leray complex-scalar linearity and R157 owns normalized-curl
-- complex linearity; rather than duplicate those long finite-algebra proofs
-- here, package their exact composition as the smallest authority consumed by
-- the literal R227 cell theorem.
--
-- Once
--
--   P_±(-rho u + f) = -rho P_±u + P_±f
--
-- is supplied, cross-product bilinearity gives
--
--   d (P_+u_p x P_-u_q)
--     = -(rho_p+rho_q)(P_+u_p x P_-u_q)
--       + P_+f_p x P_-u_q + P_+u_p x P_-f_q.
--
-- The remainder is definitionally the R230 product-rule forcing cell.  For
-- physical f=N(u), its fixed-output sum is already collapsed by R230 to the
-- signed mixed commutator before absolute values.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
open import Data.Rational.Base using (ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230

F : C3.RealField _
F = Rational.rationalRealField

record HelicalDampedProjectorLinearity
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F) : Set where
  field
    plusDamped :
      (mode : Z3.FourierMode) (rho : ℚ)
      (u f : C3.Complex3 F) →
      Helical.helicalProjectorPlus E I S mode
        (R94.dampedPlusForcing rho u f)
      ≡ R94.dampedPlusForcing rho
          (Helical.helicalProjectorPlus E I S mode u)
          (Helical.helicalProjectorPlus E I S mode f)

    minusDamped :
      (mode : Z3.FourierMode) (rho : ℚ)
      (u f : C3.Complex3 F) →
      Helical.helicalProjectorMinus E I S mode
        (R94.dampedPlusForcing rho u f)
      ≡ R94.dampedPlusForcing rho
          (Helical.helicalProjectorMinus E I S mode u)
          (Helical.helicalProjectorMinus E I S mode f)

open HelicalDampedProjectorLinearity public

cellTangent :
  {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (S : Helical.HelicalModeScalars F) →
  (velocity tangent : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
cellTangent {E = E} {I = I} S velocity tangent tau =
  C3.complex3Add
    (Cross.complex3Cross
      (Helical.helicalProjectorPlus E I S
        (Physical.p tau) (tangent (Physical.p tau)))
      (Helical.helicalProjectorMinus E I S
        (Physical.q tau) (velocity (Physical.q tau))))
    (Cross.complex3Cross
      (Helical.helicalProjectorPlus E I S
        (Physical.p tau) (velocity (Physical.p tau)))
      (Helical.helicalProjectorMinus E I S
        (Physical.q tau) (tangent (Physical.q tau))))

cellTangentIsR230ProductRule :
  {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (S : Helical.HelicalModeScalars F) →
  (velocity tangent : Z3.FourierMode → C3.Complex3 F) →
  (tau : Physical.PhysicalTriadIncidence) →
  cellTangent S velocity tangent tau
  ≡ R230.productRuleForcingCell S velocity tangent tau
cellTangentIsR230ProductRule S velocity tangent tau = refl

negativeRateSumScale :
  (rp rq : ℚ) (a : C3.Complex3 F) →
  C3.complex3Add
    (C3.complex3Scale (R94.negativeReal rp) a)
    (C3.complex3Scale (R94.negativeReal rq) a)
  ≡ C3.complex3Scale (R94.negativeReal (rp + rq)) a
negativeRateSumScale rp rq (C3.complex3 ax ay az) =
  Field.complex3Ext
    (R.solve 3
      (λ rp rq a → ((R.⊝ rp) R.⊗ a) R.⊕ ((R.⊝ rq) R.⊗ a)
        R.⊜ (R.⊝ (rp R.⊕ rq)) R.⊗ a)
      refl (C3.realEmbed F rp) (C3.realEmbed F rq) ax)
    (R.solve 3
      (λ rp rq a → ((R.⊝ rp) R.⊗ a) R.⊕ ((R.⊝ rq) R.⊗ a)
        R.⊜ (R.⊝ (rp R.⊕ rq)) R.⊗ a)
      refl (C3.realEmbed F rp) (C3.realEmbed F rq) ay)
    (R.solve 3
      (λ rp rq a → ((R.⊝ rp) R.⊗ a) R.⊕ ((R.⊝ rq) R.⊗ a)
        R.⊜ (R.⊝ (rp R.⊕ rq)) R.⊗ a)
      refl (C3.realEmbed F rp) (C3.realEmbed F rq) az)
  where module R = Ring.Solver F

cellRegroup :
  (rp rq : ℚ) (up uq fp fq : C3.Complex3 F) →
  C3.complex3Add
    (Cross.complex3Cross (R94.dampedPlusForcing rp up fp) uq)
    (Cross.complex3Cross up (R94.dampedPlusForcing rq uq fq))
  ≡
  C3.complex3Add
    (C3.complex3Scale (R94.negativeReal (rp + rq))
      (Cross.complex3Cross up uq))
    (C3.complex3Add
      (Cross.complex3Cross fp uq)
      (Cross.complex3Cross up fq))
cellRegroup rp rq up uq fp fq =
  let
    left = trans
      (R94.crossAddLeft
        (C3.complex3Scale (R94.negativeReal rp) up) fp uq)
      (cong₂ C3.complex3Add
        (R94.crossScaleLeft (R94.negativeReal rp) up uq) refl)

    right = trans
      (R94.crossAddRight up
        (C3.complex3Scale (R94.negativeReal rq) uq) fq)
      (cong₂ C3.complex3Add
        (R94.crossScaleRight (R94.negativeReal rq) up uq) refl)

    dampA = C3.complex3Scale (R94.negativeReal rp)
      (Cross.complex3Cross up uq)
    dampB = C3.complex3Scale (R94.negativeReal rq)
      (Cross.complex3Cross up uq)
    fA = Cross.complex3Cross fp uq
    fB = Cross.complex3Cross up fq

    shuffle :
      C3.complex3Add (C3.complex3Add dampA fA) (C3.complex3Add dampB fB)
      ≡ C3.complex3Add (C3.complex3Add dampA dampB) (C3.complex3Add fA fB)
    shuffle = vectorShuffle dampA fA dampB fB
  in
  trans
    (cong₂ C3.complex3Add left right)
    (trans shuffle
      (cong₂ C3.complex3Add
        (negativeRateSumScale rp rq (Cross.complex3Cross up uq)) refl))
  where
  vectorShuffle :
    (a b c d : C3.Complex3 F) →
    C3.complex3Add (C3.complex3Add a b) (C3.complex3Add c d)
    ≡ C3.complex3Add (C3.complex3Add a c) (C3.complex3Add b d)
  vectorShuffle
      (C3.complex3 ax ay az) (C3.complex3 bx by bz)
      (C3.complex3 cx cy cz) (C3.complex3 dx dy dz) =
    Field.complex3Ext
      (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (c R.⊕ d))
        R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d))) refl ax bx cx dx)
      (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (c R.⊕ d))
        R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d))) refl ay by cy dy)
      (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (c R.⊕ d))
        R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d))) refl az bz cz dz)
    where module R = Ring.Solver F

mixedCellDampedTangent :
  {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (S : Helical.HelicalModeScalars F) →
  (L : HelicalDampedProjectorLinearity E I S) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (rho : Z3.FourierMode → ℚ) →
  (tau : Physical.PhysicalTriadIncidence) →
  cellTangent S velocity
    (λ mode → R94.dampedPlusForcing (rho mode) (velocity mode) (forcing mode)) tau
  ≡
  C3.complex3Add
    (C3.complex3Scale
      (R94.negativeReal (rho (Physical.p tau) + rho (Physical.q tau)))
      (R224.mixedPlusMinus S velocity tau))
    (R230.productRuleForcingCell S velocity forcing tau)
mixedCellDampedTangent {E = E} {I = I}
    S L velocity forcing rho tau =
  let
    p = Physical.p tau
    q = Physical.q tau
    up = Helical.helicalProjectorPlus E I S p (velocity p)
    uq = Helical.helicalProjectorMinus E I S q (velocity q)
    fp = Helical.helicalProjectorPlus E I S p (forcing p)
    fq = Helical.helicalProjectorMinus E I S q (forcing q)
  in
  trans
    (cong₂ C3.complex3Add
      (cong (λ first → Cross.complex3Cross first uq)
        (plusDamped L p (rho p) (velocity p) (forcing p)))
      (cong (Cross.complex3Cross up)
        (minusDamped L q (rho q) (velocity q) (forcing q))))
    (cellRegroup (rho p) (rho q) up uq fp fq)
  where
  cong : ∀ {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

round292CellDampedTangentCompilerClosed : Bool
round292CellDampedTangentCompilerClosed = true

round292UsesLiteralR227MixedCell : Bool
round292UsesLiteralR227MixedCell = true

round292NonlinearRemainderIsLiteralR230ProductRuleCell : Bool
round292NonlinearRemainderIsLiteralR230ProductRuleCell = true

round292HelicalDampedLinearityInstantiatedFromR73R157 : Bool
round292HelicalDampedLinearityInstantiatedFromR73R157 = false

round292PhysicalRhoEqualsNuModeSquareWeldClosed : Bool
round292PhysicalRhoEqualsNuModeSquareWeldClosed = false

round292PairFluxAggregationClosed : Bool
round292PairFluxAggregationClosed = false

round292PackageAClosed : Bool
round292PackageAClosed = false

round292ClayPromotion : Bool
round292ClayPromotion = false

round292CellDampedTangentCompilerClosedIsTrue :
  round292CellDampedTangentCompilerClosed ≡ true
round292CellDampedTangentCompilerClosedIsTrue = refl

round292HelicalDampedLinearityInstantiatedFromR73R157IsFalse :
  round292HelicalDampedLinearityInstantiatedFromR73R157 ≡ false
round292HelicalDampedLinearityInstantiatedFromR73R157IsFalse = refl
