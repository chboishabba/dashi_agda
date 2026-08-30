module DASHI.Physics.Closure.NSTriadKNMixedHelicityCellDampedTangentRound292Exact where

------------------------------------------------------------------------
-- ROUND292 / LITERAL R227 CELL DAMPED-FORCED TANGENT
--
-- This closes the routine same-object seam left by R291.
--
-- For the literal R227 mixed-helicity cell
--
--   A_pq = P_+ u_p x P_- u_q,
--
-- let the two modal tangents be
--
--   du_p = -rho_p u_p + f_p,
--   du_q = -rho_q u_q + f_q.
--
-- Leray and normalized curl are complex-linear (R73/R157), hence both helical
-- projectors commute with these damped-forced decompositions.  Cross-product
-- bilinearity then gives the exact cell equation
--
--   dA_pq
--     = -(rho_p+rho_q) A_pq
--       + (P_+ f_p x P_- u_q + P_+ u_p x P_- f_q).
--
-- The remainder on the right is exactly R230's literal product-rule forcing
-- cell with `forcing=f`.  For physical f=N(u), summing it over a fixed output
-- fibre is already collapsed by R230 to the signed mixed commutator.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as R73
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact as R157
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230

------------------------------------------------------------------------
-- Routine Leray/helical additivity.
------------------------------------------------------------------------

complex3ScaleScalarAdd :
  ∀ {r} {F : C3.RealField r}
    (a b : C3.Complex F) (v : C3.Complex3 F) →
  C3.complex3Scale (C3.complexAdd a b) v
  ≡ C3.complex3Add (C3.complex3Scale a v) (C3.complex3Scale b v)
complex3ScaleScalarAdd {F = F} a b (C3.complex3 x y z) =
  Field.complex3Ext
    (Algebra.complexMultiplyDistributesRight a b x)
    (Algebra.complexMultiplyDistributesRight a b y)
    (Algebra.complexMultiplyDistributesRight a b z)

lerayProjectAdd :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (mode : Z3.FourierMode)
    (u v : C3.Complex3 F) →
  C3.lerayProject3 E I mode (C3.complex3Add u v)
  ≡ C3.complex3Add
      (C3.lerayProject3 E I mode u)
      (C3.lerayProject3 E I mode v)
lerayProjectAdd {F = F} E I mode u v =
  let
    wave = C3.modeVector E mode
    inverse = C3.realEmbed F (C3.inverseNormSquared I mode)
    du = C3.bilinearDot3 wave u
    dv = C3.bilinearDot3 wave v

    dotAdd :
      C3.bilinearDot3 wave (C3.complex3Add u v)
      ≡ C3.complexAdd du dv
    dotAdd = Algebra.bilinearDot3RightAdd wave u v

    coefficientAdd :
      C3.complexMultiply inverse
        (C3.bilinearDot3 wave (C3.complex3Add u v))
      ≡ C3.complexAdd
          (C3.complexMultiply inverse du)
          (C3.complexMultiply inverse dv)
    coefficientAdd = trans
      (cong (C3.complexMultiply inverse) dotAdd)
      (Algebra.complexMultiplyDistributesLeft inverse du dv)

    correctionAdd :
      C3.complex3Scale
        (C3.complexMultiply inverse
          (C3.bilinearDot3 wave (C3.complex3Add u v))) wave
      ≡ C3.complex3Add
          (C3.complex3Scale (C3.complexMultiply inverse du) wave)
          (C3.complex3Scale (C3.complexMultiply inverse dv) wave)
    correctionAdd = trans
      (cong (λ scalar → C3.complex3Scale scalar wave) coefficientAdd)
      (complex3ScaleScalarAdd
        (C3.complexMultiply inverse du)
        (C3.complexMultiply inverse dv) wave)
  in
  trans
    (cong (C3.complex3Subtract (C3.complex3Add u v)) correctionAdd)
    (subtractAddInterchange u v
      (C3.complex3Scale (C3.complexMultiply inverse du) wave)
      (C3.complex3Scale (C3.complexMultiply inverse dv) wave))
  where
  subtractAddInterchange :
    ∀ (a b c d : C3.Complex3 F) →
    C3.complex3Subtract (C3.complex3Add a b) (C3.complex3Add c d)
    ≡ C3.complex3Add (C3.complex3Subtract a c) (C3.complex3Subtract b d)
  subtractAddInterchange
      (C3.complex3 ax ay az) (C3.complex3 bx by bz)
      (C3.complex3 cx cy cz) (C3.complex3 dx dy dz) =
    Field.complex3Ext
      (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (R.⊝ (c R.⊕ d))) R.⊜ ((a R.⊕ (R.⊝ c)) R.⊕ (b R.⊕ (R.⊝ d)))) refl ax bx cx dx)
      (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (R.⊝ (c R.⊕ d))) R.⊜ ((a R.⊕ (R.⊝ c)) R.⊕ (b R.⊕ (R.⊝ d)))) refl ay by cy dy)
      (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (R.⊝ (c R.⊕ d))) R.⊜ ((a R.⊕ (R.⊝ c)) R.⊕ (b R.⊕ (R.⊝ d)))) refl az bz cz dz)
    where module R = Ring.Solver F

helicalProjectorPlusAdd :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F) (mode : Z3.FourierMode)
    (u v : C3.Complex3 F) →
  Helical.helicalProjectorPlus E I S mode (C3.complex3Add u v)
  ≡ C3.complex3Add
      (Helical.helicalProjectorPlus E I S mode u)
      (Helical.helicalProjectorPlus E I S mode v)
helicalProjectorPlusAdd {F = F} E I S mode u v =
  let h = C3.realEmbed F (Helical.half S)
      pu = C3.lerayProject3 E I mode u
      pv = C3.lerayProject3 E I mode v
      hu = R142.normalizedCurl E S mode u
      hv = R142.normalizedCurl E S mode v
  in
  trans
    (cong (C3.complex3Scale h)
      (cong₂ C3.complex3Add
        (lerayProjectAdd E I mode u v)
        (R157.normalizedCurlAdd E S mode u v)))
    (trans
      (R73.complex3ScaleAdd h
        (C3.complex3Add pu pv) (C3.complex3Add hu hv))
      (regroup h pu pv hu hv))
  where
  regroup :
    ∀ (h : C3.Complex F) (pu pv hu hv : C3.Complex3 F) →
    C3.complex3Add
      (C3.complex3Scale h (C3.complex3Add pu pv))
      (C3.complex3Scale h (C3.complex3Add hu hv))
    ≡ C3.complex3Add
        (C3.complex3Scale h (C3.complex3Add pu hu))
        (C3.complex3Scale h (C3.complex3Add pv hv))
  regroup h pu pv hu hv =
    trans
      (cong₂ C3.complex3Add
        (R73.complex3ScaleAdd h pu pv)
        (R73.complex3ScaleAdd h hu hv))
      (shuffle
        (C3.complex3Scale h pu) (C3.complex3Scale h pv)
        (C3.complex3Scale h hu) (C3.complex3Scale h hv))
    where
    shuffle : ∀ (a b c d : C3.Complex3 F) →
      C3.complex3Add (C3.complex3Add a b) (C3.complex3Add c d)
      ≡ C3.complex3Add (C3.complex3Add a c) (C3.complex3Add b d)
    shuffle
        (C3.complex3 ax ay az) (C3.complex3 bx by bz)
        (C3.complex3 cx cy cz) (C3.complex3 dx dy dz) =
      Field.complex3Ext
        (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (c R.⊕ d)) R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d))) refl ax bx cx dx)
        (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (c R.⊕ d)) R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d))) refl ay by cy dy)
        (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (c R.⊕ d)) R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d))) refl az bz cz dz)
      where module R = Ring.Solver F

helicalProjectorMinusAdd :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F) (mode : Z3.FourierMode)
    (u v : C3.Complex3 F) →
  Helical.helicalProjectorMinus E I S mode (C3.complex3Add u v)
  ≡ C3.complex3Add
      (Helical.helicalProjectorMinus E I S mode u)
      (Helical.helicalProjectorMinus E I S mode v)
helicalProjectorMinusAdd {F = F} E I S mode u v =
  let h = C3.realEmbed F (Helical.half S)
      pu = C3.lerayProject3 E I mode u
      pv = C3.lerayProject3 E I mode v
      hu = R142.normalizedCurl E S mode u
      hv = R142.normalizedCurl E S mode v
  in
  -- Both the Leray and normalized-curl pieces are additive; coordinate ring
  -- normalization handles the subtraction/regrouping without a new law.
  trans
    (cong (C3.complex3Scale h)
      (cong₂ C3.complex3Subtract
        (lerayProjectAdd E I mode u v)
        (R157.normalizedCurlAdd E S mode u v)))
    (minusRegroup h pu pv hu hv)
  where
  minusRegroup :
    ∀ (h : C3.Complex F) (pu pv hu hv : C3.Complex3 F) →
    C3.complex3Scale h
      (C3.complex3Subtract (C3.complex3Add pu pv) (C3.complex3Add hu hv))
    ≡ C3.complex3Add
        (C3.complex3Scale h (C3.complex3Subtract pu hu))
        (C3.complex3Scale h (C3.complex3Subtract pv hv))
  minusRegroup h
      (C3.complex3 pux puy puz) (C3.complex3 pvx pvy pvz)
      (C3.complex3 hux huy huz) (C3.complex3 hvx hvy hvz) =
    Field.complex3Ext
      (R.solve 5 (λ h a b c d → h R.⊗ ((a R.⊕ b) R.⊕ (R.⊝ (c R.⊕ d))) R.⊜ (h R.⊗ (a R.⊕ (R.⊝ c))) R.⊕ (h R.⊗ (b R.⊕ (R.⊝ d)))) refl h pux pvx hux hvx)
      (R.solve 5 (λ h a b c d → h R.⊗ ((a R.⊕ b) R.⊕ (R.⊝ (c R.⊕ d))) R.⊜ (h R.⊗ (a R.⊕ (R.⊝ c))) R.⊕ (h R.⊗ (b R.⊕ (R.⊝ d)))) refl h puy pvy huy hvy)
      (R.solve 5 (λ h a b c d → h R.⊗ ((a R.⊕ b) R.⊕ (R.⊝ (c R.⊕ d))) R.⊜ (h R.⊗ (a R.⊕ (R.⊝ c))) R.⊕ (h R.⊗ (b R.⊕ (R.⊝ d)))) refl h puz pvz huz hvz)
    where module R = Ring.Solver F

helicalProjectorPlusScale :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F) (mode : Z3.FourierMode)
    (scalar : C3.Complex F) (u : C3.Complex3 F) →
  Helical.helicalProjectorPlus E I S mode (C3.complex3Scale scalar u)
  ≡ C3.complex3Scale scalar (Helical.helicalProjectorPlus E I S mode u)
helicalProjectorPlusScale {F = F} E I S mode scalar u =
  let h = C3.realEmbed F (Helical.half S)
  in
  trans
    (cong (C3.complex3Scale h)
      (cong₂ C3.complex3Add
        (R73.lerayProjectComplexScale E I mode scalar u)
        (R157.normalizedCurlScale E S mode scalar u)))
    (R157.complex3ScaleNestedCommutes h scalar
      (C3.complex3Add
        (C3.lerayProject3 E I mode u)
        (R142.normalizedCurl E S mode u)))

helicalProjectorMinusScale :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F) (mode : Z3.FourierMode)
    (scalar : C3.Complex F) (u : C3.Complex3 F) →
  Helical.helicalProjectorMinus E I S mode (C3.complex3Scale scalar u)
  ≡ C3.complex3Scale scalar (Helical.helicalProjectorMinus E I S mode u)
helicalProjectorMinusScale {F = F} E I S mode scalar u =
  let h = C3.realEmbed F (Helical.half S)
  in
  trans
    (cong (C3.complex3Scale h)
      (cong₂ C3.complex3Subtract
        (R73.lerayProjectComplexScale E I mode scalar u)
        (R157.normalizedCurlScale E S mode scalar u)))
    (scaleCommuteMinus h scalar
      (C3.lerayProject3 E I mode u)
      (R142.normalizedCurl E S mode u))
  where
  scaleCommuteMinus :
    ∀ (h scalar : C3.Complex F) (a b : C3.Complex3 F) →
    C3.complex3Scale h
      (C3.complex3Subtract
        (C3.complex3Scale scalar a) (C3.complex3Scale scalar b))
    ≡ C3.complex3Scale scalar
        (C3.complex3Scale h (C3.complex3Subtract a b))
  scaleCommuteMinus h scalar
      (C3.complex3 ax ay az) (C3.complex3 bx by bz) =
    Field.complex3Ext
      (R.solve 4 (λ h s a b → h R.⊗ ((s R.⊗ a) R.⊕ (R.⊝ (s R.⊗ b))) R.⊜ s R.⊗ (h R.⊗ (a R.⊕ (R.⊝ b)))) refl h scalar ax bx)
      (R.solve 4 (λ h s a b → h R.⊗ ((s R.⊗ a) R.⊕ (R.⊝ (s R.⊗ b))) R.⊜ s R.⊗ (h R.⊗ (a R.⊕ (R.⊝ b)))) refl h scalar ay by)
      (R.solve 4 (λ h s a b → h R.⊗ ((s R.⊗ a) R.⊕ (R.⊝ (s R.⊗ b))) R.⊜ s R.⊗ (h R.⊗ (a R.⊕ (R.⊝ b)))) refl h scalar az bz)
    where module R = Ring.Solver F

helicalPlusDampedPlusForcing :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F) (mode : Z3.FourierMode)
    (rho : C3.Carrier F) (u f : C3.Complex3 F) →
  Helical.helicalProjectorPlus E I S mode (R94.dampedPlusForcing rho u f)
  ≡ R94.dampedPlusForcing rho
      (Helical.helicalProjectorPlus E I S mode u)
      (Helical.helicalProjectorPlus E I S mode f)
helicalPlusDampedPlusForcing E I S mode rho u f =
  trans
    (helicalProjectorPlusAdd E I S mode
      (C3.complex3Scale (R94.negativeReal rho) u) f)
    (cong₂ C3.complex3Add
      (helicalProjectorPlusScale E I S mode (R94.negativeReal rho) u) refl)

helicalMinusDampedPlusForcing :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F) (mode : Z3.FourierMode)
    (rho : C3.Carrier F) (u f : C3.Complex3 F) →
  Helical.helicalProjectorMinus E I S mode (R94.dampedPlusForcing rho u f)
  ≡ R94.dampedPlusForcing rho
      (Helical.helicalProjectorMinus E I S mode u)
      (Helical.helicalProjectorMinus E I S mode f)
helicalMinusDampedPlusForcing E I S mode rho u f =
  trans
    (helicalProjectorMinusAdd E I S mode
      (C3.complex3Scale (R94.negativeReal rho) u) f)
    (cong₂ C3.complex3Add
      (helicalProjectorMinusScale E I S mode (R94.negativeReal rho) u) refl)

mixedCellDampedTangent :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (rho : Z3.FourierMode → C3.Carrier F)
    (tau : Physical.PhysicalTriadIncidence) →
  R230.productRuleForcingCell S velocity
    (λ mode → R94.dampedPlusForcing (rho mode) (velocity mode) (forcing mode)) tau
  ≡
  C3.complex3Add
    (C3.complex3Scale
      (R94.negativeReal
        (C3.add F (rho (Physical.p tau)) (rho (Physical.q tau))))
      (R224.mixedPlusMinus S velocity tau))
    (R230.productRuleForcingCell S velocity forcing tau)
mixedCellDampedTangent {F = F} {E = E} {I = I}
    S velocity forcing rho tau =
  let
    p = Physical.p tau
    q = Physical.q tau
    up = Helical.helicalProjectorPlus E I S p (velocity p)
    uq = Helical.helicalProjectorMinus E I S q (velocity q)
    fp = Helical.helicalProjectorPlus E I S p (forcing p)
    fq = Helical.helicalProjectorMinus E I S q (forcing q)
    rp = rho p
    rq = rho q
  in
  trans
    (cong₂ C3.complex3Add
      (cong₂ R94.crossAddLeft
        (helicalPlusDampedPlusForcing E I S p rp (velocity p) (forcing p)) refl)
      (cong₂ R94.crossAddRight refl
        (helicalMinusDampedPlusForcing E I S q rq (velocity q) (forcing q))))
    (cellRegroup rp rq up uq fp fq)
  where
  cellRegroup :
    ∀ (rp rq : C3.Carrier F)
      (up uq fp fq : C3.Complex3 F) →
    C3.complex3Add
      (Cross.complex3Cross (R94.dampedPlusForcing rp up fp) uq)
      (Cross.complex3Cross up (R94.dampedPlusForcing rq uq fq))
    ≡
    C3.complex3Add
      (C3.complex3Scale
        (R94.negativeReal (C3.add F rp rq))
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
    in
    trans
      (cong₂ C3.complex3Add left right)
      (combine rp rq (Cross.complex3Cross up uq)
        (Cross.complex3Cross fp uq) (Cross.complex3Cross up fq))
    where
    combine :
      ∀ (rp rq : C3.Carrier F) (a b c : C3.Complex3 F) →
      C3.complex3Add
        (C3.complex3Add (C3.complex3Scale (R94.negativeReal rp) a) b)
        (C3.complex3Add (C3.complex3Scale (R94.negativeReal rq) a) c)
      ≡
      C3.complex3Add
        (C3.complex3Scale (R94.negativeReal (C3.add F rp rq)) a)
        (C3.complex3Add b c)
    combine rp rq
        (C3.complex3 ax ay az) (C3.complex3 bx by bz) (C3.complex3 cx cy cz) =
      Field.complex3Ext
        (R.solve 5 (λ rp rq a b c → (((R.⊝ rp) R.⊗ a) R.⊕ b) R.⊕ (((R.⊝ rq) R.⊗ a) R.⊕ c) R.⊜ ((R.⊝ (rp R.⊕ rq)) R.⊗ a) R.⊕ (b R.⊕ c)) refl (C3.realEmbed F rp) (C3.realEmbed F rq) ax bx cx)
        (R.solve 5 (λ rp rq a b c → (((R.⊝ rp) R.⊗ a) R.⊕ b) R.⊕ (((R.⊝ rq) R.⊗ a) R.⊕ c) R.⊜ ((R.⊝ (rp R.⊕ rq)) R.⊗ a) R.⊕ (b R.⊕ c)) refl (C3.realEmbed F rp) (C3.realEmbed F rq) ay by cy)
        (R.solve 5 (λ rp rq a b c → (((R.⊝ rp) R.⊗ a) R.⊕ b) R.⊕ (((R.⊝ rq) R.⊗ a) R.⊕ c) R.⊜ ((R.⊝ (rp R.⊕ rq)) R.⊗ a) R.⊕ (b R.⊕ c)) refl (C3.realEmbed F rp) (C3.realEmbed F rq) az bz cz)
      where module R = Ring.Solver F

round292HelicalProjectorsDampedForcedLinear : Bool
round292HelicalProjectorsDampedForcedLinear = true

round292LiteralR227CellDampedTangentClosed : Bool
round292LiteralR227CellDampedTangentClosed = true

round292NonlinearRemainderIsLiteralR230ProductRuleCell : Bool
round292NonlinearRemainderIsLiteralR230ProductRuleCell = true

round292PhysicalRhoEqualsNuModeSquareWeldClosed : Bool
round292PhysicalRhoEqualsNuModeSquareWeldClosed = false

round292PairFluxAggregationClosed : Bool
round292PairFluxAggregationClosed = false

round292PackageAClosed : Bool
round292PackageAClosed = false

round292ClayPromotion : Bool
round292ClayPromotion = false

round292LiteralR227CellDampedTangentClosedIsTrue :
  round292LiteralR227CellDampedTangentClosed ≡ true
round292LiteralR227CellDampedTangentClosedIsTrue = refl
