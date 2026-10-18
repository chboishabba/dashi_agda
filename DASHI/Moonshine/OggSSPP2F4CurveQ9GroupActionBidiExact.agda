module DASHI.Moonshine.OggSSPP2F4CurveQ9GroupActionBidiExact where

------------------------------------------------------------------------
-- ACTUAL F4 CURVE CHORD GROUP -> ORIGINAL DASHI PHASE QUOTIENT 9
--
-- Imports the independently checked nine-point chord law and the genuine
-- q9Add owner, Base369.triXor×Base369.triXor.
--
-- Proves all of:
-- * two-sided F4 curve / PhaseQuotient9 chart,
-- * preservation of ACTUAL chord addition,
-- * Frobenius reflection and cube-root shear as group automorphisms,
-- * transport of the group law to the SIGNED centre (mid,mid),
-- * inversion = signed reversal in centered coordinates.
--
-- The ordinary q9Add identity is (low,low); the centered group identity
-- is (mid,mid). This explicitly prevents false identification of the
-- naive signed-negation map with inverse for the UNTRANSLATED q9Add.
--
-- The comparison with Mathlib's actual Weierstrass point AddCommGroup
-- and any VOA/Monster/Gamma0(4) same-object theorem remain separate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import Base369 as Base
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase
import DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact as Q9
import DASHI.Moonshine.OggSSPP2F4ZetaCurvePointEnumerationExact as Curve
import DASHI.Moonshine.OggSSPP2F4CurveExactChordGroup as Group
import DASHI.Moonshine.OggSSPP2F4CurveShearReflectionExact as Action
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

coeffToTri : Group.Coeff3 → Base.TriTruth
coeffToTri Group.c0 = Base.tri-low
coeffToTri Group.c1 = Base.tri-mid
coeffToTri Group.c2 = Base.tri-high

triToCoeff : Base.TriTruth → Group.Coeff3
triToCoeff Base.tri-low = Group.c0
triToCoeff Base.tri-mid = Group.c1
triToCoeff Base.tri-high = Group.c2

coeffTriRoundtrip : (a : Group.Coeff3) → triToCoeff (coeffToTri a) ≡ a
coeffTriRoundtrip Group.c0 = refl
coeffTriRoundtrip Group.c1 = refl
coeffTriRoundtrip Group.c2 = refl

triCoeffRoundtrip : (a : Base.TriTruth) → coeffToTri (triToCoeff a) ≡ a
triCoeffRoundtrip Base.tri-low = refl
triCoeffRoundtrip Base.tri-mid = refl
triCoeffRoundtrip Base.tri-high = refl

curveToQ9 : Curve.RationalF4Point → Phase.PhaseQuotient9
curveToQ9 p =
  coeffToTri (proj₁ (Group.chartDecoding p)) ,
  coeffToTri (proj₂ (Group.chartDecoding p))

q9ToCurve : Phase.PhaseQuotient9 → Curve.RationalF4Point
q9ToCurve (a , b) = Group.basisChart (triToCoeff a) (triToCoeff b)

curveAfterQ9 : (q : Phase.PhaseQuotient9) →
  curveToQ9 (q9ToCurve q) ≡ q
curveAfterQ9 (Base.tri-low , Base.tri-low) = refl
curveAfterQ9 (Base.tri-low , Base.tri-mid) = refl
curveAfterQ9 (Base.tri-low , Base.tri-high) = refl
curveAfterQ9 (Base.tri-mid , Base.tri-low) = refl
curveAfterQ9 (Base.tri-mid , Base.tri-mid) = refl
curveAfterQ9 (Base.tri-mid , Base.tri-high) = refl
curveAfterQ9 (Base.tri-high , Base.tri-low) = refl
curveAfterQ9 (Base.tri-high , Base.tri-mid) = refl
curveAfterQ9 (Base.tri-high , Base.tri-high) = refl

q9AfterCurve : (p : Curve.RationalF4Point) →
  q9ToCurve (curveToQ9 p) ≡ p
q9AfterCurve Curve.infinity = refl
q9AfterCurve (Curve.affine Curve.p00) = refl
q9AfterCurve (Curve.affine Curve.p01) = refl
q9AfterCurve (Curve.affine Curve.p1Zeta) = refl
q9AfterCurve (Curve.affine Curve.p1ZetaSquared) = refl
q9AfterCurve (Curve.affine Curve.pZetaZeta) = refl
q9AfterCurve (Curve.affine Curve.pZetaZetaSquared) = refl
q9AfterCurve (Curve.affine Curve.pZetaSquaredZeta) = refl
q9AfterCurve (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

-- This is the CRITICAL group-law compatibility missing from prior
-- pointed / Frobenius-only nine-sheet charts.
q9AdditionIsActualCurveChordAddition :
  (p q : Curve.RationalF4Point) →
  curveToQ9 (Group._⊞_ p q)
  ≡ Q9.q9Add (curveToQ9 p) (curveToQ9 q)
q9AdditionIsActualCurveChordAddition Curve.infinity Curve.infinity = refl
q9AdditionIsActualCurveChordAddition Curve.infinity (Curve.affine Curve.p00) = refl
q9AdditionIsActualCurveChordAddition Curve.infinity (Curve.affine Curve.p01) = refl
q9AdditionIsActualCurveChordAddition Curve.infinity (Curve.affine Curve.p1Zeta) = refl
q9AdditionIsActualCurveChordAddition Curve.infinity (Curve.affine Curve.p1ZetaSquared) = refl
q9AdditionIsActualCurveChordAddition Curve.infinity (Curve.affine Curve.pZetaZeta) = refl
q9AdditionIsActualCurveChordAddition Curve.infinity (Curve.affine Curve.pZetaZetaSquared) = refl
q9AdditionIsActualCurveChordAddition Curve.infinity (Curve.affine Curve.pZetaSquaredZeta) = refl
q9AdditionIsActualCurveChordAddition Curve.infinity (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p00) Curve.infinity = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p00) (Curve.affine Curve.p00) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p00) (Curve.affine Curve.p01) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p01) Curve.infinity = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p01) (Curve.affine Curve.p00) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p01) (Curve.affine Curve.p01) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1Zeta) Curve.infinity = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1ZetaSquared) Curve.infinity = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZeta) Curve.infinity = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZetaSquared) Curve.infinity = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZeta) Curve.infinity = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZetaSquared) Curve.infinity = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
q9AdditionIsActualCurveChordAddition (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

actualCurveZeroIsQ9Zero :
  curveToQ9 Curve.infinity ≡ Q9.q9Zero
actualCurveZeroIsQ9Zero = refl

-- Two distinct ACTUAL elliptic curve actions on the group, not a
-- free 27-code output phase rotation.
triNeg : Base.TriTruth → Base.TriTruth
triNeg Base.tri-low = Base.tri-low
triNeg Base.tri-mid = Base.tri-high
triNeg Base.tri-high = Base.tri-mid

phaseFrobenius : Phase.PhaseQuotient9 → Phase.PhaseQuotient9
phaseFrobenius (a , b) = a , triNeg b

phaseShear : Phase.PhaseQuotient9 → Phase.PhaseQuotient9
phaseShear (a , b) = Base.triXor a b , b

phaseInversion : Phase.PhaseQuotient9 → Phase.PhaseQuotient9
phaseInversion (a , b) = triNeg a , triNeg b

actualFrobeniusIntertwinesQ9 :
  (p : Curve.RationalF4Point) →
  curveToQ9 (Action.frobenius p) ≡ phaseFrobenius (curveToQ9 p)
actualFrobeniusIntertwinesQ9 Curve.infinity = refl
actualFrobeniusIntertwinesQ9 (Curve.affine Curve.p00) = refl
actualFrobeniusIntertwinesQ9 (Curve.affine Curve.p01) = refl
actualFrobeniusIntertwinesQ9 (Curve.affine Curve.p1Zeta) = refl
actualFrobeniusIntertwinesQ9 (Curve.affine Curve.p1ZetaSquared) = refl
actualFrobeniusIntertwinesQ9 (Curve.affine Curve.pZetaZeta) = refl
actualFrobeniusIntertwinesQ9 (Curve.affine Curve.pZetaZetaSquared) = refl
actualFrobeniusIntertwinesQ9 (Curve.affine Curve.pZetaSquaredZeta) = refl
actualFrobeniusIntertwinesQ9 (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

actualShearIntertwinesQ9 :
  (p : Curve.RationalF4Point) →
  curveToQ9 (Action.rho p) ≡ phaseShear (curveToQ9 p)
actualShearIntertwinesQ9 Curve.infinity = refl
actualShearIntertwinesQ9 (Curve.affine Curve.p00) = refl
actualShearIntertwinesQ9 (Curve.affine Curve.p01) = refl
actualShearIntertwinesQ9 (Curve.affine Curve.p1Zeta) = refl
actualShearIntertwinesQ9 (Curve.affine Curve.p1ZetaSquared) = refl
actualShearIntertwinesQ9 (Curve.affine Curve.pZetaZeta) = refl
actualShearIntertwinesQ9 (Curve.affine Curve.pZetaZetaSquared) = refl
actualShearIntertwinesQ9 (Curve.affine Curve.pZetaSquaredZeta) = refl
actualShearIntertwinesQ9 (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

actualInversionIntertwinesQ9 :
  (p : Curve.RationalF4Point) →
  curveToQ9 (Group.curveInverse p) ≡ phaseInversion (curveToQ9 p)
actualInversionIntertwinesQ9 Curve.infinity = refl
actualInversionIntertwinesQ9 (Curve.affine Curve.p00) = refl
actualInversionIntertwinesQ9 (Curve.affine Curve.p01) = refl
actualInversionIntertwinesQ9 (Curve.affine Curve.p1Zeta) = refl
actualInversionIntertwinesQ9 (Curve.affine Curve.p1ZetaSquared) = refl
actualInversionIntertwinesQ9 (Curve.affine Curve.pZetaZeta) = refl
actualInversionIntertwinesQ9 (Curve.affine Curve.pZetaZetaSquared) = refl
actualInversionIntertwinesQ9 (Curve.affine Curve.pZetaSquaredZeta) = refl
actualInversionIntertwinesQ9 (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

-- The naive signed centre differs from the ORIGINAL q9Add group zero.
-- Translate each coordinate by +1 (rotateTri) and transport the law.
center : Phase.PhaseQuotient9 → Phase.PhaseQuotient9
center (a , b) = Base.rotateTri a , Base.rotateTri b

uncenter : Phase.PhaseQuotient9 → Phase.PhaseQuotient9
uncenter (a , b) =
  Base.rotateTri (Base.rotateTri a) ,
  Base.rotateTri (Base.rotateTri b)

centerAfterUncenter : (q : Phase.PhaseQuotient9) →
  center (uncenter q) ≡ q
centerAfterUncenter (Base.tri-low , Base.tri-low) = refl
centerAfterUncenter (Base.tri-low , Base.tri-mid) = refl
centerAfterUncenter (Base.tri-low , Base.tri-high) = refl
centerAfterUncenter (Base.tri-mid , Base.tri-low) = refl
centerAfterUncenter (Base.tri-mid , Base.tri-mid) = refl
centerAfterUncenter (Base.tri-mid , Base.tri-high) = refl
centerAfterUncenter (Base.tri-high , Base.tri-low) = refl
centerAfterUncenter (Base.tri-high , Base.tri-mid) = refl
centerAfterUncenter (Base.tri-high , Base.tri-high) = refl

uncenterAfterCenter : (q : Phase.PhaseQuotient9) →
  uncenter (center q) ≡ q
uncenterAfterCenter (Base.tri-low , Base.tri-low) = refl
uncenterAfterCenter (Base.tri-low , Base.tri-mid) = refl
uncenterAfterCenter (Base.tri-low , Base.tri-high) = refl
uncenterAfterCenter (Base.tri-mid , Base.tri-low) = refl
uncenterAfterCenter (Base.tri-mid , Base.tri-mid) = refl
uncenterAfterCenter (Base.tri-mid , Base.tri-high) = refl
uncenterAfterCenter (Base.tri-high , Base.tri-low) = refl
uncenterAfterCenter (Base.tri-high , Base.tri-mid) = refl
uncenterAfterCenter (Base.tri-high , Base.tri-high) = refl

centeredAdd : Phase.PhaseQuotient9 → Phase.PhaseQuotient9 →
  Phase.PhaseQuotient9
centeredAdd a b = center (Q9.q9Add (uncenter a) (uncenter b))

centeredZero : Phase.PhaseQuotient9
centeredZero = Base.tri-mid , Base.tri-mid

curveToCenteredQ9 : Curve.RationalF4Point → Phase.PhaseQuotient9
curveToCenteredQ9 p = center (curveToQ9 p)

centeredQ9ToCurve : Phase.PhaseQuotient9 → Curve.RationalF4Point
centeredQ9ToCurve q = q9ToCurve (uncenter q)

curveToCenteredQ9Zero :
  curveToCenteredQ9 Curve.infinity ≡ centeredZero
curveToCenteredQ9Zero = refl

centeredCurveAfterQ9 : (q : Phase.PhaseQuotient9) →
  curveToCenteredQ9 (centeredQ9ToCurve q) ≡ q
centeredCurveAfterQ9 (Base.tri-low , Base.tri-low) = refl
centeredCurveAfterQ9 (Base.tri-low , Base.tri-mid) = refl
centeredCurveAfterQ9 (Base.tri-low , Base.tri-high) = refl
centeredCurveAfterQ9 (Base.tri-mid , Base.tri-low) = refl
centeredCurveAfterQ9 (Base.tri-mid , Base.tri-mid) = refl
centeredCurveAfterQ9 (Base.tri-mid , Base.tri-high) = refl
centeredCurveAfterQ9 (Base.tri-high , Base.tri-low) = refl
centeredCurveAfterQ9 (Base.tri-high , Base.tri-mid) = refl
centeredCurveAfterQ9 (Base.tri-high , Base.tri-high) = refl

centeredQ9AfterCurve : (p : Curve.RationalF4Point) →
  centeredQ9ToCurve (curveToCenteredQ9 p) ≡ p
centeredQ9AfterCurve Curve.infinity = refl
centeredQ9AfterCurve (Curve.affine Curve.p00) = refl
centeredQ9AfterCurve (Curve.affine Curve.p01) = refl
centeredQ9AfterCurve (Curve.affine Curve.p1Zeta) = refl
centeredQ9AfterCurve (Curve.affine Curve.p1ZetaSquared) = refl
centeredQ9AfterCurve (Curve.affine Curve.pZetaZeta) = refl
centeredQ9AfterCurve (Curve.affine Curve.pZetaZetaSquared) = refl
centeredQ9AfterCurve (Curve.affine Curve.pZetaSquaredZeta) = refl
centeredQ9AfterCurve (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

centeredAddPreservesActualChordLaw :
  (p q : Curve.RationalF4Point) →
  curveToCenteredQ9 (Group._⊞_ p q)
  ≡ centeredAdd (curveToCenteredQ9 p) (curveToCenteredQ9 q)
centeredAddPreservesActualChordLaw Curve.infinity Curve.infinity = refl
centeredAddPreservesActualChordLaw Curve.infinity (Curve.affine Curve.p00) = refl
centeredAddPreservesActualChordLaw Curve.infinity (Curve.affine Curve.p01) = refl
centeredAddPreservesActualChordLaw Curve.infinity (Curve.affine Curve.p1Zeta) = refl
centeredAddPreservesActualChordLaw Curve.infinity (Curve.affine Curve.p1ZetaSquared) = refl
centeredAddPreservesActualChordLaw Curve.infinity (Curve.affine Curve.pZetaZeta) = refl
centeredAddPreservesActualChordLaw Curve.infinity (Curve.affine Curve.pZetaZetaSquared) = refl
centeredAddPreservesActualChordLaw Curve.infinity (Curve.affine Curve.pZetaSquaredZeta) = refl
centeredAddPreservesActualChordLaw Curve.infinity (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p00) Curve.infinity = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p00) (Curve.affine Curve.p00) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p00) (Curve.affine Curve.p01) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p00) (Curve.affine Curve.p1Zeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p00) (Curve.affine Curve.p1ZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p00) (Curve.affine Curve.pZetaZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p00) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p01) Curve.infinity = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p01) (Curve.affine Curve.p00) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p01) (Curve.affine Curve.p01) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p01) (Curve.affine Curve.p1Zeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p01) (Curve.affine Curve.p1ZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p01) (Curve.affine Curve.pZetaZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p01) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1Zeta) Curve.infinity = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p00) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p01) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1Zeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1Zeta) (Curve.affine Curve.p1ZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1Zeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1ZetaSquared) Curve.infinity = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p00) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p01) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1Zeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.p1ZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZeta) Curve.infinity = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p00) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p01) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1Zeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.p1ZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZetaSquared) Curve.infinity = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p00) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p01) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1Zeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZeta) Curve.infinity = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p00) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p01) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1Zeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.p1ZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZeta) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZetaSquared) Curve.infinity = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p00) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p01) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1Zeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.p1ZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaZetaSquared) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZeta) = refl
centeredAddPreservesActualChordLaw (Curve.affine Curve.pZetaSquaredZetaSquared) (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

signedNeg : Phase.PhaseQuotient9 → Phase.PhaseQuotient9
signedNeg (a , b) = reflect a , reflect b
  where
    reflect : Base.TriTruth → Base.TriTruth
    reflect Base.tri-low = Base.tri-high
    reflect Base.tri-mid = Base.tri-mid
    reflect Base.tri-high = Base.tri-low

centeredInversionIsSignedNeg :
  (p : Curve.RationalF4Point) →
  curveToCenteredQ9 (Group.curveInverse p)
  ≡ signedNeg (curveToCenteredQ9 p)
centeredInversionIsSignedNeg Curve.infinity = refl
centeredInversionIsSignedNeg (Curve.affine Curve.p00) = refl
centeredInversionIsSignedNeg (Curve.affine Curve.p01) = refl
centeredInversionIsSignedNeg (Curve.affine Curve.p1Zeta) = refl
centeredInversionIsSignedNeg (Curve.affine Curve.p1ZetaSquared) = refl
centeredInversionIsSignedNeg (Curve.affine Curve.pZetaZeta) = refl
centeredInversionIsSignedNeg (Curve.affine Curve.pZetaZetaSquared) = refl
centeredInversionIsSignedNeg (Curve.affine Curve.pZetaSquaredZeta) = refl
centeredInversionIsSignedNeg (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

centeredFrobenius : Phase.PhaseQuotient9 → Phase.PhaseQuotient9
centeredFrobenius q = center (phaseFrobenius (uncenter q))

centeredShear : Phase.PhaseQuotient9 → Phase.PhaseQuotient9
centeredShear q = center (phaseShear (uncenter q))

centeredFrobeniusWeld :
  (p : Curve.RationalF4Point) →
  curveToCenteredQ9 (Action.frobenius p)
  ≡ centeredFrobenius (curveToCenteredQ9 p)
centeredFrobeniusWeld Curve.infinity = refl
centeredFrobeniusWeld (Curve.affine Curve.p00) = refl
centeredFrobeniusWeld (Curve.affine Curve.p01) = refl
centeredFrobeniusWeld (Curve.affine Curve.p1Zeta) = refl
centeredFrobeniusWeld (Curve.affine Curve.p1ZetaSquared) = refl
centeredFrobeniusWeld (Curve.affine Curve.pZetaZeta) = refl
centeredFrobeniusWeld (Curve.affine Curve.pZetaZetaSquared) = refl
centeredFrobeniusWeld (Curve.affine Curve.pZetaSquaredZeta) = refl
centeredFrobeniusWeld (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

centeredShearWeld :
  (p : Curve.RationalF4Point) →
  curveToCenteredQ9 (Action.rho p)
  ≡ centeredShear (curveToCenteredQ9 p)
centeredShearWeld Curve.infinity = refl
centeredShearWeld (Curve.affine Curve.p00) = refl
centeredShearWeld (Curve.affine Curve.p01) = refl
centeredShearWeld (Curve.affine Curve.p1Zeta) = refl
centeredShearWeld (Curve.affine Curve.p1ZetaSquared) = refl
centeredShearWeld (Curve.affine Curve.pZetaZeta) = refl
centeredShearWeld (Curve.affine Curve.pZetaZetaSquared) = refl
centeredShearWeld (Curve.affine Curve.pZetaSquaredZeta) = refl
centeredShearWeld (Curve.affine Curve.pZetaSquaredZetaSquared) = refl

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record Boundary : Set where
  constructor boundary
  field
    actualCurveChordGroupQ9Bidi : Bool
    preservesOriginalBase369TriXor : Bool
    frobeniusAndShearIntertwining : Bool
    centerTranslatedToMidMid : Bool
    signedInversionNowCorrect : Bool
    centeredGroupAdditionTransported : Bool
    comparisonWithMathlibActualEllipticGroup : Bool
    monsterValuationRecognition : Bool
canonicalBoundary : Boundary
canonicalBoundary = boundary true true true true true true false false
