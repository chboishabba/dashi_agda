module DASHI.Moonshine.JInvariantEisensteinBishopRadiusWeldExact where

------------------------------------------------------------------------
-- LITERAL q-RADIUS -> BISHOP E4/E6 MAJORANT COMPILER
--
-- DASHI CONTRIBUTION
--
-- The analytic convergence theorem is now fully paid on the concrete Bishop
-- backend.  What remains is a representation theorem saying that the literal
-- legacy |q(tau)| is represented by one Bishop real radius r with
--
--   0 <= r < 1.
--
-- This owner isolates that statement without inventing the cross-carrier
-- equality relation.  The relation is an explicit parameter supplied by the
-- caller; the weld carries exactly one same-object witness plus the Bishop
-- unit-interval certificate.
--
-- Once that weld exists, both literal Eisenstein-shaped majorant series are
-- absolutely convergent immediately:
--
--   240 (n+1)^4 r^(n+1)
--   504 (n+1)^6 r^(n+1).
--
-- No additional polynomial/geometric estimate, ratio choice, or Cauchy theorem
-- remains in this compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopConstructedRealBackendExact as BishopBackend
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Moonshine.JInvariantEisensteinBishopMajorantSeriesExact as Majorant

record LiteralRadiusBishopWeld
    {LegacyRadius : Set}
    (_≈B_ : LegacyRadius → BishopReal.ℝ → Set)
    (literalRadius : LegacyRadius) : Set₁ where
  field
    bishopRadius : BishopReal.ℝ
    sameRadius : _≈B_ literalRadius bishopRadius
    unitInterval : Unit.BishopUnitIntervalRatio bishopRadius

open LiteralRadiusBishopWeld public

record EisensteinBishopMajorantReceipt
    {LegacyRadius : Set}
    (_≈B_ : LegacyRadius → BishopReal.ℝ → Set)
    (literalRadius : LegacyRadius)
    (weld : LiteralRadiusBishopWeld _≈B_ literalRadius) : Set₁ where
  field
    radiusAgreement : _≈B_ literalRadius (bishopRadius weld)

    e4AbsoluteConvergence :
      BishopSequence.SeriesOf_ConvergesAbsolutely
        (Majorant.e4MajorantTerm (bishopRadius weld))

    e6AbsoluteConvergence :
      BishopSequence.SeriesOf_ConvergesAbsolutely
        (Majorant.e6MajorantTerm (bishopRadius weld))

open EisensteinBishopMajorantReceipt public

compileEisensteinBishopMajorants :
  ∀ {LegacyRadius : Set}
    {_≈B_ : LegacyRadius → BishopReal.ℝ → Set}
    {literalRadius : LegacyRadius} →
  (weld : LiteralRadiusBishopWeld _≈B_ literalRadius) →
  EisensteinBishopMajorantReceipt _≈B_ literalRadius weld
compileEisensteinBishopMajorants weld = record
  { radiusAgreement = sameRadius weld
  ; e4AbsoluteConvergence =
      Majorant.e4MajorantAbsoluteConvergence
        (unitInterval weld)
  ; e6AbsoluteConvergence =
      Majorant.e6MajorantAbsoluteConvergence
        (unitInterval weld)
  }


------------------------------------------------------------------------
-- Canonical same-object relation induced by a concrete quotient of the
-- repository's selected Murray/Bishop setoid backend.
------------------------------------------------------------------------

BishopSetoidReal : Spine.SetoidOrderedCompleteReal
BishopSetoidReal =
  BishopBackend.bishopImportedSetoidOrderedCompleteReal

QuotientRadiusRelation :
  (Q : Spine.PropositionalQuotientRealization BishopSetoidReal) →
  Spine.Quotient Q →
  BishopReal.ℝ →
  Set
QuotientRadiusRelation Q legacyRadius radius =
  Spine.quotient Q radius ≡ legacyRadius

radiusWeldFromConcreteBishopQuotient :
  (Q : Spine.PropositionalQuotientRealization BishopSetoidReal) →
  (radius : BishopReal.ℝ) →
  Unit.BishopUnitIntervalRatio radius →
  LiteralRadiusBishopWeld
    (QuotientRadiusRelation Q)
    (Spine.quotient Q radius)
radiusWeldFromConcreteBishopQuotient Q radius unit = record
  { bishopRadius = radius
  ; sameRadius = refl
  ; unitInterval = unit
  }

majorantsFromConcreteBishopQuotient :
  (Q : Spine.PropositionalQuotientRealization BishopSetoidReal) →
  (radius : BishopReal.ℝ) →
  (unit : Unit.BishopUnitIntervalRatio radius) →
  EisensteinBishopMajorantReceipt
    (QuotientRadiusRelation Q)
    (Spine.quotient Q radius)
    (radiusWeldFromConcreteBishopQuotient Q radius unit)
majorantsFromConcreteBishopQuotient Q radius unit =
  compileEisensteinBishopMajorants
    (radiusWeldFromConcreteBishopQuotient Q radius unit)
