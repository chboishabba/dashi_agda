module DASHI.Moonshine.JInvariantEllipticFixedPointCompilerExact where

------------------------------------------------------------------------
-- ELLIPTIC FIXED-POINT VANISHING, REUSING ORIGINAL EISENSTEIN SERIES
--
-- Attribution: Eisenstein modular-form transformation (classical);
-- Serre, A Course in Arithmetic (1973); Miyake, Modular Forms (2006).
-- Reuses the repo's explicit SL2(Z) lattice-index transformation proof,
-- rather than postulating E4/E6 modularity a second time.
--
-- THIS IS A CONDITIONAL COMPILER, not a new concrete analytic j-value:
-- concrete S/ST fixed points, scalar nontrivial-factor cancellation,
-- Bishop q/lattice identity and Delta nonvanishing must be instantiated
-- on the literal constructive complex carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Eisenstein
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact as Disc

record EllipticFixedPointEvidence
    (M : Eisenstein.EisensteinAnalyticModel) : Set₁ where
  field
    s : Eisenstein.SL2Z
    st : Eisenstein.SL2Z

    iPoint : Eisenstein.Parameter M
    omegaPoint : Eisenstein.Parameter M

    sFixesI :
      Eisenstein.actParameter M s iPoint ≡ iPoint
    stFixesOmega :
      Eisenstein.actParameter M st omegaPoint ≡ omegaPoint

    -- In a characteristic-zero complex field, these follow by
    -- subtraction/cancellation from (c tau+d)^6 != 1 at i and
    -- (c tau+d)^4 != 1 at omega.
    -- They are explicitly outstanding, not assumed proven below.
    weight6IFactorForcesZero :
      (x : Eisenstein.Scalar M) →
      x ≡ Eisenstein._*ˢ_ M
        (Eisenstein.power M (Eisenstein.denominator M s iPoint) 6)
        x →
      x ≡ Eisenstein.zero M

    weight4OmegaFactorForcesZero :
      (x : Eisenstein.Scalar M) →
      x ≡ Eisenstein._*ˢ_ M
        (Eisenstein.power M (Eisenstein.denominator M st omegaPoint) 4)
        x →
      x ≡ Eisenstein.zero M

open EllipticFixedPointEvidence public

------------------------------------------------------------------------
-- Genuine use of the existing global transformation theorem:
-- E6(i) = (c i + d)^6 E6(i), E4(omega) = (c omega+d)^4 E4(omega).
------------------------------------------------------------------------

e6AtIFixedWeightEquation :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (W : EllipticFixedPointEvidence M) →
  Disc.E6 M (iPoint W)
    ≡ Eisenstein._*ˢ_ M
       (Eisenstein.power M
         (Eisenstein.denominator M (s W) (iPoint W)) 6)
       (Disc.E6 M (iPoint W))
e6AtIFixedWeightEquation M W =
  trans
    (cong (Disc.E6 M) (sym (sFixesI W)))
    (Eisenstein.eisensteinTransformation M 6 (s W) (iPoint W))

e4AtOmegaFixedWeightEquation :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (W : EllipticFixedPointEvidence M) →
  Disc.E4 M (omegaPoint W)
    ≡ Eisenstein._*ˢ_ M
       (Eisenstein.power M
         (Eisenstein.denominator M (st W) (omegaPoint W)) 4)
       (Disc.E4 M (omegaPoint W))
e4AtOmegaFixedWeightEquation M W =
  trans
    (cong (Disc.E4 M) (sym (stFixesOmega W)))
    (Eisenstein.eisensteinTransformation M 4 (st W) (omegaPoint W))

e6AtIIsZero :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (W : EllipticFixedPointEvidence M) →
  Disc.E6 M (iPoint W) ≡ Eisenstein.zero M
e6AtIIsZero M W =
  weight6IFactorForcesZero W
    (Disc.E6 M (iPoint W))
    (e6AtIFixedWeightEquation M W)

e4AtOmegaIsZero :
  (M : Eisenstein.EisensteinAnalyticModel) →
  (W : EllipticFixedPointEvidence M) →
  Disc.E4 M (omegaPoint W) ≡ Eisenstein.zero M
e4AtOmegaIsZero M W =
  weight4OmegaFactorForcesZero W
    (Disc.E4 M (omegaPoint W))
    (e4AtOmegaFixedWeightEquation M W)

------------------------------------------------------------------------
-- Promotion remains STRICT: no claim that these records have concrete
-- inhabitants in the current Bishop complex q-series/lattice model.
-- j(i)=1728 and j(omega)=0 additionally require exact normalized
-- quotient evaluation and Delta != 0 at the selected original points.
------------------------------------------------------------------------
