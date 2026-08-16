module DASHI.Moonshine.OggCyclicFixedSpaceFourProbeNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7, pp. 1-8.
-- MR 417184; no DOI assigned.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230-239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Strengthen the earlier C2/C3 fixed-space no-go.  Even the four-probe
-- signature
--
--   (dim V_j^C2, dim V_j^C3, dim V_j^C4, dim V_j^C5)
--
-- cannot characterize the Ogg locus: j=6 (dimension 13, Ogg) and j=7
-- (dimension 15, non-Ogg control) both give
--
--   (7,5,3,3).
--
-- Hence *every* Boolean selector factoring only through these four cyclic
-- fixed-space dimensions must assign the same result to 13 and 15.  Richer
-- branching/operator/correspondence information is mathematically necessary.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.PolyhedralFixedSpaceSpectrumJ0To35Exact as Fixed

record CyclicFixedSignature4 : Set where
  constructor cyclicFixedSignature4
  field
    c2 c3 c4 c5 : Nat

open CyclicFixedSignature4 public

cyclicFixedSignature : Spin.AngularMomentum0To35 → CyclicFixedSignature4
cyclicFixedSignature j =
  cyclicFixedSignature4
    (Fixed.fixedDimension j Fixed.C2Probe)
    (Fixed.fixedDimension j Fixed.C3Probe)
    (Fixed.fixedDimension j Fixed.C4Probe)
    (Fixed.fixedDimension j Fixed.C5Probe)

j6DimensionIsThirteen : Spin.jDimension Spin.j6 ≡ 13
j6DimensionIsThirteen = refl

j7DimensionIsFifteen : Spin.jDimension Spin.j7 ≡ 15
j7DimensionIsFifteen = refl

j6FourProbeSignature :
  cyclicFixedSignature Spin.j6 ≡ cyclicFixedSignature4 7 5 3 3
j6FourProbeSignature = refl

j7FourProbeSignature :
  cyclicFixedSignature Spin.j7 ≡ cyclicFixedSignature4 7 5 3 3
j7FourProbeSignature = refl

j6AndJ7FourProbeSignaturesCoincide :
  cyclicFixedSignature Spin.j6 ≡ cyclicFixedSignature Spin.j7
j6AndJ7FourProbeSignaturesCoincide = refl

CyclicFixedSignatureSelector : Set
CyclicFixedSignatureSelector = CyclicFixedSignature4 → Bool

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

fourProbeSelectorCannotSeparateThirteenAndFifteen :
  (selector : CyclicFixedSignatureSelector) →
  selector (cyclicFixedSignature Spin.j6) ≡ true →
  selector (cyclicFixedSignature Spin.j7) ≡ false →
  ⊥
fourProbeSelectorCannotSeparateThirteenAndFifteen
  selector selects13 rejects15 =
  falseNotTrue
    (trans
      (sym rejects15)
      (trans
        (cong selector (sym j6AndJ7FourProbeSignaturesCoincide))
        selects13))

------------------------------------------------------------------------
-- Benchmark polarity is external to the representation producer.  It is
-- recorded only to state the control test; it is not used to compute the
-- fixed-space signature.
------------------------------------------------------------------------

dimension13ExpectedOggStatus : Bool
dimension13ExpectedOggStatus = true

dimension15ExpectedOggStatus : Bool
dimension15ExpectedOggStatus = false

expectedStatusesDiffer :
  dimension13ExpectedOggStatus ≡ dimension15ExpectedOggStatus → ⊥
expectedStatusesDiffer ()

record FourProbeNoGoBoundary : Set where
  field
    c2c3c4c5ComputedWithoutOggPremise : Bool
    c2c3c4c5ComputedWithoutOggPremiseIsTrue :
      c2c3c4c5ComputedWithoutOggPremise ≡ true

    fourProbeCollisionConstructed : Bool
    fourProbeCollisionConstructedIsTrue :
      fourProbeCollisionConstructed ≡ true

    fourProbeSignatureAloneSelectsOgg : Bool
    fourProbeSignatureAloneSelectsOggIsFalse :
      fourProbeSignatureAloneSelectsOgg ≡ false

    operatorLevelSelectorRefutedHere : Bool
    operatorLevelSelectorRefutedHereIsFalse :
      operatorLevelSelectorRefutedHere ≡ false

canonicalFourProbeNoGoBoundary : FourProbeNoGoBoundary
canonicalFourProbeNoGoBoundary =
  record
    { c2c3c4c5ComputedWithoutOggPremise = true
    ; c2c3c4c5ComputedWithoutOggPremiseIsTrue = refl
    ; fourProbeCollisionConstructed = true
    ; fourProbeCollisionConstructedIsTrue = refl
    ; fourProbeSignatureAloneSelectsOgg = false
    ; fourProbeSignatureAloneSelectsOggIsFalse = refl
    ; operatorLevelSelectorRefutedHere = false
    ; operatorLevelSelectorRefutedHereIsFalse = refl
    }
