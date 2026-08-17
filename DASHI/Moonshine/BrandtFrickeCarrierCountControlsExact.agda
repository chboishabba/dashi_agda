module DASHI.Moonshine.BrandtFrickeCarrierCountControlsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires", 1974/75, MR 417184; no DOI.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- John Voight,
-- "Quaternion Algebras", Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- DASHI CONTRIBUTION
--
-- Run a cheap same-carrier falsifier across the current Brandt/Fricke controls.
-- p=37 has three source Brandt classes but only two Fricke fixed points, so the
-- two sets cannot literally be the same fixed-point carrier.  p=43 has four of
-- each, but that equality is retained only as a cardinality coincidence: the
-- C9 versus F9 development supplies a concrete nine-state warning that equal
-- size does not construct an algebra/action identification.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.BrandtStackUnweightingControlsExact as Stack
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.PrimeFrickeGenusControlExact as Fricke
import DASHI.Foundations.TernaryNineRingFieldFibreSeparationExact as Nine
import DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact as Separation

p37BrandtClassCount : Nat
p37BrandtClassCount = 3

p37FrickeFixedCount : Nat
p37FrickeFixedCount =
  Fricke.frickeFixedPointCount (Fricke.frickeRow Matrix.prime37)

p37FrickeFixedCountIsTwo : p37FrickeFixedCount ≡ 2
p37FrickeFixedCountIsTwo = refl

record P37SameCarrierFrickeIdentification : Set where
  field
    fixedPointsAreBrandtClasses : p37FrickeFixedCount ≡ p37BrandtClassCount

p37SameCarrierIdentificationImpossible :
  P37SameCarrierFrickeIdentification → ⊥
p37SameCarrierIdentificationImpossible record
  { fixedPointsAreBrandtClasses = () }

p43BrandtClassCount : Nat
p43BrandtClassCount = 4

p43FrickeFixedCount : Nat
p43FrickeFixedCount =
  Fricke.frickeFixedPointCount (Fricke.frickeRow Matrix.prime43)

p43FrickeFixedCountIsFour : p43FrickeFixedCount ≡ 4
p43FrickeFixedCountIsFour = refl

p43BrandtAndFrickeCountsCoincide : p43BrandtClassCount ≡ p43FrickeFixedCount
p43BrandtAndFrickeCountsCoincide = refl

-- Equal finite size cannot by itself promote a structure identity.  The
-- existing C9/F9 witness is reused rather than restating the argument.
equalNineStateSizeDoesNotForceGroupIdentification :
  Separation.Q9NonaryGroupIsomorphism → ⊥
equalNineStateSizeDoesNotForceGroupIdentification =
  Nine.noAdditiveGroupIdentificationWithC9

p37SourceClassCarrierStillThree : Stack.p37UnweightedStateCount ≡ 3
p37SourceClassCarrierStillThree = Stack.p37UnweightedStateCountIsThree

p43SourceFineCoverStillSeven : Stack.p43UnweightedStateCount ≡ 7
p43SourceFineCoverStillSeven = Stack.p43UnweightedStateCountIsSeven

record BrandtFrickeCarrierCountBoundary : Set where
  field
    p37SameCarrierCountFalsified : Bool
    p37SameCarrierCountFalsifiedIsTrue :
      p37SameCarrierCountFalsified ≡ true

    p43CountCoincidenceRecorded : Bool
    p43CountCoincidenceRecordedIsTrue :
      p43CountCoincidenceRecorded ≡ true

    p43CountCoincidencePromotedToActionIdentity : Bool
    p43CountCoincidencePromotedToActionIdentityIsFalse :
      p43CountCoincidencePromotedToActionIdentity ≡ false

canonicalBrandtFrickeCarrierCountBoundary : BrandtFrickeCarrierCountBoundary
canonicalBrandtFrickeCarrierCountBoundary = record
  { p37SameCarrierCountFalsified = true
  ; p37SameCarrierCountFalsifiedIsTrue = refl
  ; p43CountCoincidenceRecorded = true
  ; p43CountCoincidenceRecordedIsTrue = refl
  ; p43CountCoincidencePromotedToActionIdentity = false
  ; p43CountCoincidencePromotedToActionIdentityIsFalse = refl
  }
