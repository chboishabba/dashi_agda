module DASHI.Physics.Chemistry.AmmoniaC3RegularRepresentationExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AmmoniaC3ElectronicSymmetryExact as NH3
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as CycloLA
import DASHI.Moonshine.Monster3BC3RepresentationRingEvaluationExact as Rep
import DASHI.Wikimedia.IbrahimC3ZetaRegularCharacterOEISQuantumGRBidiExact as MonsterZeta

------------------------------------------------------------------------
-- NH3 A1 PLUS E -> ONE REGULAR C3 BLOCK
--
-- Existing NH3 symmetry gives
--
--   A1|C3 = 1
--   E |C3 = zeta + zeta^2.
--
-- Hence A1 + E restricts to exactly one copy of Reg(C3).  This is the same
-- representation-theoretic phase cycle used by the Monster-3B regular bulk,
-- but the multiplicities and state spaces are radically different:
--
--   NH3 selected block : 1 * Reg(C3)
--   Monster W|C3       : 65610 * Reg(C3) + 53 * 1.
--
-- The common motif is exact.  It is not a same-object module identification.
------------------------------------------------------------------------

phaseAmplitude : NH3.ElectronicC3Phase → C3.Cyclotomic3
phaseAmplitude NH3.invariant = C3.one
phaseAmplitude NH3.zeta = C3.zeta
phaseAmplitude NH3.zetaSquared = C3.zetaSquared

zeroAmplitude : C3.Cyclotomic3
zeroAmplitude = C3.zero

ammoniaA1Phase : C3.Cyclotomic3
ammoniaA1Phase = phaseAmplitude NH3.invariant

ammoniaEPlusPhase : C3.Cyclotomic3
ammoniaEPlusPhase = phaseAmplitude NH3.zeta

ammoniaEMinusPhase : C3.Cyclotomic3
ammoniaEMinusPhase = phaseAmplitude NH3.zetaSquared

ammoniaA1PlusEGeneratorAmplitude : C3.Cyclotomic3
ammoniaA1PlusEGeneratorAmplitude =
  CycloLA.add ammoniaA1Phase
    (CycloLA.add ammoniaEPlusPhase ammoniaEMinusPhase)

ammoniaA1PlusEGeneratorCancels :
  ammoniaA1PlusEGeneratorAmplitude ≡ zeroAmplitude
ammoniaA1PlusEGeneratorCancels = MonsterZeta.regularC3PhaseCycleCancels

record RestrictedRegularC3Block : Set where
  constructor restrictedRegularC3Block
  field
    trivialPhase : NH3.ElectronicC3Phase
    positivePhase : NH3.ElectronicC3Phase
    negativePhase : NH3.ElectronicC3Phase
    generatorAmplitude : C3.Cyclotomic3
    generatorAmplitudeCancels : generatorAmplitude ≡ C3.zero
    scope : String

open RestrictedRegularC3Block public

canonicalAmmoniaA1PlusERegularBlock : RestrictedRegularC3Block
canonicalAmmoniaA1PlusERegularBlock =
  restrictedRegularC3Block
    NH3.invariant
    NH3.zeta
    NH3.zetaSquared
    ammoniaA1PlusEGeneratorAmplitude
    ammoniaA1PlusEGeneratorCancels
    "DASHI reconstruction of the restriction (A1 plus E)|C3 = 1 plus zeta plus zeta^2 = Reg(C3); no Monster state-space identification is imported"

monsterRegularBlockMultiplicity : Nat
monsterRegularBlockMultiplicity = Rep.regularBlockMultiplicity

monsterResidualMultiplicity : Nat
monsterResidualMultiplicity = Rep.residualMultiplicity Rep.monster3BCharacter

monsterRegularBlockMultiplicityIs65610 : monsterRegularBlockMultiplicity ≡ 65610
monsterRegularBlockMultiplicityIs65610 = Rep.regularBlockMultiplicityIs65610

monsterResidualMultiplicityIs53 : monsterResidualMultiplicity ≡ 53
monsterResidualMultiplicityIs53 = Rep.monster3BResidualIs53

monsterRegularBulkCancellation :
  CycloLA.add
    (C3.multiply C3.one (C3.embedRational 65610))
    (CycloLA.add
      (C3.multiply C3.zeta (C3.embedRational 65610))
      (C3.multiply C3.zetaSquared (C3.embedRational 65610)))
  ≡ C3.zero
monsterRegularBulkCancellation = MonsterZeta.regularC3CancellationAt65610

record RegularC3CrossDomainBoundary : Set where
  constructor regularC3CrossDomainBoundary
  field
    nh3A1PlusERestrictsToOneRegularC3 : Bool
    nh3A1PlusERestrictsToOneRegularC3IsTrue :
      nh3A1PlusERestrictsToOneRegularC3 ≡ true
    sameCyclotomicCancellationLawUsed : Bool
    sameCyclotomicCancellationLawUsedIsTrue :
      sameCyclotomicCancellationLawUsed ≡ true
    monsterRegularMultiplicity65610SeparatelyPaid : Bool
    monsterRegularMultiplicity65610SeparatelyPaidIsTrue :
      monsterRegularMultiplicity65610SeparatelyPaid ≡ true
    monsterResidual53SeparatelyPaid : Bool
    monsterResidual53SeparatelyPaidIsTrue :
      monsterResidual53SeparatelyPaid ≡ true
    nh3RegularMultiplicityEqualsMonsterMultiplicity : Bool
    nh3RegularMultiplicityEqualsMonsterMultiplicityIsFalse :
      nh3RegularMultiplicityEqualsMonsterMultiplicity ≡ false
    sameRegularC3MotifCreatesMonsterModule : Bool
    sameRegularC3MotifCreatesMonsterModuleIsFalse :
      sameRegularC3MotifCreatesMonsterModule ≡ false
    sameRegularC3MotifCreatesPhysicalSameObject : Bool
    sameRegularC3MotifCreatesPhysicalSameObjectIsFalse :
      sameRegularC3MotifCreatesPhysicalSameObject ≡ false
    interpretation : String

open RegularC3CrossDomainBoundary public

canonicalRegularC3CrossDomainBoundary : RegularC3CrossDomainBoundary
canonicalRegularC3CrossDomainBoundary =
  regularC3CrossDomainBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "NH3 A1 plus E is an exact multiplicity-one regular-C3 motif. Monster-3B contains 65610 regular copies plus a 53-dimensional trivial residual. The shared representation motif licenses common C3/character algebra, not a same-state or physical Monster identification."
