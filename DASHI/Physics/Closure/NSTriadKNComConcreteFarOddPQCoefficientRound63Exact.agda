module DASHI.Physics.Closure.NSTriadKNComConcreteFarOddPQCoefficientRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- ROUND 63 B0 FAR-COEFFICIENT FALSIFIER
--
-- Round62's shell-0 -> shell-3 witness was previously only a selector/support
-- witness.  Round63 upgrades it to an ACTUAL nonzero literal transport
-- coefficient on the same carrier.
--
--   p=(7,0,0), q=(1,1,0), k=(8,1,0)=p+q.
--
-- With the transverse constant y-unit advector used by the earlier active
-- test, q.a_p=1, hence T(k,q)=i.  At cutoff zero q is low and k is high, so
-- the literal odd-P/Q coefficient is exactly -i and is nonzero on every
-- nontrivial compatible RealField.
--
-- The authoritative strict Bony classifier places this triad in CC/comparable,
-- not HL.  Therefore the literal fifth Com kernel genuinely contains live
-- far triadic summands before any additional cancellation/localization theorem.
-- This rules out interpreting the raw fifth-cell kernel itself as an already
-- width-one operator.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportMatrixSkewRound40Exact as Matrix
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportCoefficientSkewRound40Exact as Coeff
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQKernelRound57Exact as Odd
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Concrete
import DASHI.Physics.Closure.NSTriadKNComRawHardLowPassCommonHatNoGoRound62Exact as Raw
import DASHI.Physics.Closure.NSTriadKNLiteralBonyInteractionRoutingRound63Exact as Routing

farInputDotYUnitIsOne :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  (unit : Concrete.UnitPreservingIntegerEmbedding F E) →
  Coeff.modeDot E Raw.farInput (Concrete.yUnit F) ≡ C3.complexOne F
farInputDotYUnitIsOne = Concrete.qDotYUnitIsOne

farTransportCoefficientIsI :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  (unit : Concrete.UnitPreservingIntegerEmbedding F E) →
  Matrix.transportEntryCoefficient E (Concrete.constantYAdvector F) Raw.farEntry
  ≡ C3.complexI F
farTransportCoefficientIsI {F = F} {E = E} unit
  rewrite farInputDotYUnitIsOne unit
        | Hermitian.complexMultiplyOneRight (C3.complexI F) = refl

literalFarOddPQCoefficientIsNegativeI :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  (unit : Concrete.UnitPreservingIntegerEmbedding F E) →
  Odd.literalOddPQEntryCoefficient
    (Concrete.selectorOnlyModel F) zero E
    (Concrete.constantYAdvector F) Raw.farEntry
  ≡ C3.complexNegate (C3.complexI F)
literalFarOddPQCoefficientIsNegativeI {F = F} {E = E} unit
  rewrite Raw.farOutputHighAtZero F
        | Raw.farInputLowAtZero F
        | farTransportCoefficientIsI unit = refl

literalFarOddPQCoefficientNonzero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  (unit : Concrete.UnitPreservingIntegerEmbedding F E) →
  (nontrivial : Concrete.NontrivialRealField F) →
  Odd.literalOddPQEntryCoefficient
    (Concrete.selectorOnlyModel F) zero E
    (Concrete.constantYAdvector F) Raw.farEntry
  ≢ C3.complexZero F
literalFarOddPQCoefficientNonzero unit nontrivial equality =
  Concrete.negativeImaginaryUnitNonzero nontrivial
    (trans (sym (literalFarOddPQCoefficientIsNegativeI unit)) equality)

farTriadAuthoritativelyComparable :
  Routing.round62FarWitnessIsCCNotHL ≡ true
farTriadAuthoritativelyComparable = refl

rawFifthComHasLiveFarCoefficient : Bool
rawFifthComHasLiveFarCoefficient = true

rawFifthComHasLiveFarCoefficientIsTrue :
  rawFifthComHasLiveFarCoefficient ≡ true
rawFifthComHasLiveFarCoefficientIsTrue = refl
