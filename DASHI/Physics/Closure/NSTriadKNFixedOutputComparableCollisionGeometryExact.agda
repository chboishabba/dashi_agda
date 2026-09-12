module DASHI.Physics.Closure.NSTriadKNFixedOutputComparableCollisionGeometryExact where

------------------------------------------------------------------------
-- PR #890 / TWO DISTINCT SAME-OUTPUT COMPARABLE INCIDENCES
--
-- This file supplies only the finite lattice geometry needed by the slot-
-- collision negative control.  It does NOT construct a Galerkin velocity
-- state and does NOT claim the two slot values coincide by itself.
--
-- Selected resonances:
--
--   alpha : (1,1,0) + (2,2,0) = (3,3,0)
--   beta  : (1,2,0) + (2,1,0) = (3,3,0)
--
-- Under the official max-norm dyadic policy with Csep = 3 both incidences are
-- in the literal CC/comparable class.  They are nevertheless distinct physical
-- incidences, so any later equality of their slot observables is a genuine
-- many-to-one carrier phenomenon rather than the swap quotient alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (ℤ; +_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNComparableResidualProducerBoundaryRound204Exact as R204

outputMode : Z3.FourierMode
outputMode = Z3.mode (+ 3) (+ 3) (+ 0)

alphaP alphaQ betaP betaQ : Z3.FourierMode
alphaP = Z3.mode (+ 1) (+ 1) (+ 0)
alphaQ = Z3.mode (+ 2) (+ 2) (+ 0)
betaP  = Z3.mode (+ 1) (+ 2) (+ 0)
betaQ  = Z3.mode (+ 2) (+ 1) (+ 0)

alphaIncidence betaIncidence : Physical.PhysicalTriadIncidence
alphaIncidence = Physical.physicalTriad alphaP alphaQ outputMode refl
betaIncidence  = Physical.physicalTriad betaP betaQ outputMode refl

alphaComparableCertificate :
  Support.TriadicClassCertificate alphaIncidence Support.CC
alphaComparableCertificate =
  Support.triadic-class-certificate
    refl
    (Scale.scaleClassificationSound Shell.literalDyadicShellPolicy alphaIncidence)

betaComparableCertificate :
  Support.TriadicClassCertificate betaIncidence Support.CC
betaComparableCertificate =
  Support.triadic-class-certificate
    refl
    (Scale.scaleClassificationSound Shell.literalDyadicShellPolicy betaIncidence)

alphaLocalizedComparable betaLocalizedComparable : R204.LocalizedComparableIncidence
alphaLocalizedComparable =
  R204.localizePhysicalComparable alphaIncidence alphaComparableCertificate
betaLocalizedComparable =
  R204.localizePhysicalComparable betaIncidence betaComparableCertificate

sameSelectedOutput :
  Physical.k alphaIncidence ≡ Physical.k betaIncidence
sameSelectedOutput = refl

oneNotTwo : (+ 1 : ℤ) ≡ + 2 → ⊥
oneNotTwo ()

incidencesDistinct : alphaIncidence ≡ betaIncidence → ⊥
incidencesDistinct equality =
  oneNotTwo
    (cong
      (λ tau → Z3.ky (Physical.p tau))
      equality)

record DistinctComparableSameOutputIncidences : Set where
  constructor distinct-comparable-same-output-incidences
  field
    alpha beta : R204.LocalizedComparableIncidence
    outputAgreement : R204.incidence alpha |> Physical.k ≡ R204.incidence beta |> Physical.k
    distinct : R204.incidence alpha ≡ R204.incidence beta → ⊥

open DistinctComparableSameOutputIncidences public

-- Keep the witness construction transparent rather than hiding it behind an
-- existential search.
distinctComparableSameOutputIncidences : DistinctComparableSameOutputIncidences
distinctComparableSameOutputIncidences =
  distinct-comparable-same-output-incidences
    alphaLocalizedComparable
    betaLocalizedComparable
    refl
    incidencesDistinct

roundConcreteDistinctComparableSameOutputGeometryClosed : Bool
roundConcreteDistinctComparableSameOutputGeometryClosed = true

roundConcreteDistinctComparableSameOutputSlotCollisionClosed : Bool
roundConcreteDistinctComparableSameOutputSlotCollisionClosed = false

roundConcreteDistinctComparableSameOutputGeometryClayPromotion : Bool
roundConcreteDistinctComparableSameOutputGeometryClayPromotion = false

roundConcreteDistinctComparableSameOutputGeometryClosedIsTrue :
  roundConcreteDistinctComparableSameOutputGeometryClosed ≡ true
roundConcreteDistinctComparableSameOutputGeometryClosedIsTrue = refl

roundConcreteDistinctComparableSameOutputSlotCollisionClosedIsFalse :
  roundConcreteDistinctComparableSameOutputSlotCollisionClosed ≡ false
roundConcreteDistinctComparableSameOutputSlotCollisionClosedIsFalse = refl
