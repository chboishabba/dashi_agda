module DASHI.Moonshine.GradedVOAHomogeneousLinearRealisationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CALIBRATION
--
-- Victor G. Kac, Vertex Algebras for Beginners, 2nd ed., AMS, 1998.
-- No DOI asserted here for the book.
--
-- Richard E. Borcherds,
-- Monstrous moonshine and monstrous Lie superalgebras.
-- DOI: 10.1007/BF01232032.
--
-- Jean-Pierre Serre, Linear Representations of Finite Groups.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- `GradedVertexOperatorAlgebraBoundary` owns linear-looking operations on the
-- TOTAL VOA carrier, but its homogeneous grades are bare Sets and both
-- `gradingCompatibility` and `homogeneousCarrierAgreement` are opaque proof
-- slots.  They cannot be used as if they were explicit subspace maps.
--
-- This owner states the missing proof-bearing bridge for one grade without
-- changing the existing VOA API: the exact grade representation receives the
-- generic linear-endomorphism realisation, its vector carrier is identified
-- two-sidedly with the exact homogeneous carrier, and the grade injection into
-- the total VOA carrier is required to preserve zero/add/scalar operations.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as GVOA
import DASHI.Moonshine.GradedRepresentationLinearRealisationExact as LinearRep

------------------------------------------------------------------------
-- One proof-bearing homogeneous linear grade.
------------------------------------------------------------------------

record HomogeneousGradeLinearRealisation
    {G K : Set}
    (actionData : GVOA.VOAWithGroupAction G K) : Setω where
  field
    grade : Nat

    linearEndomorphismRealisation :
      LinearRep.LinearEndomorphismRealisation
        (GVOA.group actionData)
        (GR.grade (GVOA.gradedRepresentation actionData) grade)

    toHomogeneous :
      Linear.Vector
        (LinearRep.linearCarrier linearEndomorphismRealisation) →
      GVOA.Homogeneous (GVOA.voa actionData) grade

    fromHomogeneous :
      GVOA.Homogeneous (GVOA.voa actionData) grade →
      Linear.Vector
        (LinearRep.linearCarrier linearEndomorphismRealisation)

    homogeneousAfterLinear :
      (v : Linear.Vector
        (LinearRep.linearCarrier linearEndomorphismRealisation)) →
      fromHomogeneous (toHomogeneous v) ≡ v

    linearAfterHomogeneous :
      (v : GVOA.Homogeneous (GVOA.voa actionData) grade) →
      toHomogeneous (fromHomogeneous v) ≡ v

    scalarToVOA :
      Linear.Scalar
        (LinearRep.linearCarrier linearEndomorphismRealisation) → K

    zeroCompatibility :
      GVOA.injectGrade (GVOA.voa actionData) grade
        (toHomogeneous
          (Linear.zero
            (LinearRep.linearCarrier linearEndomorphismRealisation)))
      ≡ GVOA.zero (GVOA.voa actionData)

    additionCompatibility :
      (left right : Linear.Vector
        (LinearRep.linearCarrier linearEndomorphismRealisation)) →
      GVOA.injectGrade (GVOA.voa actionData) grade
        (toHomogeneous
          (Linear._+_
            (LinearRep.linearCarrier linearEndomorphismRealisation)
            left right))
      ≡ GVOA.add (GVOA.voa actionData)
          (GVOA.injectGrade (GVOA.voa actionData) grade
            (toHomogeneous left))
          (GVOA.injectGrade (GVOA.voa actionData) grade
            (toHomogeneous right))

    scalingCompatibility :
      (scalar : Linear.Scalar
        (LinearRep.linearCarrier linearEndomorphismRealisation)) →
      (v : Linear.Vector
        (LinearRep.linearCarrier linearEndomorphismRealisation)) →
      GVOA.injectGrade (GVOA.voa actionData) grade
        (toHomogeneous
          (Linear._·_
            (LinearRep.linearCarrier linearEndomorphismRealisation)
            scalar v))
      ≡ GVOA.scalarMultiply (GVOA.voa actionData)
          (scalarToVOA scalar)
          (GVOA.injectGrade (GVOA.voa actionData) grade
            (toHomogeneous v))

open HomogeneousGradeLinearRealisation public

------------------------------------------------------------------------
-- WrongType / non-promotion boundary.
------------------------------------------------------------------------

data OpaqueGradingCompatibilityCreatesLinearGrade : Set where
data HomogeneousCarrierAgreementCreatesLinearGrade : Set where
data GradeDimensionCreatesLinearGrade : Set where
data TraceCreatesLinearGrade : Set where

opaqueGradingCompatibilityDoesNotCreateLinearGrade :
  OpaqueGradingCompatibilityCreatesLinearGrade → ⊥
opaqueGradingCompatibilityDoesNotCreateLinearGrade ()

homogeneousAgreementDoesNotCreateLinearGrade :
  HomogeneousCarrierAgreementCreatesLinearGrade → ⊥
homogeneousAgreementDoesNotCreateLinearGrade ()

gradeDimensionDoesNotCreateLinearGrade : GradeDimensionCreatesLinearGrade → ⊥
gradeDimensionDoesNotCreateLinearGrade ()

traceDoesNotCreateLinearGrade : TraceCreatesLinearGrade → ⊥
traceDoesNotCreateLinearGrade ()

------------------------------------------------------------------------
-- Source / classification coordinates.
------------------------------------------------------------------------

borcherdsDOI : String
borcherdsDOI = "10.1007/BF01232032"

serreDOI : String
serreDOI = "10.1007/978-1-4684-9458-7"

groupRepresentationQID : String
groupRepresentationQID = "Q1055807"

groupRepresentationDewey : String
groupRepresentationDewey = "512.22"

oeisRole : String
oeisRole = "not applicable: homogeneous linear-grade structure is not integer-sequence evidence"

------------------------------------------------------------------------
-- Boundary state.
------------------------------------------------------------------------

record HomogeneousGradeLinearBoundary : Set where
  constructor homogeneous-grade-linear-boundary
  field
    totalVOAOperationsAlreadyOwned : Bool
    gradeRepresentationAlreadyOwned : Bool
    opaqueCompatibilityInsufficient : Bool
    explicitTwoSidedGradeCarrierRequired : Bool
    explicitOperationCompatibilityRequired : Bool
    genericGradeLinearRealisationInhabitedHere : Bool
open HomogeneousGradeLinearBoundary public

canonicalHomogeneousGradeLinearBoundary : HomogeneousGradeLinearBoundary
canonicalHomogeneousGradeLinearBoundary = homogeneous-grade-linear-boundary
  true true true true true false
