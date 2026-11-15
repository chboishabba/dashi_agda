module DASHI.Cognition.Teleodynamics.ExceptionalPriorFamilyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.Teleodynamics.GeometricLearnerPriorExact as Prior
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as AF

------------------------------------------------------------------------
-- EXCEPTIONAL-PRIOR EXPERIMENT CONFIGURATION
--
-- Two modes remain separate:
--   rootCodebookMode        : finite root systems in their rank-dimensional
--                             root spaces;
--   representationCarrierMode : candidate representation/state carriers.
--
-- The rows below are experiment configuration data.  They do not identify a
-- transformer's hidden state with a named exceptional representation.
------------------------------------------------------------------------

data ExceptionalFamily : Set where
  G2 F4 E6 E7 E8 : ExceptionalFamily

data PriorMode : Set where
  rootCodebookMode : PriorMode
  representationCarrierMode : PriorMode

record ExceptionalRootPrior : Set where
  constructor exceptionalRootPrior
  field
    family : ExceptionalFamily
    rootRank : Nat
    rootCount : Nat
    sourceLabel : String
    actionEstablished : Bool
    equivarianceEstablished : Bool

open ExceptionalRootPrior public

g2RootPrior f4RootPrior e6RootPrior e7RootPrior e8RootPrior : ExceptionalRootPrior
g2RootPrior = exceptionalRootPrior G2 2 12 "standard G2 root-system experiment row" false false
f4RootPrior = exceptionalRootPrior F4 4 48 "standard F4 root-system experiment row" false false
e6RootPrior = exceptionalRootPrior E6 6 72 "standard E6 root-system experiment row" false false
e7RootPrior = exceptionalRootPrior E7 7 126 "standard E7 root-system experiment row" false false
e8RootPrior = exceptionalRootPrior E8 8 240 "DASHI E8 finite-root owner / LILA-E8 comparison row" false false

record ExceptionalRepresentationCarrier : Set where
  constructor exceptionalRepresentationCarrier
  field
    familyR : ExceptionalFamily
    representationDimension : Nat
    carrierLabel : String
    existingShapeOwnerLabel : String
    actualGroupActionEstablished : Bool

open ExceptionalRepresentationCarrier public

f4TracelessAlbertCarrier : ExceptionalRepresentationCarrier
f4TracelessAlbertCarrier =
  exceptionalRepresentationCarrier F4 AF.tracelessAlbertDimension
    "traceless Albert shape"
    "ExceptionalAlbertFreudenthalResidualExact.J0"
    false

e6AlbertCarrier : ExceptionalRepresentationCarrier
e6AlbertCarrier =
  exceptionalRepresentationCarrier E6 AF.albertDimension
    "Albert 27 shape"
    "ExceptionalAlbertFreudenthalResidualExact.Albert27"
    false

e7FreudenthalCarrier : ExceptionalRepresentationCarrier
e7FreudenthalCarrier =
  exceptionalRepresentationCarrier E7 AF.freudenthalDimension
    "Freudenthal 56 shape"
    "ExceptionalAlbertFreudenthalResidualExact.Freudenthal56"
    false

record ExceptionalFamilyBoundary : Set where
  constructor exceptionalFamilyBoundary
  field
    rootRankEqualsRepresentationDimension : Bool
    dimensionMatchCreatesAction : Bool
    codebookMatchCreatesIntertwiner : Bool
    e8Adjoint248CarrierConstructedHere : Bool

canonicalExceptionalFamilyBoundary : ExceptionalFamilyBoundary
canonicalExceptionalFamilyBoundary =
  exceptionalFamilyBoundary false false false false

exceptionalRootPriorAsGeneric : ExceptionalRootPrior → Prior.GeometricLearnerPrior
exceptionalRootPriorAsGeneric p =
  Prior.geometricLearnerPrior
    "exceptional root-codebook experiment prior"
    "rank-dimensional root space"
    "application-supplied hidden projection"
    (sourceLabel p)
    "application-supplied comparison geometry"
    "optional soft codebook quantizer"
    "optional root-conditioned attention bias"
    "optional codebook observer"
    "DASHI experiment configuration; no group-action promotion"
    true true false false
