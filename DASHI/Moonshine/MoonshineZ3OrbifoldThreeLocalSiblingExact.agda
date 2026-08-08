module DASHI.Moonshine.MoonshineZ3OrbifoldThreeLocalSiblingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Hsian-Yang Chen, Ching Hung Lam and Hiroki Shimakura,
-- "Z_3-orbifold construction of the Moonshine vertex operator algebra and
-- some maximal 3-local subgroups of the Monster",
-- Mathematische Zeitschrift 288 (2018), 75--100.
-- DOI: 10.1007/s00209-017-1878-z.
--
-- Toshiyuki Abe, Ching Hung Lam and Hiromichi Yamada,
-- "A remark on Z_p-orbifold constructions of the Moonshine vertex operator
-- algebra",
-- arXiv:1705.09022; no DOI assigned in this file.
--
-- DASHI CONTRIBUTION
--
-- Record the two different 3-local geometries constructed from the same
-- order-three Leech-lattice orbifold route:
--
--   3^(1+12).2.Suz:2
--   3^8.Omega_8^-(3).2.
--
-- They share a sourced orbifold origin and the exact 65610 refactorization,
-- but their kernels, quotient geometries and representation coordinates remain
-- different typed objects.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Moonshine.Monster3BHeisenbergMultiplicityExact as H
import DASHI.Moonshine.MonsterThreeLocalE8LeechBridgeExact as Existing

data OrbifoldOrigin : Set where
  fixedPointFreeOrderThreeLeechOrbifold : OrbifoldOrigin

data KernelGeometry : Set where
  extraspecialThreePowerOnePlusTwelve : KernelGeometry
  elementaryAbelianThreePowerEight : KernelGeometry

data QuotientGeometry : Set where
  suzukiNormalizerGeometry : QuotientGeometry
  omegaEightMinusGeometry : QuotientGeometry

data ThreeLocalSiblingName : Set where
  extraspecialSuzukiSibling : ThreeLocalSiblingName
  elementaryOmegaSibling : ThreeLocalSiblingName

record ThreeLocalSiblingShape (name : ThreeLocalSiblingName) : Set where
  constructor three-local-sibling-shape
  field
    origin : OrbifoldOrigin
    kernelGeometry : KernelGeometry
    quotientGeometry : QuotientGeometry
    kernelExponentCoordinate : Nat
    internalCoordinateRank : Nat
    multiplicityCoordinate : Nat
    representedSectorDimension : Nat
    representedSectorDimensionExact : representedSectorDimension ≡ 65610

open ThreeLocalSiblingShape public

extraspecialSuzukiShape :
  ThreeLocalSiblingShape extraspecialSuzukiSibling
extraspecialSuzukiShape =
  three-local-sibling-shape
    fixedPointFreeOrderThreeLeechOrbifold
    extraspecialThreePowerOnePlusTwelve
    suzukiNormalizerGeometry
    13 6 90 H.heisenbergMultiplicitySector
    H.heisenbergMultiplicitySectorIs65610

elementaryOmegaShape :
  ThreeLocalSiblingShape elementaryOmegaSibling
elementaryOmegaShape =
  three-local-sibling-shape
    fixedPointFreeOrderThreeLeechOrbifold
    elementaryAbelianThreePowerEight
    omegaEightMinusGeometry
    8 8 10 Existing.tenTimesThreePowerEight
    Existing.tenTimesThreePowerEightIs65610

siblingsShareOrbifoldOrigin :
  origin extraspecialSuzukiShape ≡ origin elementaryOmegaShape
siblingsShareOrbifoldOrigin = refl

siblingsShareRepresentedSectorDimension :
  representedSectorDimension extraspecialSuzukiShape
  ≡ representedSectorDimension elementaryOmegaShape
siblingsShareRepresentedSectorDimension =
  Existing.twoThreeLocalChartsShare65610

kernelGeometriesAreDistinct :
  kernelGeometry extraspecialSuzukiShape
  ≡ kernelGeometry elementaryOmegaShape → ⊥
kernelGeometriesAreDistinct ()

quotientGeometriesAreDistinct :
  quotientGeometry extraspecialSuzukiShape
  ≡ quotientGeometry elementaryOmegaShape → ⊥
quotientGeometriesAreDistinct ()

internalCoordinateRanksAreSixAndEight :
  internalCoordinateRank extraspecialSuzukiShape ≡ 6
  × internalCoordinateRank elementaryOmegaShape ≡ 8
internalCoordinateRanksAreSixAndEight = refl , refl

record ThreeLocalSiblingBoundary : Set where
  constructor three-local-sibling-boundary
  field
    commonOriginWitness :
      origin extraspecialSuzukiShape ≡ origin elementaryOmegaShape
    commonDimensionWitness :
      representedSectorDimension extraspecialSuzukiShape
      ≡ representedSectorDimension elementaryOmegaShape
    distinctKernelWitness :
      kernelGeometry extraspecialSuzukiShape
      ≡ kernelGeometry elementaryOmegaShape → ⊥
    dimensionEqualityConstructsGroupIsomorphism : Bool
    dimensionEqualityConstructsGroupIsomorphismIsFalse :
      dimensionEqualityConstructsGroupIsomorphism ≡ false
    commonOrbifoldOriginConstructsRepresentationIntertwiner : Bool
    commonOrbifoldOriginConstructsRepresentationIntertwinerIsFalse :
      commonOrbifoldOriginConstructsRepresentationIntertwiner ≡ false

canonicalThreeLocalSiblingBoundary : ThreeLocalSiblingBoundary
canonicalThreeLocalSiblingBoundary =
  three-local-sibling-boundary
    siblingsShareOrbifoldOrigin
    siblingsShareRepresentedSectorDimension
    kernelGeometriesAreDistinct
    false refl
    false refl
