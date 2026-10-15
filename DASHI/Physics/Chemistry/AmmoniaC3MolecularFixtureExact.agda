module DASHI.Physics.Chemistry.AmmoniaC3MolecularFixtureExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.C3FourierConjugationExact as Fourier

------------------------------------------------------------------------
-- Same-object finite molecular-symmetry fixture.
--
-- NIST CCCBDB records experimental NH3 geometry with point group C3v and
-- symmetry number 3.  This module extracts only the threefold permutation
-- structure needed by the generic chemistry-C3 consumer.  It does NOT claim
-- that the three hydrogen labels are the full electronic molecular state.
------------------------------------------------------------------------

nistCCCBDBAmmoniaGeometry : Source.AttributedSource
nistCCCBDBAmmoniaGeometry =
  Source.mkNoDOISource
    "National Institute of Standards and Technology"
    "CCCBDB experimental geometry data for NH3 (Ammonia)"
    "NIST Computational Chemistry Comparison and Benchmark Database"
    "2026"
    "https://cccbdb.nist.gov/expgeom2x.asp?casno=7664417&charge=0"
    Source.institutionalSource
    "institutional compilation for the experimental ammonia geometry, point group C3v, symmetry number 3, equal N-H geometry coordinates and source references; not a DASHI electronic-structure calculation"
    Source.publicAttribution

nistAmmoniaSpectroscopy : Source.AttributedSource
nistAmmoniaSpectroscopy =
  Source.mkNoDOISource
    "National Institute of Standards and Technology"
    "Ammonia vibrational and symmetry data"
    "NIST Chemistry WebBook / NSRDS molecular spectra compilation"
    "2026"
    "https://webbook.nist.gov/cgi/cbook.cgi?ID=C7664417&Mask=1D80"
    Source.institutionalSource
    "institutional spectroscopy compilation recording C3v symmetry and symmetry-resolved vibrational data; used only as a molecular-symmetry observation source"
    Source.publicAttribution

data HydrogenLabel : Set where
  h1 h2 h3 : HydrogenLabel

rotateH : HydrogenLabel → HydrogenLabel
rotateH h1 = h2
rotateH h2 = h3
rotateH h3 = h1

rotateHThreeTimes : (h : HydrogenLabel) →
  rotateH (rotateH (rotateH h)) ≡ h
rotateHThreeTimes h1 = refl
rotateHThreeTimes h2 = refl
rotateHThreeTimes h3 = refl

data AmmoniaC3Phase : Set where
  invariant zeta zetaSquared : AmmoniaC3Phase

phaseFourierRow : AmmoniaC3Phase → Fourier.FourierRow
phaseFourierRow invariant = Fourier.chi0
phaseFourierRow zeta = Fourier.chi1
phaseFourierRow zetaSquared = Fourier.chi2

zetaConjugatesToZetaSquared :
  Fourier.conjugateRow (phaseFourierRow zeta)
  ≡ phaseFourierRow zetaSquared
zetaConjugatesToZetaSquared = Fourier.chi1ConjugateIsChi2

record AmmoniaC3Fixture : Set where
  constructor ammoniaC3Fixture
  field
    formula : String
    pointGroup : String
    symmetryNumber : Nat
    hydrogenCount : Nat
    experimentalC3GeometryPaid : Bool
    equalNHBondGeometryReported : Bool
    c3PermutationCyclePaid : Bool
    exactFourierCarrierAttached : Bool
    geometrySource : Source.AttributedSource
    spectroscopySource : Source.AttributedSource

open AmmoniaC3Fixture public

canonicalAmmoniaC3Fixture : AmmoniaC3Fixture
canonicalAmmoniaC3Fixture =
  ammoniaC3Fixture
    "NH3"
    "C3v"
    3
    3
    true
    true
    true
    true
    nistCCCBDBAmmoniaGeometry
    nistAmmoniaSpectroscopy

------------------------------------------------------------------------
-- Inversion provides a useful same-molecule transition fixture, but it is not
-- a reactants -> products chemical reaction.  The planar D3h transition-state
-- description therefore cannot pay the reaction/products/byproducts frontier.
------------------------------------------------------------------------

data AmmoniaGeometryClass : Set where
  pyramidalUp pyramidalDown planarInversionConfiguration : AmmoniaGeometryClass

record AmmoniaInversionFixture : Set where
  constructor ammoniaInversionFixture
  field
    sourceGeometry : AmmoniaGeometryClass
    transitionGeometry : AmmoniaGeometryClass
    targetGeometry : AmmoniaGeometryClass
    sameMolecularFormula : Bool
    sameAtomInventory : Bool
    inversionCoordinateRequired : Bool
    spectroscopyAuthorityRetained : Bool

canonicalAmmoniaInversionFixture : AmmoniaInversionFixture
canonicalAmmoniaInversionFixture =
  ammoniaInversionFixture
    pyramidalUp
    planarInversionConfiguration
    pyramidalDown
    true true true true

record AmmoniaC3Boundary : Set where
  constructor ammoniaC3Boundary
  field
    experimentalGeometryEstablishesC3MolecularFixture : Bool
    experimentalGeometryEstablishesC3MolecularFixtureIsTrue :
      experimentalGeometryEstablishesC3MolecularFixture ≡ true

    hydrogenPermutationIsFullElectronicWavefunction : Bool
    hydrogenPermutationIsFullElectronicWavefunctionIsFalse :
      hydrogenPermutationIsFullElectronicWavefunction ≡ false

    fullElectronicC3RepresentationPaid : Bool
    fullElectronicC3RepresentationPaidIsFalse :
      fullElectronicC3RepresentationPaid ≡ false

    ammoniaInversionIsProductsByproductsReaction : Bool
    ammoniaInversionIsProductsByproductsReactionIsFalse :
      ammoniaInversionIsProductsByproductsReaction ≡ false

    inversionFixturePaysReactionEnergeticsAndKinetics : Bool
    inversionFixturePaysReactionEnergeticsAndKineticsIsFalse :
      inversionFixturePaysReactionEnergeticsAndKinetics ≡ false

    c3MolecularGeometryImpliesMonsterModule : Bool
    c3MolecularGeometryImpliesMonsterModuleIsFalse :
      c3MolecularGeometryImpliesMonsterModule ≡ false

canonicalAmmoniaC3Boundary : AmmoniaC3Boundary
canonicalAmmoniaC3Boundary =
  ammoniaC3Boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
