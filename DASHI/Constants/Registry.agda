module DASHI.Constants.Registry where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Physics.Closure.PhotonuclearEmpiricalConstantsRegistry as PECR

------------------------------------------------------------------------
-- Repo-wide constants registry owner.
--
-- This module is intentionally conservative: it does not introduce a new
-- physics claim or duplicate empirical constants. It only names the existing
-- photonuclear empirical registry as the current repo-wide linked constant
-- surface, with explicit provenance and boundary tags.

data RegistryBoundary : Set where
  referenceOnly : RegistryBoundary
  noPhysicsClaim : RegistryBoundary

data AuthoritySourceKind : Set where
  siDefinitionAuthority : AuthoritySourceKind
  codataConstantsAuthority : AuthoritySourceKind
  pdgParticleDataAuthority : AuthoritySourceKind
  nistChemistryAuthority : AuthoritySourceKind
  clinicalValidityAuthority : AuthoritySourceKind
  neuroimagingProvenanceAuthority : AuthoritySourceKind
  connectomeDatasetAuthority : AuthoritySourceKind
  fairDataProvenanceAuthority : AuthoritySourceKind
  providerReceiptAuthority : AuthoritySourceKind
  runtimeReceiptAuthority : AuthoritySourceKind

data ConstantAuthorityClass : Set where
  exactSIDefiningConstant : ConstantAuthorityClass
  exactSIDerivedConstant : ConstantAuthorityClass
  measuredCODATAInput : ConstantAuthorityClass
  domainReferenceInput : ConstantAuthorityClass
  modelLawInput : ConstantAuthorityClass
  repoInternalProxyInput : ConstantAuthorityClass

record KnownConstantSlot : Set₁ where
  field
    constantLabel : String
    symbol : String
    value : String
    unit : String
    authorityClass : ConstantAuthorityClass
    authoritySource : String
    targetLanes : List String
    boundaryNotes : List String

open KnownConstantSlot public

record AuthoritySourceSlot : Set₁ where
  field
    authorityLabel : String
    authorityKind : AuthoritySourceKind
    sourceUri : String
    appliesTo : List String
    boundaryNotes : List String

open AuthoritySourceSlot public

mkAuthority :
  String →
  AuthoritySourceKind →
  String →
  List String →
  List String →
  AuthoritySourceSlot
mkAuthority label kind uri lanes notes =
  record
    { authorityLabel = label
    ; authorityKind = kind
    ; sourceUri = uri
    ; appliesTo = lanes
    ; boundaryNotes = notes
    }

mkConstant :
  String →
  String →
  String →
  String →
  ConstantAuthorityClass →
  String →
  List String →
  List String →
  KnownConstantSlot
mkConstant label symbol value unit authority source lanes notes =
  record
    { constantLabel = label
    ; symbol = symbol
    ; value = value
    ; unit = unit
    ; authorityClass = authority
    ; authoritySource = source
    ; targetLanes = lanes
    ; boundaryNotes = notes
    }

record KnownLawSlot : Set₁ where
  field
    lawLabel : String
    lawFamily : String
    canonicalForm : String
    targetSurface : String
    ownerOrAdapter : String
    authorityClass : ConstantAuthorityClass
    requiredAdapters : List String
    boundaryNotes : List String

open KnownLawSlot public

mkLaw :
  String →
  String →
  String →
  String →
  String →
  ConstantAuthorityClass →
  List String →
  List String →
  KnownLawSlot
mkLaw label family form surface owner authority adapters notes =
  record
    { lawLabel = label
    ; lawFamily = family
    ; canonicalForm = form
    ; targetSurface = surface
    ; ownerOrAdapter = owner
    ; authorityClass = authority
    ; requiredAdapters = adapters
    ; boundaryNotes = notes
    }

record ConstantsRegistryLink : Set₁ where
  field
    linkLabel : String
    sourceModule : String
    sourceRegistry : PECR.PhotonuclearConstantsRegistry
    sourceBoundary : PECR.ClaimBoundary
    provenanceNotes : List String

open ConstantsRegistryLink public

linkedRegistryEntryCount : ConstantsRegistryLink → Nat
linkedRegistryEntryCount link =
  PECR.registryEntryCount (ConstantsRegistryLink.sourceRegistry link)

record ConstantsRegistry : Set₁ where
  field
    registryLabel : String
    registryBoundary : RegistryBoundary
    linkedRegistry : ConstantsRegistryLink
    linkedRegistryCount : Nat
    linkedEntryCount : Nat
    exactSIDefiningConstants : List KnownConstantSlot
    exactSIDerivedConstants : List KnownConstantSlot
    measuredPhysicsConstantSlots : List KnownConstantSlot
    physicsLawSlots : List KnownLawSlot
    chemistryLawSlots : List KnownLawSlot
    biologyLawSlots : List KnownLawSlot
    empiricalRuntimeLawSlots : List KnownLawSlot
    authoritySourceSlots : List AuthoritySourceSlot
    constantCarrierDerived : Bool
    constantCarrierDerivedIsFalse : constantCarrierDerived ≡ false
    physicalLawDerived : Bool
    physicalLawDerivedIsFalse : physicalLawDerived ≡ false
    calibrationPromoted : Bool
    calibrationPromotedIsFalse : calibrationPromoted ≡ false
    empiricalAdequacyAccepted : Bool
    empiricalAdequacyAcceptedIsFalse : empiricalAdequacyAccepted ≡ false
    externalInputOnly : Bool
    externalInputOnlyIsTrue : externalInputOnly ≡ true
    noGlobalClaim : RegistryBoundary

open ConstantsRegistry public

canonicalPhotonuclearLink : ConstantsRegistryLink
canonicalPhotonuclearLink = record
  { linkLabel = "photonuclear-empirical"
  ; sourceModule =
      "DASHI.Physics.Closure.PhotonuclearEmpiricalConstantsRegistry"
  ; sourceRegistry = PECR.photonuclearConstantsRegistry
  ; sourceBoundary = PECR.notPhysicsClaim
  ; provenanceNotes =
      "current repo-side empirical constants owner"
      ∷ "registry is linked, not re-derived"
      ∷ "no new physics claim introduced"
      ∷ []
  }

canonicalSIDefiningConstants : List KnownConstantSlot
canonicalSIDefiningConstants =
  mkConstant
    "caesium-133 hyperfine transition frequency"
    "Delta nu Cs"
    "9192631770"
    "Hz"
    exactSIDefiningConstant
    "BIPM SI defining constants / NIST SI base-unit definitions"
    ( "time/frequency"
    ∷ "measurement"
    ∷ "runtime clock provenance"
    ∷ []
    )
    ( "exact by SI definition"
    ∷ "unit definition only; no dynamics theorem"
    ∷ []
    )
  ∷ mkConstant
    "speed of light in vacuum"
    "c"
    "299792458"
    "m s^-1"
    exactSIDefiningConstant
    "BIPM SI defining constants / NIST SI base-unit definitions"
    ( "Maxwell"
    ∷ "relativity"
    ∷ "GR"
    ∷ "QFT"
    ∷ "empirical calibration"
    ∷ []
    )
    ( "exact by SI definition"
    ∷ "does not by itself prove Lorentzian recovery or Maxwell equations"
    ∷ []
    )
  ∷ mkConstant
    "Planck constant"
    "h"
    "6.62607015e-34"
    "J s"
    exactSIDefiningConstant
    "BIPM SI defining constants / NIST SI base-unit definitions"
    ( "Schrodinger"
    ∷ "QFT"
    ∷ "quantum measurement"
    ∷ "chemistry spectra"
    ∷ []
    )
    ( "exact by SI definition"
    ∷ "hbar and quantum dynamics still require representation adapters"
    ∷ []
    )
  ∷ mkConstant
    "elementary charge"
    "e"
    "1.602176634e-19"
    "C"
    exactSIDefiningConstant
    "BIPM SI defining constants / NIST SI base-unit definitions"
    ( "Maxwell"
    ∷ "electrochemistry"
    ∷ "Standard Model sector"
    ∷ "biology membrane potentials"
    ∷ []
    )
    ( "exact by SI definition"
    ∷ "charge source and representation laws remain adapters"
    ∷ []
    )
  ∷ mkConstant
    "Boltzmann constant"
    "k_B"
    "1.380649e-23"
    "J K^-1"
    exactSIDefiningConstant
    "BIPM SI defining constants / NIST SI base-unit definitions"
    ( "thermodynamics"
    ∷ "statistical mechanics"
    ∷ "chemistry kinetics"
    ∷ "biology energetics"
    ∷ []
    )
    ( "exact by SI definition"
    ∷ "thermodynamic model validity remains separate"
    ∷ []
    )
  ∷ mkConstant
    "Avogadro constant"
    "N_A"
    "6.02214076e23"
    "mol^-1"
    exactSIDefiningConstant
    "BIPM SI defining constants / NIST SI base-unit definitions"
    ( "chemistry stoichiometry"
    ∷ "molecular biology"
    ∷ "cross-scale simulator"
    ∷ []
    )
    ( "exact by SI definition"
    ∷ "molecular identity and reaction model authority remain separate"
    ∷ []
    )
  ∷ mkConstant
    "luminous efficacy at 540 THz"
    "K_cd"
    "683"
    "lm W^-1"
    exactSIDefiningConstant
    "BIPM SI defining constants / NIST SI base-unit definitions"
    ( "measurement"
    ∷ "biology vision/retina observations"
    ∷ []
    )
    ( "exact by SI definition"
    ∷ "photometric and biological response models remain adapters"
    ∷ []
    )
  ∷ []

canonicalSIDerivedConstants : List KnownConstantSlot
canonicalSIDerivedConstants =
  mkConstant
    "reduced Planck constant"
    "hbar"
    "h / (2 pi)"
    "J s"
    exactSIDerivedConstant
    "derived from exact SI Planck constant and mathematical pi"
    ( "Schrodinger"
    ∷ "QFT"
    ∷ "spectroscopy"
    ∷ []
    )
    ( "exact as an expression in h and pi"
    ∷ "numeric decimal use still requires chosen rounding policy"
    ∷ []
    )
  ∷ mkConstant
    "molar gas constant"
    "R"
    "N_A k_B"
    "J mol^-1 K^-1"
    exactSIDerivedConstant
    "derived from exact SI Avogadro and Boltzmann constants"
    ( "thermodynamics"
    ∷ "chemistry kinetics"
    ∷ "biology energetics"
    ∷ []
    )
    ( "exact as an expression in N_A and k_B"
    ∷ "model validity remains separate"
    ∷ []
    )
  ∷ mkConstant
    "Faraday constant"
    "F"
    "N_A e"
    "C mol^-1"
    exactSIDerivedConstant
    "derived from exact SI Avogadro constant and elementary charge"
    ( "electrochemistry"
    ∷ "membrane biology"
    ∷ "empirical calibration"
    ∷ []
    )
    ( "exact as an expression in N_A and e"
    ∷ "activity and membrane model validity remain separate"
    ∷ []
    )
  ∷ mkConstant
    "Josephson constant"
    "K_J"
    "2 e / h"
    "Hz V^-1"
    exactSIDerivedConstant
    "derived from exact SI elementary charge and Planck constant"
    ( "quantum electrical metrology"
    ∷ "voltage calibration"
    ∷ "runtime measurement provenance"
    ∷ []
    )
    ( "exact as an expression in e and h"
    ∷ "Josephson-device realization and calibration remain adapters"
    ∷ []
    )
  ∷ mkConstant
    "von Klitzing constant"
    "R_K"
    "h / e^2"
    "ohm"
    exactSIDerivedConstant
    "derived from exact SI Planck constant and elementary charge"
    ( "quantum Hall metrology"
    ∷ "resistance calibration"
    ∷ "condensed matter adapter targets"
    ∷ []
    )
    ( "exact as an expression in h and e"
    ∷ "quantum Hall realization and material conditions remain adapters"
    ∷ []
    )
  ∷ mkConstant
    "conductance quantum"
    "G_0"
    "2 e^2 / h"
    "S"
    exactSIDerivedConstant
    "derived from exact SI elementary charge and Planck constant"
    ( "quantum transport"
    ∷ "mesoscopic conductance"
    ∷ "QFT/condensed matter adapter targets"
    ∷ []
    )
    ( "exact as an expression in e and h"
    ∷ "transport realization and degeneracy assumptions remain adapters"
    ∷ []
    )
  ∷ mkConstant
    "magnetic flux quantum"
    "Phi_0"
    "h / (2 e)"
    "Wb"
    exactSIDerivedConstant
    "derived from exact SI Planck constant and elementary charge"
    ( "superconductivity"
    ∷ "gauge/flux quantisation targets"
    ∷ "quantum metrology"
    ∷ []
    )
    ( "exact as an expression in h and e"
    ∷ "superconducting realization and gauge model remain adapters"
    ∷ []
    )
  ∷ mkConstant
    "electron volt-joule relation"
    "eV"
    "e J"
    "J"
    exactSIDerivedConstant
    "derived from exact SI elementary charge"
    ( "particle physics"
    ∷ "chemistry energetics"
    ∷ "spectroscopy"
    ∷ []
    )
    ( "exact joule relation by elementary charge"
    ∷ "reported particle/chemical values still require authority"
    ∷ []
    )
  ∷ mkConstant
    "molar Planck constant"
    "N_A h"
    "N_A h"
    "J s mol^-1"
    exactSIDerivedConstant
    "derived from exact SI Avogadro constant and Planck constant"
    ( "molar quantum chemistry"
    ∷ "spectroscopy"
    ∷ "thermochemistry adapter targets"
    ∷ []
    )
    ( "exact as an expression in N_A and h"
    ∷ "chemical-model use remains authority and adapter bound"
    ∷ []
    )
  ∷ mkConstant
    "first radiation constant"
    "c_1"
    "2 pi h c^2"
    "W m^2"
    exactSIDerivedConstant
    "derived from exact SI Planck constant and speed of light"
    ( "blackbody radiation"
    ∷ "spectroscopy"
    ∷ "thermal measurement"
    ∷ []
    )
    ( "exact expression only"
    ∷ "Planck-law/blackbody applicability remains a model-law adapter"
    ∷ []
    )
  ∷ mkConstant
    "second radiation constant"
    "c_2"
    "h c / k_B"
    "m K"
    exactSIDerivedConstant
    "derived from exact SI Planck, speed-of-light, and Boltzmann constants"
    ( "blackbody radiation"
    ∷ "spectroscopy"
    ∷ "thermal measurement"
    ∷ []
    )
    ( "exact expression only"
    ∷ "Planck-law/blackbody applicability remains a model-law adapter"
    ∷ []
    )
  ∷ []

measuredPhysicsConstantAuthoritySlots : List KnownConstantSlot
measuredPhysicsConstantAuthoritySlots =
  mkConstant
    "Newtonian gravitational constant"
    "G"
    "CODATA-current measured value required"
    "m^3 kg^-1 s^-2"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants"
    ( "GR"
    ∷ "Newtonian gravity"
    ∷ "cross-scale simulator"
    ∷ []
    )
    ( "not exact"
    ∷ "must be consumed through calibration/uncertainty authority"
    ∷ []
    )
  ∷ mkConstant
    "fine-structure constant"
    "alpha"
    "CODATA-current measured value required"
    "dimensionless"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants"
    ( "QED"
    ∷ "atomic chemistry"
    ∷ "spectroscopy"
    ∷ "Standard Model sector"
    ∷ []
    )
    ( "not exact"
    ∷ "links electromagnetic coupling only after representation and unit adapters"
    ∷ []
    )
  ∷ mkConstant
    "electron rest mass"
    "m_e"
    "CODATA-current measured value required"
    "kg"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants"
    ( "Schrodinger"
    ∷ "atomic chemistry"
    ∷ "QED"
    ∷ []
    )
    ( "not exact"
    ∷ "requires uncertainty and unit authority"
    ∷ []
    )
  ∷ mkConstant
    "proton rest mass"
    "m_p"
    "CODATA-current measured value required"
    "kg"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants"
    ( "chemistry"
    ∷ "biology"
    ∷ "nuclear/particle adapters"
    ∷ []
    )
    ( "not exact"
    ∷ "requires uncertainty and isotope/nuclear model authority"
    ∷ []
    )
  ∷ mkConstant
    "vacuum permittivity"
    "epsilon_0"
    "derived/measured-SI value required"
    "F m^-1"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants"
    ( "Maxwell"
    ∷ "electrochemistry"
    ∷ "membrane electrophysiology"
    ∷ []
    )
    ( "not an independent exact SI defining constant after 2019"
    ∷ "derive or authority-load with uncertainty policy"
    ∷ []
    )
  ∷ mkConstant
    "vacuum permeability"
    "mu_0"
    "CODATA-current adjusted value required"
    "N A^-2"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants"
    ( "Maxwell"
    ∷ "QED"
    ∷ "electromagnetic unit adapters"
    ∷ []
    )
    ( "not an independent exact SI defining constant after 2019"
    ∷ "requires source/version/uncertainty and unit convention"
    ∷ []
    )
  ∷ mkConstant
    "characteristic impedance of vacuum"
    "Z_0"
    "CODATA-current adjusted value required"
    "ohm"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants"
    ( "Maxwell"
    ∷ "electromagnetic wave adapters"
    ∷ "calibration"
    ∷ []
    )
    ( "not exact after 2019 SI"
    ∷ "depends on electromagnetic constant authority and convention"
    ∷ []
    )
  ∷ mkConstant
    "Rydberg constant"
    "R_infinity"
    "CODATA-current measured value required"
    "m^-1"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants"
    ( "atomic physics"
    ∷ "spectroscopy"
    ∷ "quantum chemistry"
    ∷ []
    )
    ( "not exact"
    ∷ "spectral use requires model and isotope/reduced-mass adapters"
    ∷ []
    )
  ∷ mkConstant
    "neutron rest mass"
    "m_n"
    "CODATA-current measured value required"
    "kg"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants"
    ( "nuclear adapters"
    ∷ "chemistry isotope authority"
    ∷ "particle physics"
    ∷ []
    )
    ( "not exact"
    ∷ "requires uncertainty and particle/nuclear authority"
    ∷ []
    )
  ∷ mkConstant
    "muon rest mass"
    "m_mu"
    "PDG/CODATA-current measured value required"
    "MeV c^-2 or kg"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants / PDG particle data"
    ( "Standard Model sector"
    ∷ "lepton lane"
    ∷ "particle calibration"
    ∷ []
    )
    ( "not exact"
    ∷ "requires unit convention and particle-data authority"
    ∷ []
    )
  ∷ mkConstant
    "tau rest mass"
    "m_tau"
    "PDG/CODATA-current measured value required"
    "MeV c^-2 or kg"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants / PDG particle data"
    ( "Standard Model sector"
    ∷ "lepton lane"
    ∷ "particle calibration"
    ∷ []
    )
    ( "not exact"
    ∷ "requires unit convention and particle-data authority"
    ∷ []
    )
  ∷ mkConstant
    "proton mass energy equivalent"
    "m_p c^2"
    "CODATA-current measured value required"
    "MeV"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants"
    ( "physical unit authority"
    ∷ "nuclear adapters"
    ∷ "particle calibration"
    ∷ []
    )
    ( "not exact because m_p is measured"
    ∷ "requires energy-unit and uncertainty authority"
    ∷ []
    )
  ∷ mkConstant
    "Bohr radius"
    "a_0"
    "CODATA-current adjusted value required"
    "m"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants"
    ( "atomic physics"
    ∷ "quantum chemistry"
    ∷ "spectroscopy"
    ∷ []
    )
    ( "not exact"
    ∷ "depends on measured constants and atomic-model adapters"
    ∷ []
    )
  ∷ mkConstant
    "Hartree energy"
    "E_h"
    "CODATA-current adjusted value required"
    "J"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants"
    ( "atomic physics"
    ∷ "quantum chemistry"
    ∷ "spectroscopy"
    ∷ []
    )
    ( "not exact"
    ∷ "depends on measured constants and model convention"
    ∷ []
    )
  ∷ mkConstant
    "Bohr magneton"
    "mu_B"
    "CODATA-current adjusted value required"
    "J T^-1"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants"
    ( "atomic physics"
    ∷ "spin/magnetic adapters"
    ∷ "spectroscopy"
    ∷ []
    )
    ( "not exact"
    ∷ "depends on electron mass authority"
    ∷ []
    )
  ∷ mkConstant
    "nuclear magneton"
    "mu_N"
    "CODATA-current adjusted value required"
    "J T^-1"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants"
    ( "nuclear physics"
    ∷ "magnetic resonance adapters"
    ∷ "chemistry/biology measurement"
    ∷ []
    )
    ( "not exact"
    ∷ "depends on proton mass authority"
    ∷ []
    )
  ∷ mkConstant
    "Higgs boson mass"
    "m_H"
    "PDG-current measured value required"
    "GeV c^-2"
    measuredCODATAInput
    "PDG particle data"
    ( "Standard Model sector"
    ∷ "Higgs/EWSB adapters"
    ∷ "collider empirical lanes"
    ∷ []
    )
    ( "not exact"
    ∷ "not carrier-derived; requires PDG/provider authority"
    ∷ []
    )
  ∷ mkConstant
    "W and Z boson masses"
    "m_W, m_Z"
    "PDG-current measured values required"
    "GeV c^-2"
    measuredCODATAInput
    "PDG particle data"
    ( "Standard Model sector"
    ∷ "electroweak adapters"
    ∷ "collider empirical lanes"
    ∷ []
    )
    ( "not exact"
    ∷ "requires PDG/provider authority and electroweak scheme"
    ∷ []
    )
  ∷ mkConstant
    "quark masses"
    "m_q"
    "PDG-current scheme-dependent values required"
    "MeV or GeV"
    measuredCODATAInput
    "PDG particle data"
    ( "Standard Model sector"
    ∷ "QCD adapters"
    ∷ "hadron/chemistry boundary"
    ∷ []
    )
    ( "not exact"
    ∷ "scheme, scale, and authority must be explicit"
    ∷ []
    )
  ∷ mkConstant
    "CKM and PMNS parameters"
    "CKM, PMNS"
    "PDG-current fitted values required"
    "dimensionless"
    measuredCODATAInput
    "PDG particle data"
    ( "Standard Model sector"
    ∷ "flavour lanes"
    ∷ "neutrino adapters"
    ∷ []
    )
    ( "not exact"
    ∷ "fit authority, convention, and uncertainty required"
    ∷ []
    )
  ∷ mkConstant
    "strong coupling constant"
    "alpha_s"
    "PDG-current scale-dependent value required"
    "dimensionless"
    measuredCODATAInput
    "PDG particle data"
    ( "QCD"
    ∷ "Yang-Mills"
    ∷ "Standard Model sector"
    ∷ []
    )
    ( "not exact"
    ∷ "renormalization scale and scheme required"
    ∷ []
    )
  ∷ mkConstant
    "Fermi coupling constant"
    "G_F"
    "PDG/CODATA-current measured value required"
    "GeV^-2"
    measuredCODATAInput
    "NIST CODATA fundamental physical constants / PDG particle data"
    ( "weak interaction"
    ∷ "Standard Model sector"
    ∷ "collider empirical lanes"
    ∷ []
    )
    ( "not exact"
    ∷ "requires convention, authority, and uncertainty"
    ∷ []
    )
  ∷ []

canonicalPhysicsLawSlots : List KnownLawSlot
canonicalPhysicsLawSlots =
  mkLaw
    "Newtonian mechanics"
    "classical dynamics"
    "F = m a plus action-reaction and inertial-frame assumptions"
    "classical mechanics adapter"
    "future dynamics law adapter"
    modelLawInput
    ( "mass calibration"
    ∷ "force/acceleration units"
    ∷ "inertial frame"
    ∷ "validity regime"
    ∷ []
    )
    ( "classical model law; not carrier-derived dynamics"
    ∷ []
    )
  ∷ mkLaw
    "Newtonian gravitation"
    "classical gravity"
    "F = G m1 m2 / r^2"
    "GR / weak-field / cross-scale simulator"
    "weak-field and GR adapter surfaces"
    modelLawInput
    ( "G authority"
    ∷ "mass/distance calibration"
    ∷ "weak-field validity"
    ∷ []
    )
    ( "uses measured G authority; not full GR closure"
    ∷ []
    )
  ∷ mkLaw
    "conservation and continuity laws"
    "local conservation"
    "d rho/dt + div J = source"
    "field, fluid, chemistry, biology transport lanes"
    "adapter blocker index and observation transport spine"
    modelLawInput
    ( "density/current carrier"
    ∷ "source law"
    ∷ "boundary conditions"
    ∷ "units"
    ∷ []
    )
    ( "target form only; each lane needs its own conserved quantity"
    ∷ []
    )
  ∷ mkLaw
    "thermodynamic laws"
    "thermodynamics"
    "energy conservation, entropy inequality, third-law reference behavior"
    "chemistry / biology / statistical physics lanes"
    "future thermodynamics adapter"
    modelLawInput
    ( "state variables"
    ∷ "temperature"
    ∷ "entropy/free-energy carrier"
    ∷ "validity regime"
    ∷ []
    )
    ( "model-law target, not empirical thermodynamic closure"
    ∷ []
    )
  ∷ mkLaw
    "Klein-Gordon equation"
    "relativistic wave equation"
    "(Box + m^2) phi = 0"
    "QFT / relativistic dynamics adapter"
    "Known-limits QFT bridge"
    modelLawInput
    ( "Lorentzian metric"
    ∷ "mass parameter"
    ∷ "field representation"
    ∷ "quantization boundary"
    ∷ []
    )
    ( "relativistic target only"
    ∷ []
    )
  ∷ mkLaw
    "Dirac equation"
    "relativistic spinor dynamics"
    "(i gamma^mu partial_mu - m) psi = 0"
    "spinor / QFT / matter adapter"
    "Clifford and spin-Dirac bridge targets"
    modelLawInput
    ( "gamma matrices"
    ∷ "spinor bundle"
    ∷ "mass calibration"
    ∷ "gauge coupling"
    ∷ []
    )
    ( "canonical spin bridge is not a full physical Dirac dynamics derivation"
    ∷ []
    )
  ∷ mkLaw
    "Standard Model gauge and matter law"
    "particle physics"
    "SU(3)c x SU(2)L x U(1)Y with Higgs/Yukawa/anomaly constraints"
    "Standard Model sector lane"
    "SM candidate and anomaly receipt surfaces"
    modelLawInput
    ( "representation table"
    ∷ "hypercharge normalization"
    ∷ "Higgs/Yukawa couplings"
    ∷ "CKM/PMNS inputs"
    ∷ "empirical authority"
    ∷ []
    )
    ( "sector target only; exact SM match remains authority-gated"
    ∷ []
    )
  ∷ mkLaw
    "Maxwell equations"
    "classical field equation"
    "dF = 0; d * F = J"
    "Maxwell / gauge lane"
    "Docs/PhysicsLaneMaturityMatrix.md and gauge-field receipts"
    modelLawInput
    ( "curvature carrier"
    ∷ "Hodge/metric"
    ∷ "source-current extraction"
    ∷ "unit calibration"
    ∷ []
    )
    ( "law target is named; field-equation theorem remains unpromoted"
    ∷ []
    )
  ∷ mkLaw
    "Lorentz force law"
    "classical charged-particle dynamics"
    "F = q (E + v x B)"
    "Maxwell / dynamics adapter"
    "physics adapter blocker index"
    modelLawInput
    ( "charge authority"
    ∷ "velocity/metric carrier"
    ∷ "matter representation"
    ∷ []
    )
    ( "consumption target only"
    ∷ []
    )
  ∷ mkLaw
    "Schrodinger equation"
    "quantum dynamics"
    "i hbar d psi/dt = H psi"
    "Schrodinger / dynamics lane"
    "bounded Hamiltonian consumer receipts"
    modelLawInput
    ( "Hilbert representation"
    ∷ "self-adjoint Hamiltonian"
    ∷ "Born rule"
    ∷ "calibration"
    ∷ []
    )
    ( "bounded dynamics consumers are not textbook derivations"
    ∷ []
    )
  ∷ mkLaw
    "Born probability rule"
    "quantum measurement"
    "P(outcome) = |amplitude|^2"
    "measurement / uncertainty lane"
    "BornLike interface and measurement adapter blockers"
    modelLawInput
    ( "outcome sigma algebra"
    ∷ "state normalization"
    ∷ "empirical observable map"
    ∷ []
    )
    ( "probability semantics remain adapter-gated"
    ∷ []
    )
  ∷ mkLaw
    "Einstein field equation"
    "GR curvature"
    "G_mu_nu + Lambda g_mu_nu = 8 pi G T_mu_nu / c^4"
    "GR / curvature lane"
    "Known-limits GR bridge and GR-QFT consumer receipts"
    modelLawInput
    ( "non-flat Levi-Civita"
    ∷ "Ricci/scalar contraction"
    ∷ "stress-energy"
    ∷ "G calibration"
    ∷ []
    )
    ( "known-limits bridge does not promote full GR closure"
    ∷ []
    )
  ∷ mkLaw
    "Navier-Stokes equations"
    "continuum PDE"
    "incompressible momentum, pressure, viscosity, divergence-free flow"
    "Navier-Stokes Clay lane"
    "Clay NS receipts and roadmaps"
    modelLawInput
    ( "weak/strong solution class"
    ∷ "pressure reconstruction"
    ∷ "energy inequality"
    ∷ "regularity criterion"
    ∷ []
    )
    ( "Clay regularity remains false/open"
    ∷ []
    )
  ∷ mkLaw
    "Yang-Mills equation and mass gap target"
    "non-abelian gauge/QFT"
    "D_A F_A = 0 plus continuum quantum mass-gap target"
    "Yang-Mills Clay lane"
    "YM KP/Balaban/OS/Wightman receipts"
    modelLawInput
    ( "Lie algebra representation"
    ∷ "Wilson action"
    ∷ "OS positivity"
    ∷ "Wightman reconstruction"
    ∷ "continuum mass-shell"
    ∷ []
    )
    ( "Clay YM promotion remains false/open"
    ∷ []
    )
  ∷ []

canonicalChemistryLawSlots : List KnownLawSlot
canonicalChemistryLawSlots =
  mkLaw
    "stoichiometric conservation"
    "chemistry accounting"
    "atoms and charge conserved across balanced reactions"
    "chemistry / DNA / cross-scale simulator"
    "AtomicChemistryRecoveryTheorem and chemistry handoff diagnostics"
    modelLawInput
    ( "element identity"
    ∷ "charge state"
    ∷ "reaction authority"
    ∷ "Avogadro/mole unit"
    ∷ []
    )
    ( "safe local accounting target; not a wet-lab kinetics claim"
    ∷ []
    )
  ∷ mkLaw
    "law of mass action"
    "chemical equilibrium/kinetics"
    "reaction rate/equilibrium as product of activities or concentrations"
    "chemistry / biology reaction adapters"
    "chemistry physical handoff and protein-hormone chemistry bridge"
    modelLawInput
    ( "activity/concentration carrier"
    ∷ "temperature"
    ∷ "rate constants"
    ∷ "empirical calibration"
    ∷ []
    )
    ( "requires domain calibration before prediction"
    ∷ []
    )
  ∷ mkLaw
    "ideal gas law"
    "thermodynamics"
    "p V = n R T"
    "cross-scale simulator / chemistry"
    "future physical-model adapter"
    modelLawInput
    ( "equation-of-state authority"
    ∷ "temperature/pressure/volume units"
    ∷ "validity regime"
    ∷ []
    )
    ( "proxy model only unless EOS authority is supplied"
    ∷ []
    )
  ∷ mkLaw
    "Arrhenius law"
    "chemical kinetics"
    "k = A exp(-E_a / (R T))"
    "chemistry / biology kinetics"
    "future kinetics adapter"
    modelLawInput
    ( "activation energy"
    ∷ "temperature"
    ∷ "rate measurement"
    ∷ "fit authority"
    ∷ []
    )
    ( "empirical model target only"
    ∷ []
    )
  ∷ mkLaw
    "Beer-Lambert law"
    "spectroscopy/measurement"
    "A = epsilon l c"
    "empirical chemistry / biology measurement"
    "measurement adapter"
    modelLawInput
    ( "optical path"
    ∷ "molar absorptivity"
    ∷ "concentration"
    ∷ "instrument calibration"
    ∷ []
    )
    ( "measurement law requires instrument authority"
    ∷ []
    )
  ∷ mkLaw
    "Nernst equation"
    "electrochemistry"
    "E = E0 - (R T / n F) ln Q"
    "electrochemistry / membrane biology"
    "chemistry-biology adapter"
    modelLawInput
    ( "temperature"
    ∷ "charge number"
    ∷ "activities"
    ∷ "electrode/membrane authority"
    ∷ []
    )
    ( "connects chemistry and biology only through calibrated adapters"
    ∷ []
    )
  ∷ mkLaw
    "Gibbs free energy relation"
    "chemical thermodynamics"
    "Delta G = Delta H - T Delta S; Delta G = Delta G0 + R T ln Q"
    "chemistry / biology energetics"
    "future thermodynamic chemistry adapter"
    modelLawInput
    ( "enthalpy/entropy authority"
    ∷ "temperature"
    ∷ "activity model"
    ∷ "standard-state convention"
    ∷ []
    )
    ( "thermodynamic model target only"
    ∷ []
    )
  ∷ mkLaw
    "Henderson-Hasselbalch equation"
    "acid-base chemistry"
    "pH = pKa + log10(base/acid)"
    "chemistry / biology pH adapter"
    "future acid-base receipt"
    modelLawInput
    ( "pKa authority"
    ∷ "activity/concentration convention"
    ∷ "temperature"
    ∷ "buffer validity regime"
    ∷ []
    )
    ( "acid-base model target only"
    ∷ []
    )
  ∷ []

canonicalBiologyLawSlots : List KnownLawSlot
canonicalBiologyLawSlots =
  mkLaw
    "central dogma information flow"
    "molecular biology"
    "DNA -> RNA -> protein as canonical coding flow"
    "DNA / genome / protein bridge"
    "GenomeSensorimotorConnectomeBridge and protein-hormone chemistry bridge"
    domainReferenceInput
    ( "sequence provenance"
    ∷ "transcription/translation context"
    ∷ "organism/cell authority"
    ∷ []
    )
    ( "does not imply DNA encodes meaning or qualia"
    ∷ []
    )
  ∷ mkLaw
    "Mendelian inheritance"
    "genetics"
    "segregation and independent assortment under model assumptions"
    "DNA / biology observation lane"
    "developmental genomic inverse bridge"
    domainReferenceInput
    ( "genotype/phenotype observation"
    ∷ "pedigree/provenance"
    ∷ "model validity"
    ∷ []
    )
    ( "not a general causation or clinical prediction theorem"
    ∷ []
    )
  ∷ mkLaw
    "Hardy-Weinberg equilibrium"
    "population genetics"
    "p^2 + 2 p q + q^2 genotype frequencies under assumptions"
    "biology population adapter"
    "future population-genetics receipt"
    domainReferenceInput
    ( "population sampling"
    ∷ "random mating/no-selection assumptions"
    ∷ "statistical validation"
    ∷ []
    )
    ( "assumption-heavy model law"
    ∷ []
    )
  ∷ mkLaw
    "Michaelis-Menten kinetics"
    "enzyme kinetics"
    "v = Vmax S / (Km + S)"
    "protein / hormone / chemistry-cell bridge"
    "ProteinHormoneChemistryCellBridge"
    modelLawInput
    ( "enzyme/substrate measurement"
    ∷ "steady-state assumptions"
    ∷ "fit authority"
    ∷ []
    )
    ( "biochemical model target only"
    ∷ []
    )
  ∷ mkLaw
    "Fick diffusion law"
    "transport biology"
    "J = -D grad c"
    "cell / organism / observation transport"
    "ObservationTransportSpine adapters"
    modelLawInput
    ( "concentration field"
    ∷ "diffusion coefficient"
    ∷ "geometry/medium authority"
    ∷ []
    )
    ( "requires physical transport calibration"
    ∷ []
    )
  ∷ mkLaw
    "Nernst membrane potential"
    "electrophysiology"
    "E_ion = (R T / z F) ln(outside/inside)"
    "brain / membrane / sensory biology"
    "biology observation adapters"
    modelLawInput
    ( "ion concentrations"
    ∷ "temperature"
    ∷ "charge"
    ∷ "membrane measurement authority"
    ∷ []
    )
    ( "does not prove brain, cognition, or clinical closure"
    ∷ []
    )
  ∷ mkLaw
    "Goldman-Hodgkin-Katz membrane equation"
    "electrophysiology"
    "membrane potential from multi-ion permeabilities and concentrations"
    "brain / membrane / sensory biology"
    "biology observation adapters"
    modelLawInput
    ( "ion concentrations"
    ∷ "permeability ratios"
    ∷ "temperature"
    ∷ "membrane protocol authority"
    ∷ []
    )
    ( "model law only; no brain-state or clinical closure"
    ∷ []
    )
  ∷ mkLaw
    "logistic population growth"
    "population biology"
    "dN/dt = r N (1 - N/K)"
    "biology population adapter"
    "future population dynamics receipt"
    modelLawInput
    ( "population observation"
    ∷ "growth-rate fit"
    ∷ "carrying-capacity fit"
    ∷ "holdout validation"
    ∷ []
    )
    ( "phenomenological model only"
    ∷ []
    )
  ∷ mkLaw
    "Lotka-Volterra interaction model"
    "ecology"
    "coupled predator-prey or competition equations"
    "biology/ecology adapter"
    "future ecology receipt"
    modelLawInput
    ( "species observation"
    ∷ "interaction fit"
    ∷ "sampling protocol"
    ∷ "holdout validation"
    ∷ []
    )
    ( "model-law target only"
    ∷ []
    )
  ∷ mkLaw
    "Hill binding equation"
    "biochemistry/regulation"
    "theta = L^n / (K_d + L^n)"
    "protein / gene regulation adapter"
    "future regulatory kinetics receipt"
    modelLawInput
    ( "ligand concentration"
    ∷ "binding fit"
    ∷ "cooperativity parameter"
    ∷ "assay authority"
    ∷ []
    )
    ( "fit model only"
    ∷ []
    )
  ∷ []

canonicalEmpiricalRuntimeLawSlots : List KnownLawSlot
canonicalEmpiricalRuntimeLawSlots =
  mkLaw
    "source checksum and provenance law"
    "empirical/runtime receipt discipline"
    "source artifact -> checksum -> projection -> comparison"
    "empirical and PNF/ITIR lanes"
    "provider-intake, HEPData, PNF residual, and runtime receipt surfaces"
    repoInternalProxyInput
    ( "source artifact"
    ∷ "parser/reducer version"
    ∷ "projection digest"
    ∷ "authority decision"
    ∷ []
    )
    ( "receipt law only; no semantic or empirical adequacy by inspection"
    ∷ []
    )
  ∷ []

canonicalAuthoritySourceSlots : List AuthoritySourceSlot
canonicalAuthoritySourceSlots =
  mkAuthority
    "BIPM SI defining constants"
    siDefinitionAuthority
    "https://www.bipm.org/en/measurement-units/si-defining-constants"
    ( "exact SI defining constants"
    ∷ "exact SI derived constants"
    ∷ "unit definitions"
    ∷ []
    )
    ( "exact-value authority only"
    ∷ "does not derive physical law"
    ∷ []
    )
  ∷ mkAuthority
    "NIST SI base-unit definitions"
    siDefinitionAuthority
    "https://www.nist.gov/si-redefinition/definitions-si-base-units"
    ( "exact SI defining constants"
    ∷ "unit definitions"
    ∷ []
    )
    ( "US/NIST presentation of revised SI definitions"
    ∷ "does not provide model validation"
    ∷ []
    )
  ∷ mkAuthority
    "NIST CODATA fundamental physical constants"
    codataConstantsAuthority
    "https://www.nist.gov/pml/fundamental-physical-constants"
    ( "measured physics constants"
    ∷ "unit uncertainty"
    ∷ "calibration"
    ∷ []
    )
    ( "measured/adjusted values require version and uncertainty"
    ∷ "not carrier-derived constants"
    ∷ []
    )
  ∷ mkAuthority
    "Particle Data Group"
    pdgParticleDataAuthority
    "https://pdg.lbl.gov/"
    ( "particle masses"
    ∷ "couplings"
    ∷ "CKM/PMNS"
    ∷ "Standard Model sector"
    ∷ []
    )
    ( "external particle-data authority"
    ∷ "must be consumed through a typed receipt"
    ∷ []
    )
  ∷ mkAuthority
    "NIST Chemistry WebBook"
    nistChemistryAuthority
    "https://webbook.nist.gov/"
    ( "spectra"
    ∷ "thermochemistry"
    ∷ "chemical property authority"
    ∷ []
    )
    ( "external chemistry property authority"
    ∷ "does not close chemistry laws by citation alone"
    ∷ []
    )
  ∷ mkAuthority
    "MedlinePlus genetic-test validity framing"
    clinicalValidityAuthority
    "https://medlineplus.gov/genetics/understanding/testing/validtest/"
    ( "genetic testing"
    ∷ "clinical validity"
    ∷ "clinical utility"
    ∷ []
    )
    ( "clinical framing authority only"
    ∷ "no clinical claim is promoted"
    ∷ []
    )
  ∷ mkAuthority
    "BIDS neuroimaging provenance standard"
    neuroimagingProvenanceAuthority
    "https://www.nature.com/articles/sdata201644"
    ( "fMRI"
    ∷ "brain observation provenance"
    ∷ "dataset metadata"
    ∷ []
    )
    ( "metadata/provenance standard"
    ∷ "not latent brain-state recovery"
    ∷ []
    )
  ∷ mkAuthority
    "FlyWire adult Drosophila connectome"
    connectomeDatasetAuthority
    "https://www.nature.com/articles/s41586-024-07558-y"
    ( "connectome dataset facts"
    ∷ "brain observation"
    ∷ []
    )
    ( "dataset authority candidate"
    ∷ "requires checksum and selection receipt before consumption"
    ∷ []
    )
  ∷ mkAuthority
    "FAIR data principles"
    fairDataProvenanceAuthority
    "https://www.nature.com/articles/sdata201618"
    ( "empirical provenance"
    ∷ "source stewardship"
    ∷ "runtime artifacts"
    ∷ []
    )
    ( "provenance/stewardship framing"
    ∷ "not semantic truth authority"
    ∷ []
    )
  ∷ mkAuthority
    "HEPData/provider receipt authorities"
    providerReceiptAuthority
    "repo-local provider receipt packs"
    ( "HEPData"
    ∷ "empirical comparison"
    ∷ "authority decision"
    ∷ []
    )
    ( "must resolve to concrete source checksum and authority token"
    ∷ []
    )
  ∷ mkAuthority
    "PNF/ITIR runtime receipt authority"
    runtimeReceiptAuthority
    "repo-local runtime receipt packs"
    ( "PNF"
    ∷ "ITIR"
    ∷ "parser/reducer replay"
    ∷ []
    )
    ( "runtime provenance only"
    ∷ "not truth by parser output"
    ∷ []
    )
  ∷ []

constantSlotCount : List KnownConstantSlot → Nat
constantSlotCount [] = zero
constantSlotCount (_ ∷ xs) = suc (constantSlotCount xs)

lawSlotCount : List KnownLawSlot → Nat
lawSlotCount [] = zero
lawSlotCount (_ ∷ xs) = suc (lawSlotCount xs)

authoritySourceSlotCount : List AuthoritySourceSlot → Nat
authoritySourceSlotCount [] = zero
authoritySourceSlotCount (_ ∷ xs) = suc (authoritySourceSlotCount xs)

knownConstantSlotCount : ConstantsRegistry → Nat
knownConstantSlotCount registry =
  constantSlotCount (ConstantsRegistry.exactSIDefiningConstants registry)
  + constantSlotCount (ConstantsRegistry.exactSIDerivedConstants registry)
  + constantSlotCount (ConstantsRegistry.measuredPhysicsConstantSlots registry)

knownLawSlotCount : ConstantsRegistry → Nat
knownLawSlotCount registry =
  lawSlotCount (ConstantsRegistry.physicsLawSlots registry)
  + lawSlotCount (ConstantsRegistry.chemistryLawSlots registry)
  + lawSlotCount (ConstantsRegistry.biologyLawSlots registry)
  + lawSlotCount (ConstantsRegistry.empiricalRuntimeLawSlots registry)

data KnownInputsPopulationStatus : Set where
  externalInputSlotsPopulatedNonPromoting :
    KnownInputsPopulationStatus

record KnownInputsPopulationReceipt : Set₁ where
  field
    registry :
      ConstantsRegistry

    status :
      KnownInputsPopulationStatus

    knownConstants :
      Nat

    knownConstantsMatchRegistry :
      knownConstants ≡ knownConstantSlotCount registry

    knownLaws :
      Nat

    knownLawsMatchRegistry :
      knownLaws ≡ knownLawSlotCount registry

    authoritySources :
      Nat

    authoritySourcesMatchRegistry :
      authoritySources
      ≡
      authoritySourceSlotCount
        (ConstantsRegistry.authoritySourceSlots registry)

    validationTarget :
      String

    validationCommand :
      String

    failClosedFields :
      List String

    adapterDiscipline :
      List String

    constantCarrierDerived :
      Bool

    constantCarrierDerivedIsFalse :
      constantCarrierDerived ≡ false

    physicalLawDerived :
      Bool

    physicalLawDerivedIsFalse :
      physicalLawDerived ≡ false

    calibrationPromoted :
      Bool

    calibrationPromotedIsFalse :
      calibrationPromoted ≡ false

    empiricalAdequacyAccepted :
      Bool

    empiricalAdequacyAcceptedIsFalse :
      empiricalAdequacyAccepted ≡ false

    externalInputOnly :
      Bool

    externalInputOnlyIsTrue :
      externalInputOnly ≡ true

open KnownInputsPopulationReceipt public

record AuthorityConsumptionPolicyReceipt : Set₁ where
  field
    sourcePopulationReceipt :
      KnownInputsPopulationReceipt

    requiredMetadataFields :
      List String

    exactExpressionPolicy :
      List String

    measuredInputPolicy :
      List String

    lawTargetPolicy :
      List String

    acceptedAuthorityTokenPresent :
      Bool

    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false

    numericValuePromoted :
      Bool

    numericValuePromotedIsFalse :
      numericValuePromoted ≡ false

    modelLawPromoted :
      Bool

    modelLawPromotedIsFalse :
      modelLawPromoted ≡ false

    empiricalAdequacyAccepted :
      Bool

    empiricalAdequacyAcceptedIsFalse :
      empiricalAdequacyAccepted ≡ false

open AuthorityConsumptionPolicyReceipt public

record PhysicsAdapterKnownInputsReferenceReceipt : Set₁ where
  field
    sourcePopulationReceipt :
      KnownInputsPopulationReceipt

    sourceAuthorityPolicyReceipt :
      AuthorityConsumptionPolicyReceipt

    exactPhysicsReferenceInputs :
      List String

    measuredPhysicsAuthorityInputs :
      List String

    physicsLawTargets :
      List String

    gateClayRouteTargets :
      List String

    repoPhysicsAdapterSurfaces :
      List String

    missingPhysicsAdapters :
      List String

    boundedPhysicsTargetsPopulated :
      Bool

    boundedPhysicsTargetsPopulatedIsTrue :
      boundedPhysicsTargetsPopulated ≡ true

    maxwellFieldEquationPromoted :
      Bool

    maxwellFieldEquationPromotedIsFalse :
      maxwellFieldEquationPromoted ≡ false

    grFieldEquationPromoted :
      Bool

    grFieldEquationPromotedIsFalse :
      grFieldEquationPromoted ≡ false

    standardModelPromoted :
      Bool

    standardModelPromotedIsFalse :
      standardModelPromoted ≡ false

    gate3Closed :
      Bool

    gate3ClosedIsFalse :
      gate3Closed ≡ false

    navierStokesClayPromoted :
      Bool

    navierStokesClayPromotedIsFalse :
      navierStokesClayPromoted ≡ false

    yangMillsClayPromoted :
      Bool

    yangMillsClayPromotedIsFalse :
      yangMillsClayPromoted ≡ false

    knownPhysicsTranslationComplete :
      Bool

    knownPhysicsTranslationCompleteIsFalse :
      knownPhysicsTranslationComplete ≡ false

open PhysicsAdapterKnownInputsReferenceReceipt public

record ArithmeticGate3KnownInputsReferenceReceipt : Set₁ where
  field
    sourcePopulationReceipt :
      KnownInputsPopulationReceipt

    sourcePhysicsAdapterReceipt :
      PhysicsAdapterKnownInputsReferenceReceipt

    arithmeticCarrierTargets :
      List String

    gate3RouteTargets :
      List String

    moonshineHeckeSurfaces :
      List String

    repoArithmeticGate3Surfaces :
      List String

    missingArithmeticGate3Adapters :
      List String

    finiteArithmeticRoutePopulated :
      Bool

    finiteArithmeticRoutePopulatedIsTrue :
      finiteArithmeticRoutePopulated ≡ true

    densityEvidencePromoted :
      Bool

    densityEvidencePromotedIsTrue :
      densityEvidencePromoted ≡ true

    gate3Closed :
      Bool

    gate3ClosedIsFalse :
      gate3Closed ≡ false

    moscoRecoveryPromoted :
      Bool

    moscoRecoveryPromotedIsFalse :
      moscoRecoveryPromoted ≡ false

    noSpectralPollutionPromoted :
      Bool

    noSpectralPollutionPromotedIsFalse :
      noSpectralPollutionPromoted ≡ false

    continuumTransferPromoted :
      Bool

    continuumTransferPromotedIsFalse :
      continuumTransferPromoted ≡ false

    massShellBridgePromoted :
      Bool

    massShellBridgePromotedIsFalse :
      massShellBridgePromoted ≡ false

    physicsClaimPromoted :
      Bool

    physicsClaimPromotedIsFalse :
      physicsClaimPromoted ≡ false

open ArithmeticGate3KnownInputsReferenceReceipt public

record QuantumKnownInputsReferenceReceipt : Set₁ where
  field
    sourcePopulationReceipt :
      KnownInputsPopulationReceipt

    exactQuantumReferenceInputs :
      List String

    measuredQuantumAuthorityInputs :
      List String

    quantumLawTargets :
      List String

    repoQuantumSurfaces :
      List String

    missingQuantumAdapters :
      List String

    quantumDynamicsPromoted :
      Bool

    quantumDynamicsPromotedIsFalse :
      quantumDynamicsPromoted ≡ false

    bornRulePromoted :
      Bool

    bornRulePromotedIsFalse :
      bornRulePromoted ≡ false

    qftPromoted :
      Bool

    qftPromotedIsFalse :
      qftPromoted ≡ false

    quantumEmpiricalAdequacyAccepted :
      Bool

    quantumEmpiricalAdequacyAcceptedIsFalse :
      quantumEmpiricalAdequacyAccepted ≡ false

    externalInputOnly :
      Bool

    externalInputOnlyIsTrue :
      externalInputOnly ≡ true

open QuantumKnownInputsReferenceReceipt public

record ChemistryKnownInputsReferenceReceipt : Set₁ where
  field
    sourcePopulationReceipt :
      KnownInputsPopulationReceipt

    exactChemistryReferenceInputs :
      List String

    measuredChemistryAuthorityInputs :
      List String

    chemistryLawTargets :
      List String

    repoChemistrySurfaces :
      List String

    missingChemistryAdapters :
      List String

    localDefinitionalChemistryPopulated :
      Bool

    localDefinitionalChemistryPopulatedIsTrue :
      localDefinitionalChemistryPopulated ≡ true

    physicalChemistryPromoted :
      Bool

    physicalChemistryPromotedIsFalse :
      physicalChemistryPromoted ≡ false

    spectroscopyPromoted :
      Bool

    spectroscopyPromotedIsFalse :
      spectroscopyPromoted ≡ false

    bondingInterpretationPromoted :
      Bool

    bondingInterpretationPromotedIsFalse :
      bondingInterpretationPromoted ≡ false

    wetLabValidationAccepted :
      Bool

    wetLabValidationAcceptedIsFalse :
      wetLabValidationAccepted ≡ false

    externalInputOnly :
      Bool

    externalInputOnlyIsTrue :
      externalInputOnly ≡ true

open ChemistryKnownInputsReferenceReceipt public

record BiologyKnownInputsReferenceReceipt : Set₁ where
  field
    sourcePopulationReceipt :
      KnownInputsPopulationReceipt

    exactBiologyReferenceInputs :
      List String

    measuredBiologyAuthorityInputs :
      List String

    biologyLawTargets :
      List String

    repoBiologySurfaces :
      List String

    missingBiologyAdapters :
      List String

    structuredBiologyBridgePopulated :
      Bool

    structuredBiologyBridgePopulatedIsTrue :
      structuredBiologyBridgePopulated ≡ true

    biologyCausationPromoted :
      Bool

    biologyCausationPromotedIsFalse :
      biologyCausationPromoted ≡ false

    interventionPromoted :
      Bool

    interventionPromotedIsFalse :
      interventionPromoted ≡ false

    clinicalValidityAccepted :
      Bool

    clinicalValidityAcceptedIsFalse :
      clinicalValidityAccepted ≡ false

    genomeToConnectomeClosurePromoted :
      Bool

    genomeToConnectomeClosurePromotedIsFalse :
      genomeToConnectomeClosurePromoted ≡ false

    brainStateRecoveryPromoted :
      Bool

    brainStateRecoveryPromotedIsFalse :
      brainStateRecoveryPromoted ≡ false

    externalInputOnly :
      Bool

    externalInputOnlyIsTrue :
      externalInputOnly ≡ true

open BiologyKnownInputsReferenceReceipt public

record EmpiricalRuntimeKnownInputsReferenceReceipt : Set₁ where
  field
    sourcePopulationReceipt :
      KnownInputsPopulationReceipt

    sourceAuthorityPolicyReceipt :
      AuthorityConsumptionPolicyReceipt

    empiricalRuntimeLawTargets :
      List String

    providerAuthorityInputs :
      List String

    runtimeAuthorityInputs :
      List String

    repoEmpiricalRuntimeSurfaces :
      List String

    missingEmpiricalRuntimeAdapters :
      List String

    receiptInfrastructurePopulated :
      Bool

    receiptInfrastructurePopulatedIsTrue :
      receiptInfrastructurePopulated ≡ true

    acceptedProviderAuthorityPromoted :
      Bool

    acceptedProviderAuthorityPromotedIsFalse :
      acceptedProviderAuthorityPromoted ≡ false

    comparisonLawPromoted :
      Bool

    comparisonLawPromotedIsFalse :
      comparisonLawPromoted ≡ false

    covarianceCalibrationPromoted :
      Bool

    covarianceCalibrationPromotedIsFalse :
      covarianceCalibrationPromoted ≡ false

    holdoutValidationAccepted :
      Bool

    holdoutValidationAcceptedIsFalse :
      holdoutValidationAccepted ≡ false

    runtimeReplayAuthorityAccepted :
      Bool

    runtimeReplayAuthorityAcceptedIsFalse :
      runtimeReplayAuthorityAccepted ≡ false

    semanticAdequacyAccepted :
      Bool

    semanticAdequacyAcceptedIsFalse :
      semanticAdequacyAccepted ≡ false

    empiricalAdequacyAccepted :
      Bool

    empiricalAdequacyAcceptedIsFalse :
      empiricalAdequacyAccepted ≡ false

open EmpiricalRuntimeKnownInputsReferenceReceipt public

repoWideConstantsRegistry : ConstantsRegistry
repoWideConstantsRegistry = record
  { registryLabel = "DASHI repo-wide constants owner"
  ; registryBoundary = noPhysicsClaim
  ; linkedRegistry = canonicalPhotonuclearLink
  ; linkedRegistryCount = suc zero
  ; linkedEntryCount = linkedRegistryEntryCount canonicalPhotonuclearLink
  ; exactSIDefiningConstants = canonicalSIDefiningConstants
  ; exactSIDerivedConstants = canonicalSIDerivedConstants
  ; measuredPhysicsConstantSlots = measuredPhysicsConstantAuthoritySlots
  ; physicsLawSlots = canonicalPhysicsLawSlots
  ; chemistryLawSlots = canonicalChemistryLawSlots
  ; biologyLawSlots = canonicalBiologyLawSlots
  ; empiricalRuntimeLawSlots = canonicalEmpiricalRuntimeLawSlots
  ; authoritySourceSlots = canonicalAuthoritySourceSlots
  ; constantCarrierDerived = false
  ; constantCarrierDerivedIsFalse = refl
  ; physicalLawDerived = false
  ; physicalLawDerivedIsFalse = refl
  ; calibrationPromoted = false
  ; calibrationPromotedIsFalse = refl
  ; empiricalAdequacyAccepted = false
  ; empiricalAdequacyAcceptedIsFalse = refl
  ; externalInputOnly = true
  ; externalInputOnlyIsTrue = refl
  ; noGlobalClaim = noPhysicsClaim
  }

canonicalKnownInputsPopulationReceipt : KnownInputsPopulationReceipt
canonicalKnownInputsPopulationReceipt = record
  { registry = repoWideConstantsRegistry
  ; status = externalInputSlotsPopulatedNonPromoting
  ; knownConstants = knownConstantSlotCount repoWideConstantsRegistry
  ; knownConstantsMatchRegistry = refl
  ; knownLaws = knownLawSlotCount repoWideConstantsRegistry
  ; knownLawsMatchRegistry = refl
  ; authoritySources =
      authoritySourceSlotCount
        (ConstantsRegistry.authoritySourceSlots repoWideConstantsRegistry)
  ; authoritySourcesMatchRegistry = refl
  ; validationTarget = "DASHI/Constants/Registry.agda"
  ; validationCommand = "agda -i . DASHI/Constants/Registry.agda"
  ; failClosedFields =
      "constantCarrierDerived=false"
      ∷ "physicalLawDerived=false"
      ∷ "calibrationPromoted=false"
      ∷ "empiricalAdequacyAccepted=false"
      ∷ "externalInputOnly=true"
      ∷ []
  ; adapterDiscipline =
      "exact SI slots may be consumed as reference inputs"
      ∷ "exact derived SI expressions require rounding policy at use site"
      ∷ "measured constants require source/version/unit/uncertainty receipt"
      ∷ "model laws require lane-specific adapters and validation"
      ∷ "authority source slots are not accepted tokens by themselves"
      ∷ []
  ; constantCarrierDerived =
      ConstantsRegistry.constantCarrierDerived repoWideConstantsRegistry
  ; constantCarrierDerivedIsFalse =
      ConstantsRegistry.constantCarrierDerivedIsFalse repoWideConstantsRegistry
  ; physicalLawDerived =
      ConstantsRegistry.physicalLawDerived repoWideConstantsRegistry
  ; physicalLawDerivedIsFalse =
      ConstantsRegistry.physicalLawDerivedIsFalse repoWideConstantsRegistry
  ; calibrationPromoted =
      ConstantsRegistry.calibrationPromoted repoWideConstantsRegistry
  ; calibrationPromotedIsFalse =
      ConstantsRegistry.calibrationPromotedIsFalse repoWideConstantsRegistry
  ; empiricalAdequacyAccepted =
      ConstantsRegistry.empiricalAdequacyAccepted repoWideConstantsRegistry
  ; empiricalAdequacyAcceptedIsFalse =
      ConstantsRegistry.empiricalAdequacyAcceptedIsFalse
        repoWideConstantsRegistry
  ; externalInputOnly =
      ConstantsRegistry.externalInputOnly repoWideConstantsRegistry
  ; externalInputOnlyIsTrue =
      ConstantsRegistry.externalInputOnlyIsTrue repoWideConstantsRegistry
  }

canonicalAuthorityConsumptionPolicyReceipt :
  AuthorityConsumptionPolicyReceipt
canonicalAuthorityConsumptionPolicyReceipt = record
  { sourcePopulationReceipt = canonicalKnownInputsPopulationReceipt
  ; requiredMetadataFields =
      "authorityVersion"
      ∷ "sourceChecksum"
      ∷ "sourceAccessDate"
      ∷ "valueUncertainty"
      ∷ "roundingPolicy"
      ∷ "unitConvention"
      ∷ "validityRegime"
      ∷ "sourceUri"
      ∷ "providerReceiptId"
      ∷ []
  ; exactExpressionPolicy =
      "exact SI defining constants may be cited by exact value"
      ∷ "exact derived SI expressions remain symbolic until a rounding policy is supplied"
      ∷ "realization, instrument, device, and model applicability are separate adapters"
      ∷ []
  ; measuredInputPolicy =
      "measured and adjusted constants require source/version/unit/uncertainty"
      ∷ "PDG and CODATA values require convention, scheme, or scale where applicable"
      ∷ "numeric values are not frozen by the registry without a consuming authority token"
      ∷ []
  ; lawTargetPolicy =
      "law slots name canonical target vocabulary only"
      ∷ "physical, chemical, biological, empirical, or clinical adequacy requires lane-specific adapters"
      ∷ "source presence alone is not an accepted validation token"
      ∷ []
  ; acceptedAuthorityTokenPresent = false
  ; acceptedAuthorityTokenPresentIsFalse = refl
  ; numericValuePromoted = false
  ; numericValuePromotedIsFalse = refl
  ; modelLawPromoted = false
  ; modelLawPromotedIsFalse = refl
  ; empiricalAdequacyAccepted = false
  ; empiricalAdequacyAcceptedIsFalse = refl
  }

canonicalPhysicsAdapterKnownInputsReferenceReceipt :
  PhysicsAdapterKnownInputsReferenceReceipt
canonicalPhysicsAdapterKnownInputsReferenceReceipt = record
  { sourcePopulationReceipt = canonicalKnownInputsPopulationReceipt
  ; sourceAuthorityPolicyReceipt =
      canonicalAuthorityConsumptionPolicyReceipt
  ; exactPhysicsReferenceInputs =
      "c : exact SI speed of light for Maxwell, relativity, GR, QFT, and calibration units"
      ∷ "h and hbar : exact quantum/QFT/spectral reference inputs"
      ∷ "e : exact charge reference for Maxwell, Lorentz force, electrochemistry, and gauge-sector calibration"
      ∷ "k_B, N_A, R, and F : exact thermodynamic, molar, and electrochemical references"
      ∷ "K_J, R_K, G_0, Phi_0, eV, N_A h, c_1, and c_2 : exact expression-level metrology and spectroscopy references"
      ∷ []
  ; measuredPhysicsAuthorityInputs =
      "G requires CODATA authority before Newtonian or GR normalization"
      ∷ "alpha, epsilon_0, mu_0, Z_0, R_infinity, a_0, E_h, mu_B, and mu_N require CODATA authority"
      ∷ "m_e, m_p, m_n, m_mu, m_tau, and m_p c^2 require CODATA/PDG authority and unit convention"
      ∷ "Higgs/W/Z masses, quark masses, CKM/PMNS, alpha_s, and G_F require PDG/provider authority, scheme, and uncertainty"
      ∷ "all measured constants require authorityVersion, checksum, access date, uncertainty, rounding, unit, and validity-regime metadata before numeric use"
      ∷ []
  ; physicsLawTargets =
      "Newtonian mechanics"
      ∷ "Newtonian gravitation"
      ∷ "conservation and continuity laws"
      ∷ "thermodynamic laws"
      ∷ "Klein-Gordon equation"
      ∷ "Dirac equation"
      ∷ "Standard Model gauge and matter law"
      ∷ "Maxwell equations"
      ∷ "Lorentz force law"
      ∷ "Schrodinger equation"
      ∷ "Born probability rule"
      ∷ "Einstein field equation"
      ∷ "Navier-Stokes equations"
      ∷ "Yang-Mills equation and mass gap target"
      ∷ []
  ; gateClayRouteTargets =
      "Gate 3 finite norm dictionary"
      ∷ "Gate 3 pruned-union density/fill-distance evidence"
      ∷ "Gate 3 Mosco and no-spectral-pollution targets"
      ∷ "Navier-Stokes pressure/phase and standard PDE regularity route"
      ∷ "Yang-Mills KP/Balaban/OS/Wightman continuum and mass-gap route"
      ∷ "finite DHR/SM categorical compatibility and conditional promotion route"
      ∷ []
  ; repoPhysicsAdapterSurfaces =
      "DASHI/Physics/Closure/CarrierToPhysicsInterpretationFunctor.agda"
      ∷ "DASHI/Physics/Closure/BoundaryParameterAdapterAlgebra.agda"
      ∷ "DASHI/Physics/Closure/KnownLimitsQFTBridgeTheorem.agda"
      ∷ "DASHI/Physics/Closure/SchrodingerEvolutionScope.agda"
      ∷ "DASHI/Physics/Closure/SchrodingerSelfAdjointEvolutionReceipt.agda"
      ∷ "DASHI/Physics/Closure/Gate3NormDictionary.agda"
      ∷ "DASHI/Physics/Closure/Gate3PrunedUnionDensityReceipt.agda"
      ∷ "DASHI/Physics/Closure/Gate3PrunedDensityMoscoReceipt.agda"
      ∷ "DASHI/Physics/Closure/NSPhasePressureGate3Receipt.agda"
      ∷ "DASHI/Physics/Closure/YMKPActivityRatioMarginReceipt.agda"
      ∷ "DASHI/Physics/Closure/YMBalabanTransferCompatibilityTheorem.agda"
      ∷ "DASHI/Physics/QFT/ConditionalGDHRSMPromotionReceipt.agda"
      ∷ "DASHI/Physics/QFT/FinitePrimeLaneDHRSMCompatibilityLedger.agda"
      ∷ "DASHI/Physics/QFT/SMContentSummaryReceipt.agda"
      ∷ "DASHI/Physics/QFT/ExactSMMatchToken.agda"
      ∷ []
  ; missingPhysicsAdapters =
      "metric, Hodge, curvature, and source-current extraction for Maxwell/gauge"
      ∷ "non-flat Levi-Civita, Ricci/scalar contraction, stress-energy, and G normalization for GR"
      ∷ "Hilbert representation, self-adjoint Hamiltonian, Stone/unitary route, and Born semantics for Schrodinger/measurement"
      ∷ "GNS/vacuum, AQFT net, DHR/DR authority, and exact SM carrier-functor match"
      ∷ "PDG/CODATA calibration, CKM/PMNS/Higgs/sector authority, and empirical observable map"
      ∷ "Gate 3 Mosco recovery, no spectral pollution, continuum transfer, and mass-shell identification"
      ∷ "Navier-Stokes weak/strong solution class, pressure reconstruction, nonlinear passage, energy inequality, and regularity criterion"
      ∷ "Yang-Mills Lie-algebra/gauge identification, Wilson activity, OS positivity, Wightman reconstruction, continuum RG transfer, and positive mass gap"
      ∷ []
  ; boundedPhysicsTargetsPopulated = true
  ; boundedPhysicsTargetsPopulatedIsTrue = refl
  ; maxwellFieldEquationPromoted = false
  ; maxwellFieldEquationPromotedIsFalse = refl
  ; grFieldEquationPromoted = false
  ; grFieldEquationPromotedIsFalse = refl
  ; standardModelPromoted = false
  ; standardModelPromotedIsFalse = refl
  ; gate3Closed = false
  ; gate3ClosedIsFalse = refl
  ; navierStokesClayPromoted = false
  ; navierStokesClayPromotedIsFalse = refl
  ; yangMillsClayPromoted = false
  ; yangMillsClayPromotedIsFalse = refl
  ; knownPhysicsTranslationComplete = false
  ; knownPhysicsTranslationCompleteIsFalse = refl
  }

canonicalArithmeticGate3KnownInputsReferenceReceipt :
  ArithmeticGate3KnownInputsReferenceReceipt
canonicalArithmeticGate3KnownInputsReferenceReceipt = record
  { sourcePopulationReceipt = canonicalKnownInputsPopulationReceipt
  ; sourcePhysicsAdapterReceipt =
      canonicalPhysicsAdapterKnownInputsReferenceReceipt
  ; arithmeticCarrierTargets =
      "Hecke eigenvalue and CM correction carriers"
      ∷ "modular-j and Monster/moonshine support carriers"
      ∷ "finite prime-lane, SSP, PAWOTG, and adelic-localization carriers"
      ∷ "finite norm dictionary and frame lower-bound carriers"
      ∷ "cancellation-pressure and barrier-route carriers"
      ∷ []
  ; gate3RouteTargets =
      "finite norm dictionary route input"
      ∷ "pruned-union density and fill-distance evidence"
      ∷ "Mosco liminf/recovery target"
      ∷ "no spectral pollution target"
      ∷ "spectral transfer or pruning target"
      ∷ "mass-shell and known-physics translation target"
      ∷ "Navier-Stokes and Yang-Mills Gate 3 consumer targets"
      ∷ []
  ; moonshineHeckeSurfaces =
      "DASHI/Algebra/MoonshineBridge.agda"
      ∷ "DASHI/Physics/Moonshine/ModularJInvariantAlphaReceipt.agda"
      ∷ "DASHI/Physics/Moonshine/KroneckerLimitAlphaCorrectionReceipt.agda"
      ∷ "DASHI/Physics/Moonshine/HeegnerLaneAssignmentReceipt.agda"
      ∷ "DASHI/Physics/Moonshine/SupersingularPrimeLaneBridge.agda"
      ∷ "DASHI/Physics/Closure/HeckeCharacterPhaseReceipt.agda"
      ∷ "DASHI/Physics/Closure/HeckeCarrierVsCMSplittingReceipt.agda"
      ∷ "DASHI/Physics/Closure/MonsterMoonshineJDistributionSupportReceipt.agda"
      ∷ "DASHI/Physics/Closure/MonsterMoonshineSSPQuotientControlReceipt.agda"
      ∷ []
  ; repoArithmeticGate3Surfaces =
      "DASHI/Physics/Closure/Gate3NormDictionary.agda"
      ∷ "DASHI/Physics/Closure/Gate3NormDictionaryReceipt.agda"
      ∷ "DASHI/Physics/Closure/Gate3PrunedUnionDensityReceipt.agda"
      ∷ "DASHI/Physics/Closure/Gate3PrunedDensityMoscoReceipt.agda"
      ∷ "DASHI/Physics/Closure/Gate3NoSpectralPollutionReceipt.agda"
      ∷ "DASHI/Physics/Closure/Gate3NoSpectralPollutionConditionalProofReceipt.agda"
      ∷ "DASHI/Physics/Closure/Gate3MoscoConstructiveSequenceReceipt.agda"
      ∷ "DASHI/Physics/Closure/Gate3SpectralTransferOrPruningReceipt.agda"
      ∷ "DASHI/Physics/Closure/SpectralConvergenceGate3Receipt.agda"
      ∷ "DASHI/Physics/Closure/CarrierMoscoConvergenceFromPhysicsReceipt.agda"
      ∷ "DASHI/Physics/Closure/NSPhasePressureGate3Receipt.agda"
      ∷ "DASHI/Physics/Closure/YMSprint129MoscoSpectralRouteLedger.agda"
      ∷ []
  ; missingArithmeticGate3Adapters =
      "global density proof beyond finite/pruned evidence"
      ∷ "Mosco liminf and recovery completion at the required continuum target"
      ∷ "no-spectral-pollution proof for the promoted target"
      ∷ "spectral transfer from finite/pruned route to continuum operator"
      ∷ "mass-shell identification and known-physics translation"
      ∷ "NS nonlinear pressure/phase passage from Gate 3 data"
      ∷ "YM continuum RG/OS/Wightman/mass-gap transfer from Gate 3 data"
      ∷ "external mathematical authority or accepted theorem token where required"
      ∷ []
  ; finiteArithmeticRoutePopulated = true
  ; finiteArithmeticRoutePopulatedIsTrue = refl
  ; densityEvidencePromoted = true
  ; densityEvidencePromotedIsTrue = refl
  ; gate3Closed = false
  ; gate3ClosedIsFalse = refl
  ; moscoRecoveryPromoted = false
  ; moscoRecoveryPromotedIsFalse = refl
  ; noSpectralPollutionPromoted = false
  ; noSpectralPollutionPromotedIsFalse = refl
  ; continuumTransferPromoted = false
  ; continuumTransferPromotedIsFalse = refl
  ; massShellBridgePromoted = false
  ; massShellBridgePromotedIsFalse = refl
  ; physicsClaimPromoted = false
  ; physicsClaimPromotedIsFalse = refl
  }

canonicalQuantumKnownInputsReferenceReceipt :
  QuantumKnownInputsReferenceReceipt
canonicalQuantumKnownInputsReferenceReceipt = record
  { sourcePopulationReceipt = canonicalKnownInputsPopulationReceipt
  ; exactQuantumReferenceInputs =
      "h : exact SI Planck constant"
      ∷ "hbar : exact derived expression h / (2 pi)"
      ∷ "c : exact SI speed of light"
      ∷ "e : exact SI elementary charge"
      ∷ []
  ; measuredQuantumAuthorityInputs =
      "alpha : CODATA measured fine-structure constant authority required"
      ∷ "m_e : CODATA measured electron mass authority required"
      ∷ "m_p : CODATA measured proton mass authority required where nuclear/chemistry adapters consume it"
      ∷ "epsilon_0 : derived/measured-SI electromagnetic constant authority required"
      ∷ "particle masses, CKM/PMNS, Higgs, and couplings require PDG/provider receipts"
      ∷ []
  ; quantumLawTargets =
      "Schrodinger equation: i hbar d psi/dt = H psi"
      ∷ "Born probability rule: P(outcome) = abs(amplitude)^2"
      ∷ "Dirac equation: (i gamma^mu partial_mu - m) psi = 0"
      ∷ "Klein-Gordon equation: (Box + m^2) phi = 0"
      ∷ "CCR/CAR and Hilbert/GNS representation targets"
      ∷ "QFT/AQFT net, DHR/DR reconstruction, and Standard Model sector targets"
      ∷ []
  ; repoQuantumSurfaces =
      "DASHI/Physics/Closure/SchrodingerEvolutionScope.agda"
      ∷ "DASHI/Physics/Closure/SchrodingerSelfAdjointEvolutionReceipt.agda"
      ∷ "DASHI/Physics/Closure/KnownLimitsQFTBridgeTheorem.agda"
      ∷ "DASHI/Physics/Measurement.agda"
      ∷ "Docs/MeasurementSurfaceProjectionContract.md"
      ∷ "DASHI/Algebra/CCR.agda"
      ∷ "DASHI/Algebra/Quantum/Unitary.agda"
      ∷ "DASHI/Physics/QFT.agda"
      ∷ "DASHI/Physics/QFT/DHRGaugeReceiptSurface.agda"
      ∷ "DASHI/Physics/QFT/DHRTensorDualGroupReconstruction.agda"
      ∷ []
  ; missingQuantumAdapters =
      "physical Hilbert representation"
      ∷ "dense/admissible self-adjoint Hamiltonian domain"
      ∷ "Kato-Rellich or equivalent self-adjointness route"
      ∷ "Stone theorem unitary-group route"
      ∷ "Hamiltonian exponential construction"
      ∷ "Born probability semantics and outcome sigma algebra"
      ∷ "CCR/CAR representation witness"
      ∷ "GNS/vacuum/state functional"
      ∷ "local observable net and AQFT hypotheses"
      ∷ "calibration, units, and empirical observable map"
      ∷ []
  ; quantumDynamicsPromoted = false
  ; quantumDynamicsPromotedIsFalse = refl
  ; bornRulePromoted = false
  ; bornRulePromotedIsFalse = refl
  ; qftPromoted = false
  ; qftPromotedIsFalse = refl
  ; quantumEmpiricalAdequacyAccepted = false
  ; quantumEmpiricalAdequacyAcceptedIsFalse = refl
  ; externalInputOnly = true
  ; externalInputOnlyIsTrue = refl
  }

canonicalChemistryKnownInputsReferenceReceipt :
  ChemistryKnownInputsReferenceReceipt
canonicalChemistryKnownInputsReferenceReceipt = record
  { sourcePopulationReceipt = canonicalKnownInputsPopulationReceipt
  ; exactChemistryReferenceInputs =
      "N_A : exact SI Avogadro constant"
      ∷ "k_B : exact SI Boltzmann constant"
      ∷ "R : exact derived expression N_A k_B"
      ∷ "e : exact SI elementary charge"
      ∷ "F : exact derived expression N_A e"
      ∷ "h and hbar : exact quantum/spectral reference inputs"
      ∷ "c : exact optical/spectroscopic reference input"
      ∷ []
  ; measuredChemistryAuthorityInputs =
      "alpha : CODATA fine-structure constant for electromagnetic/atomic adapters"
      ∷ "m_e : CODATA electron mass for atomic/spectral adapters"
      ∷ "m_p and isotope/nuclear masses require CODATA/PDG/provider authority"
      ∷ "epsilon_0 requires derived/measured-SI electromagnetic authority"
      ∷ "spectral, thermochemical, pKa, rate, diffusion, binding, and activity data require NIST Chemistry WebBook or domain provider receipts"
      ∷ []
  ; chemistryLawTargets =
      "stoichiometric conservation"
      ∷ "law of mass action"
      ∷ "ideal gas law"
      ∷ "Arrhenius law"
      ∷ "Beer-Lambert law"
      ∷ "Nernst equation"
      ∷ "Gibbs free energy relation"
      ∷ "Henderson-Hasselbalch equation"
      ∷ "DNA/supervoxel checksum, reverse-complement, chemistry quotient, and Hamiltonian sheet laws"
      ∷ []
  ; repoChemistrySurfaces =
      "DASHI/Unified/ChemistrySupervoxel.agda"
      ∷ "DASHI/Physics/Closure/AtomicChemistryRecoveryTheorem.agda"
      ∷ "DASHI/Physics/Closure/ChemistryPhysicalHandoffDiagnostic.agda"
      ∷ "DASHI/Physics/Closure/ChemistryStrictPhysicalSemanticsBlocker.agda"
      ∷ "DASHI/Physics/Closure/Candidate256PhysicalCalibrationExternalReceipt.agda"
      ∷ "Ontology/DNA/ChemistryConcrete.agda"
      ∷ "Ontology/DNA/ChemistryUVConcrete.agda"
      ∷ "Ontology/DNA/ChemistrySheetHamiltonian.agda"
      ∷ "Ontology/DNA/SupervoxelAdmissibility.agda"
      ∷ "Ontology/DNA/SupervoxelChemistryLongWindowLaws.agda"
      ∷ "Ontology/DNA/SupervoxelChemistryCouplingLaws.agda"
      ∷ "DASHI/Biology/ProteinHormoneChemistryCellBridge.agda"
      ∷ []
  ; missingChemistryAdapters =
      "physical scale-setting law for quotient classes"
      ∷ "spectral observable map"
      ∷ "bonding interpretation carrier and preservation law"
      ∷ "empirical physical validation carrier"
      ∷ "NIST/CODATA/unit authority binding"
      ∷ "reaction-network and kinetics authority"
      ∷ "thermochemical/property source checksum"
      ∷ "instrument calibration and comparison law"
      ∷ "wet-lab protocol/provenance receipt"
      ∷ []
  ; localDefinitionalChemistryPopulated = true
  ; localDefinitionalChemistryPopulatedIsTrue = refl
  ; physicalChemistryPromoted = false
  ; physicalChemistryPromotedIsFalse = refl
  ; spectroscopyPromoted = false
  ; spectroscopyPromotedIsFalse = refl
  ; bondingInterpretationPromoted = false
  ; bondingInterpretationPromotedIsFalse = refl
  ; wetLabValidationAccepted = false
  ; wetLabValidationAcceptedIsFalse = refl
  ; externalInputOnly = true
  ; externalInputOnlyIsTrue = refl
  }

canonicalBiologyKnownInputsReferenceReceipt :
  BiologyKnownInputsReferenceReceipt
canonicalBiologyKnownInputsReferenceReceipt = record
  { sourcePopulationReceipt = canonicalKnownInputsPopulationReceipt
  ; exactBiologyReferenceInputs =
      "N_A : exact SI Avogadro constant for molecule-count/mole bridges"
      ∷ "k_B and R : exact thermodynamic reference inputs for energetics and temperature-dependent model laws"
      ∷ "e and F : exact electrochemical reference inputs for membrane potentials"
      ∷ "h and hbar : exact quantum/spectroscopic reference inputs when measurement adapters need them"
      ∷ "K_cd : exact photometric reference input for vision/retina observation lanes"
      ∷ []
  ; measuredBiologyAuthorityInputs =
      "diffusion coefficients, permeabilities, binding constants, pKa, rate constants, and Michaelis constants require assay/provider authority"
      ∷ "ion concentrations, temperature, tissue/cell context, and membrane protocol require source/version/checksum receipts"
      ∷ "sequence, organism, cell-line, phenotype, pedigree, and population samples require provenance and consent/authority framing"
      ∷ "neuroimaging and connectome use requires BIDS/FAIR metadata, dataset checksum, and selection receipts"
      ∷ "clinical validity and utility require clinical authority receipts and are not inferred from genetic or measurement data alone"
      ∷ []
  ; biologyLawTargets =
      "central dogma information flow"
      ∷ "Mendelian inheritance"
      ∷ "Hardy-Weinberg equilibrium"
      ∷ "Michaelis-Menten kinetics"
      ∷ "Fick diffusion law"
      ∷ "Nernst membrane potential"
      ∷ "Goldman-Hodgkin-Katz membrane equation"
      ∷ "logistic population growth"
      ∷ "Lotka-Volterra interaction model"
      ∷ "Hill binding equation"
      ∷ []
  ; repoBiologySurfaces =
      "DASHI/Biology/ProteinHormoneChemistryCellBridge.agda"
      ∷ "DASHI/Biology/CellDifferentiationCommunicationBridge.agda"
      ∷ "DASHI/Biology/GenomeSensorimotorConnectomeBridge.agda"
      ∷ "DASHI/Physics/Closure/DevelopmentalGenomicInverseBridge.agda"
      ∷ "DASHI/Interop/PhysicsChemistryBiologyDNAUnificationDischarge.agda"
      ∷ "DASHI/Interop/ObservationTransportSpine.agda"
      ∷ "DASHI/Biology/BioAnimalexicStackDischarge.agda"
      ∷ "DASHI/Biology/RetinalPerturbationObservationBridge.agda"
      ∷ "Docs/ProteinHormoneChemistryCellBridge.md"
      ∷ "Docs/GenomeSensorimotorConnectomeBridge.md"
      ∷ "Docs/BrainDNACrossoverStatus.md"
      ∷ []
  ; missingBiologyAdapters =
      "organism, cell-line, tissue, and session provenance authority"
      ∷ "sequence/sample checksum and assay protocol receipt"
      ∷ "reaction-network, kinetics, concentration, and transport calibration"
      ∷ "intervention design, counterfactual boundary, and causal-identification receipt"
      ∷ "clinical validity, clinical utility, and regulatory/ethics authority"
      ∷ "neuroimaging/connectome dataset checksum and BIDS/FAIR metadata receipt"
      ∷ "developmental dynamics, morphogenesis, and genome-to-connectome calibration"
      ∷ "environment/context source and phenotype-condition authority"
      ∷ "holdout validation and reproducibility receipt"
      ∷ []
  ; structuredBiologyBridgePopulated = true
  ; structuredBiologyBridgePopulatedIsTrue = refl
  ; biologyCausationPromoted = false
  ; biologyCausationPromotedIsFalse = refl
  ; interventionPromoted = false
  ; interventionPromotedIsFalse = refl
  ; clinicalValidityAccepted = false
  ; clinicalValidityAcceptedIsFalse = refl
  ; genomeToConnectomeClosurePromoted = false
  ; genomeToConnectomeClosurePromotedIsFalse = refl
  ; brainStateRecoveryPromoted = false
  ; brainStateRecoveryPromotedIsFalse = refl
  ; externalInputOnly = true
  ; externalInputOnlyIsTrue = refl
  }

canonicalEmpiricalRuntimeKnownInputsReferenceReceipt :
  EmpiricalRuntimeKnownInputsReferenceReceipt
canonicalEmpiricalRuntimeKnownInputsReferenceReceipt = record
  { sourcePopulationReceipt = canonicalKnownInputsPopulationReceipt
  ; sourceAuthorityPolicyReceipt =
      canonicalAuthorityConsumptionPolicyReceipt
  ; empiricalRuntimeLawTargets =
      "source checksum and provenance law"
      ∷ "source artifact -> checksum -> projection -> comparison"
      ∷ "provider authority decision target"
      ∷ "PNF/ITIR parser projection and replay target"
      ∷ "residual table and severity/projection target"
      ∷ "comparison-law and covariance authority target"
      ∷ "holdout validation and empirical adequacy target"
      ∷ []
  ; providerAuthorityInputs =
      "HEPData/provider source URI"
      ∷ "provider record id and version"
      ∷ "source checksum"
      ∷ "observable definition"
      ∷ "transform/projection law"
      ∷ "comparison law"
      ∷ "covariance/unit/calibration metadata"
      ∷ "authority decision token"
      ∷ []
  ; runtimeAuthorityInputs =
      "runtime receipt id"
      ∷ "parser/reducer version"
      ∷ "source artifact checksum"
      ∷ "projection digest"
      ∷ "PNF emission receipt"
      ∷ "residual computation receipt"
      ∷ "replay command/environment receipt"
      ∷ "semantic adequacy review receipt"
      ∷ []
  ; repoEmpiricalRuntimeSurfaces =
      "DASHI/Physics/Closure/HEPDataProviderReceiptRequestPack.agda"
      ∷ "DASHI/Physics/Closure/HEPDataResidualProviderReceiptRequestPack.agda"
      ∷ "DASHI/Physics/Closure/HEPDataResidualBridgeAuthorityGate.agda"
      ∷ "DASHI/Physics/Closure/HEPDataEmpiricalAuthorityReceiptCollation.agda"
      ∷ "DASHI/Physics/Closure/HEPDataComparisonLawReceiptRequest.agda"
      ∷ "DASHI/Interop/PNFResidualConsumerReceiptRequestPack.agda"
      ∷ "DASHI/Interop/PNFResidualConsumerRuntimeProviderAttempt.agda"
      ∷ "DASHI/Interop/PNFResidualSpectralSeverityReceipt.agda"
      ∷ "DASHI/Interop/SenateFormalizationPNFAdapter.agda"
      ∷ "DASHI/Interop/SweetgrassCarrierSpine.agda"
      ∷ []
  ; missingEmpiricalRuntimeAdapters =
      "accepted provider authority token"
      ∷ "observable-class authority and source checksum"
      ∷ "transform/projection comparison law"
      ∷ "unit, uncertainty, covariance, and calibration receipt"
      ∷ "holdout dataset and validation protocol"
      ∷ "runtime environment, parser version, and replay receipt"
      ∷ "paired PNFEmissionReceipt values where residual consumers require them"
      ∷ "semantic adequacy and non-inspection boundary review"
      ∷ []
  ; receiptInfrastructurePopulated = true
  ; receiptInfrastructurePopulatedIsTrue = refl
  ; acceptedProviderAuthorityPromoted = false
  ; acceptedProviderAuthorityPromotedIsFalse = refl
  ; comparisonLawPromoted = false
  ; comparisonLawPromotedIsFalse = refl
  ; covarianceCalibrationPromoted = false
  ; covarianceCalibrationPromotedIsFalse = refl
  ; holdoutValidationAccepted = false
  ; holdoutValidationAcceptedIsFalse = refl
  ; runtimeReplayAuthorityAccepted = false
  ; runtimeReplayAuthorityAcceptedIsFalse = refl
  ; semanticAdequacyAccepted = false
  ; semanticAdequacyAcceptedIsFalse = refl
  ; empiricalAdequacyAccepted = false
  ; empiricalAdequacyAcceptedIsFalse = refl
  }

canonicalKnownConstantSlotCountIs40 :
  knownConstantSlotCount repoWideConstantsRegistry ≡ 40
canonicalKnownConstantSlotCountIs40 = refl

canonicalKnownLawSlotCountIs33 :
  knownLawSlotCount repoWideConstantsRegistry ≡ 33
canonicalKnownLawSlotCountIs33 = refl

canonicalAuthoritySourceSlotCountIs11 :
  authoritySourceSlotCount
    (ConstantsRegistry.authoritySourceSlots repoWideConstantsRegistry)
  ≡ 11
canonicalAuthoritySourceSlotCountIs11 = refl
