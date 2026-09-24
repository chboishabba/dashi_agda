module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseHistoricalMechanicsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact as Config

------------------------------------------------------------------------
-- SOURCE-REPRODUCTION MECHANICS CONTEXT
--
-- Li, Liu & Ji 2015 explicitly report the principal LT-MD mechanics choices:
-- GROMACS, AMBER ffamber03, Carlson/Meagher ATP/AMP polyphosphate parameters,
-- TIP3P water, PME electrostatics, pH-7-style residue protonation, Mg ions for
-- neutralization, 300 K, 1 bar, Nose-Hoover thermostat, Parrinello-Rahman
-- pressure coupling, LINCS H-bond constraints, 2 fs production timestep, and
-- 10 A nonbonded cutoff.  These method identities/settings are source-paid.
-- Exact parameter-file bytes and a bit-for-bit executable reproduction are not.
------------------------------------------------------------------------

liLiuJiSource : Attribution.AttributedSource
liLiuJiSource = Attr.liLiuJiSource

articleDOI = Attr.articleDOI
articlePMID = Attr.articlePMID
articlePMCID = Attr.articlePMCID
articleOpenAlex = Attr.articleOpenAlex
articleQID = Attr.articleQID

historicalMechanicsDeweyCoordinate : String
historicalMechanicsDeweyCoordinate =
  "exact article-method Dewey coordinate unresolved; DOI/PMID/PMCID/OpenAlex retained"

------------------------------------------------------------------------
-- Independently identified method-lineage sources.  Their citations identify
-- the named methods; Li-Liu-Ji remains the authority for which choices were
-- actually used in the AdK simulations.
------------------------------------------------------------------------

ffamber03Source : Attribution.AttributedSource
ffamber03Source = Attribution.mkDOISource
  "Duan et al."
  "A point-charge force field for molecular mechanics simulations of proteins based on condensed-phase quantum mechanical calculations"
  "Journal of Computational Chemistry"
  "2003"
  "10.1002/jcc.10349"
  "https://doi.org/10.1002/jcc.10349"
  Attribution.academicArticleSource
  "method-lineage source for the ff03/ffamber03 protein force-field family; does not by itself prove Li-Liu-Ji parameter-file identity"
  Attribution.publicAttribution

polyphosphateParameterSource : Attribution.AttributedSource
polyphosphateParameterSource = Attribution.mkDOISource
  "Meagher, Redman and Carlson"
  "Development of polyphosphate parameters for use with the AMBER force field"
  "Journal of Computational Chemistry"
  "2003"
  "10.1002/jcc.10262"
  "https://doi.org/10.1002/jcc.10262"
  Attribution.academicArticleSource
  "method-lineage source for ATP/ADP/polyphosphate AMBER parameters cited by the AdK methods; citation does not instantiate a topology"
  Attribution.publicAttribution

tip3pSource : Attribution.AttributedSource
tip3pSource = Attribution.mkDOISource
  "Jorgensen, Chandrasekhar, Madura, Impey and Klein"
  "Comparison of simple potential functions for simulating liquid water"
  "Journal of Chemical Physics"
  "1983"
  "10.1063/1.445869"
  "https://doi.org/10.1063/1.445869"
  Attribution.academicArticleSource
  "method-lineage source for TIP3P water; Li-Liu-Ji separately pay use of TIP3P in the AdK system"
  Attribution.publicAttribution

pmeSource : Attribution.AttributedSource
pmeSource = Attribution.mkDOISource
  "Essmann et al."
  "A smooth particle mesh Ewald method"
  "Journal of Chemical Physics"
  "1995"
  "10.1063/1.470117"
  "https://doi.org/10.1063/1.470117"
  Attribution.academicArticleSource
  "method-lineage source for smooth particle-mesh Ewald electrostatics; not an AdK numerical result"
  Attribution.publicAttribution

hooverSource : Attribution.AttributedSource
hooverSource = Attribution.mkDOISource
  "William G. Hoover"
  "Canonical dynamics: Equilibrium phase-space distributions"
  "Physical Review A"
  "1985"
  "10.1103/PhysRevA.31.1695"
  "https://doi.org/10.1103/PhysRevA.31.1695"
  Attribution.academicArticleSource
  "method-lineage source for the Hoover component of Nose-Hoover canonical dynamics; Li-Liu-Ji separately report their thermostat choice"
  Attribution.publicAttribution

parrinelloRahmanSource : Attribution.AttributedSource
parrinelloRahmanSource = Attribution.mkDOISource
  "M. Parrinello and A. Rahman"
  "Polymorphic transitions in single crystals: A new molecular dynamics method"
  "Journal of Applied Physics"
  "1981"
  "10.1063/1.328693"
  "https://doi.org/10.1063/1.328693"
  Attribution.academicArticleSource
  "method-lineage source for Parrinello-Rahman cell/pressure dynamics; not an AdK pressure measurement"
  Attribution.publicAttribution

lincsSource : Attribution.AttributedSource
lincsSource = Attribution.mkDOISource
  "Hess, Bekker, Berendsen and Fraaije"
  "LINCS: A linear constraint solver for molecular simulations"
  "Journal of Computational Chemistry"
  "1997"
  "10.1002/(SICI)1096-987X(199709)18:12<1463::AID-JCC4>3.0.CO;2-H"
  "https://doi.org/10.1002/(SICI)1096-987X(199709)18:12%3C1463::AID-JCC4%3E3.0.CO;2-H"
  Attribution.academicArticleSource
  "method-lineage source for LINCS bond constraints; Li-Liu-Ji separately pay use on bonds involving hydrogen"
  Attribution.publicAttribution

gromacs4Source : Attribution.AttributedSource
gromacs4Source = Attribution.mkDOISource
  "Hess, Kutzner, van der Spoel and Lindahl"
  "GROMACS 4: Algorithms for Highly Efficient, Load-Balanced, and Scalable Molecular Simulation"
  "Journal of Chemical Theory and Computation"
  "2008"
  "10.1021/ct700301q"
  "https://doi.org/10.1021/ct700301q"
  Attribution.academicArticleSource
  "software-method lineage for GROMACS; exact executable build/version used by Li-Liu-Ji remains a separate reproduction coordinate"
  Attribution.publicAttribution

methodSources : List Attribution.AttributedSource
methodSources =
  liLiuJiSource ∷ ffamber03Source ∷ polyphosphateParameterSource ∷
  tip3pSource ∷ pmeSource ∷ hooverSource ∷ parrinelloRahmanSource ∷
  lincsSource ∷ gromacs4Source ∷ []

record MethodExternalIdentity : Set where
  constructor method-external-identity
  field
    label : String
    doi : String
    qidStatus : String
    deweyCoordinate : String
    role : String
open MethodExternalIdentity public

ffamber03Identity : MethodExternalIdentity
ffamber03Identity = method-external-identity
  "ffamber03 lineage" "10.1002/jcc.10349"
  "source-article QID unresolved in this tranche"
  "exact article-level Dewey unresolved"
  "method identity only; not parameter-file bytes"

polyphosphateIdentity : MethodExternalIdentity
polyphosphateIdentity = method-external-identity
  "Meagher-Redman-Carlson polyphosphate parameters" "10.1002/jcc.10262"
  "source-article QID unresolved in this tranche"
  "exact article-level Dewey unresolved"
  "ATP/AMP parameter-method identity only; exact Li-Liu-Ji topology/parameter manifestation remains separate"

tip3pIdentity : MethodExternalIdentity
tip3pIdentity = method-external-identity
  "TIP3P" "10.1063/1.445869"
  "source-article QID unresolved in this tranche"
  "exact article-level Dewey unresolved"
  "water-model identity only"

pmeIdentity : MethodExternalIdentity
pmeIdentity = method-external-identity
  "smooth PME" "10.1063/1.470117"
  "source-article QID unresolved in this tranche"
  "exact article-level Dewey unresolved"
  "electrostatics-method identity only"

lincsIdentity : MethodExternalIdentity
lincsIdentity = method-external-identity
  "LINCS" "10.1002/(SICI)1096-987X(199709)18:12<1463::AID-JCC4>3.0.CO;2-H"
  "source-article QID unresolved in this tranche"
  "exact article-level Dewey unresolved"
  "constraint-method identity only"

------------------------------------------------------------------------
-- Source-paid AdK mechanics settings.
------------------------------------------------------------------------

record HistoricalMechanicsContext : Set where
  constructor historical-mechanics-context
  field
    source : Attribution.AttributedSource
    sourceLocator : String
    simulationEngine : String
    forceField : String
    nucleotideParameterReference : String
    waterModel : String
    approximateWaterBoxAngstrom : Nat
    approximateWaterMoleculeCount : Nat
    approximateSystemAtomCount : Nat
    protonationConvention : String
    magnesiumRole : String
    electrostatics : String
    minimization : String
    heatingProtocol : String
    productionTemperatureKelvin : Nat
    thermostat : String
    thermostatRelaxationTenthsPicosecond : Nat
    productionPressureBar : Nat
    pressureCoupling : String
    bondConstraint : String
    productionTimestepFemtoseconds : Nat
    nonbondedCutoffAngstrom : Nat
    neighborUpdateSteps : Nat
    exactEngineBuildPaid : Bool
    exactForceFieldParameterFileBytesPaid : Bool
    exactNucleotideParameterFileBytesPaid : Bool
    exactInitialTopologyBytesPaid : Bool
    exactMagnesiumPlacementAndCoordinationPaid : Bool
    bitwiseReproductionPaid : Bool
open HistoricalMechanicsContext public

canonicalHistoricalMechanicsContext : HistoricalMechanicsContext
canonicalHistoricalMechanicsContext = historical-mechanics-context
  liLiuJiSource
  "Li-Liu-Ji 2015 Materials and Methods, Long-time explicit MD simulations"
  "GROMACS"
  "AMBER ffamber03"
  "ATP and AMP explicit force-field parameters attributed by Li-Liu-Ji to their cited Carlson-lineage source; method DOI 10.1002/jcc.10262 retained here"
  "TIP3P"
  80
  15000
  50000
  "pH 7-style assignment stated by source: Asp deprotonated; His protonated only at N-3; full residue-by-residue protonation manifest not acquired here"
  "appropriate magnesium ions added to neutralize the system; exact positions/coordination are not paid by that sentence"
  "particle mesh Ewald for long-range electrostatics"
  "steepest descent, 10000 steps"
  "heated gradually to 300 K in 200 ps with positional restraints reduced from 2.39 to 0 kcal/(mol A^2)"
  300
  "Nose-Hoover"
  5
  1
  "Parrinello-Rahman"
  "LINCS on bonds with H atoms"
  2
  10
  10
  false false false false false false

------------------------------------------------------------------------
-- Structural configuration is still not the mechanics context.
------------------------------------------------------------------------

configurationSurface : Set
configurationSurface = Config.AtomisticConfiguration

record HistoricalMechanicsAttachment (configuration : Config.AtomisticConfiguration) : Set₁ where
  constructor historical-mechanics-attachment
  field
    mechanics : HistoricalMechanicsContext
    configurationMatchesHistoricalSystem : Set
    exactParameterManifestMatchesSourceMethod : Set
    protonationAssignmentMatchesConfiguration : Set
    magnesiumAssignmentMatchesConfiguration : Set
    executableEngineManifest : String
open HistoricalMechanicsAttachment public

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data MethodCitationCreatesExecutableReproduction : Set where
data ForceFieldNameCreatesParameterBytes : Set where
data PHSevenConventionCreatesResidueProtonationManifest : Set where
data MagnesiumNeutralizationCreatesCoordinationGeometry : Set where
data ModernEngineRunEqualsHistoricalReproduction : Set where

data MethodDOICreatesAdKTrajectory : Set where

methodCitationDoesNotCreateExecutableReproduction : MethodCitationCreatesExecutableReproduction → ⊥
methodCitationDoesNotCreateExecutableReproduction ()

forceFieldNameDoesNotCreateParameterBytes : ForceFieldNameCreatesParameterBytes → ⊥
forceFieldNameDoesNotCreateParameterBytes ()

phSevenDoesNotCreateResidueManifest : PHSevenConventionCreatesResidueProtonationManifest → ⊥
phSevenDoesNotCreateResidueManifest ()

magnesiumNeutralizationDoesNotCreateCoordination : MagnesiumNeutralizationCreatesCoordinationGeometry → ⊥
magnesiumNeutralizationDoesNotCreateCoordination ()

modernRunDoesNotEqualHistoricalReproduction : ModernEngineRunEqualsHistoricalReproduction → ⊥
modernRunDoesNotEqualHistoricalReproduction ()

methodDoiDoesNotCreateTrajectory : MethodDOICreatesAdKTrajectory → ⊥
methodDoiDoesNotCreateTrajectory ()

record AdKHistoricalMechanicsBoundary : Set where
  constructor adk-historical-mechanics-boundary
  field
    gromacsPaid : Bool
    ffamber03Paid : Bool
    nucleotideParameterMethodPaid : Bool
    tip3pPaid : Bool
    pmeLincsThermostatBarostatPaid : Bool
    sourceProtonationConventionPaid : Bool
    sourceMagnesiumNeutralizationRolePaid : Bool
    twoFemtosecondTimestepPaid : Bool
    tenAngstromCutoffPaid : Bool
    methodSourceDoisRetained : Bool
    methodSourceQidsExplicitlyUnresolved : Bool
    methodSourceDeweyExplicitlyUnresolved : Bool
    exactEngineBuildPaid : Bool
    exactParameterFileBytesPaid : Bool
    exactInitialTopologyPaid : Bool
    exactMagnesiumCoordinationPaid : Bool
    bitwiseReproductionPaid : Bool
    methodCitationCreatesExecutableReproduction : Bool
    forceFieldNameCreatesParameterBytes : Bool
    historicalModelEqualsModernValidationModel : Bool
open AdKHistoricalMechanicsBoundary public

canonicalAdKHistoricalMechanicsBoundary : AdKHistoricalMechanicsBoundary
canonicalAdKHistoricalMechanicsBoundary =
  adk-historical-mechanics-boundary
    true true true true true true true true true
    true true true
    false false false false false false false false
