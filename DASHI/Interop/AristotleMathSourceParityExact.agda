module DASHI.Interop.AristotleMathSourceParityExact where

------------------------------------------------------------------------
-- UPSTREAM SOURCE / ATTRIBUTION
--
-- User-supplied Aristotle mathematics archive used on PR #555.
-- The upstream README states that the project was edited by Aristotle
-- (Harmonic), requests @Aristotle-Harmonic attribution, and requests the
-- commit trailer:
--
--   Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
--
-- This module is provenance/parity data.  It does not claim that Agda
-- kernel-checks the supplied Lean proofs, and it does not infer James Michael
-- DuPont authorship for this particular archive.  The separate Wikidata
-- snapshot retains its own JMD/Aristotle provenance.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

aristotleMathArchiveSha256 : String
aristotleMathArchiveSha256 = "2f7e5ec034d22e0d6acad21a6c5ea47ff4f1b16f190a9a60255141f5cf0aeed2"

aristotleMathCombinedLeanSha256 : String
aristotleMathCombinedLeanSha256 = "b506c87807bcfe3b9ffe4c7aa2a7cba2bbdd974e0981237f8d11d64bcda1dc83"

aristotleMathModuleCount : Nat
aristotleMathModuleCount = 18

aristotleMathLeanLineCount : Nat
aristotleMathLeanLineCount = 4302

aristotleMathNamedDeclarationCount : Nat
aristotleMathNamedDeclarationCount = 409

data ParityStatus : Set where
  nearCoreParity substantialCore partial minimalPartial unportedCore unported aggregateOnly : ParityStatus

record AristotleMathModuleParity : Set where
  constructor aristotleMathModuleParity
  field
    sourceModule : String
    sourceSha256 : String
    sourceLines : Nat
    sourceNamedDeclarations : Nat
    status : ParityStatus
    dashiTargets : String
    remainingGap : String

open AristotleMathModuleParity public

archimedes369Parity : AristotleMathModuleParity
archimedes369Parity = aristotleMathModuleParity
  "RequestProject.Archimedes369"
  "3642fe253921e95da056302654ea76aa6da0564ccfc762897e70ed94f273bc11"
  345
  39
  unported
  "none"
  "requires constructed pi/trigonometric/order/limit substrate; polygon sandwich, doubling ladder, exact rungs, nine-gon cubic/enclosure and limits remain"

archimedesNinetySixParity : AristotleMathModuleParity
archimedesNinetySixParity = aristotleMathModuleParity
  "RequestProject.ArchimedesNinetySix"
  "b04468675150478726d53b966886de449b75f915b5210e5676d2db16c833aaf7"
  146
  9
  unported
  "none"
  "96-gon interval propagation and 223/71 < pi < 22/7 remain; blocked by constructive pi/trigonometric/order layer"

archimedesSpinParity : AristotleMathModuleParity
archimedesSpinParity = aristotleMathModuleParity
  "RequestProject.ArchimedesSpin"
  "47af5c78c46077c48ed1c51f856e694d1ba2a1b3714715b29ff9101dee2e52bd"
  366
  27
  unported
  "none"
  "polar radius GLB/LUB, swept annulus, frustum/revolution volume, convergence and modular-circle polygon symmetry remain"

baseGeneralParity : AristotleMathModuleParity
baseGeneralParity = aristotleMathModuleParity
  "RequestProject.BaseGeneral"
  "dca43f7dfc6e664b7c3086dfec2bf75cf3085be29c66c67a20a6bd56b9a1edda"
  288
  31
  partial
  "DASHI.Arithmetic.DecimalDigitalRootNonaryExact;DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact"
  "generic base-acts-as-one quotient principle present, but base-b digitalRoot/trinity cardinality/minimal-base theorem and ZMod9 vortex orbit partition/cardinalities are not source-parity"

deltaGraphParity : AristotleMathModuleParity
deltaGraphParity = aristotleMathModuleParity
  "RequestProject.DeltaGraph"
  "104475e0fdb956197817401c1765ca48269c1e2e3f75c4f14e1466302cc93dbb"
  179
  24
  partial
  "DASHI.Moonshine.RamanujanTauHecke23Exact;DASHI.Analysis.FiniteRealQSeriesReflectionExact"
  "selected tau identities and finite-q symmetry substrate ported; eta-product coefficient construction, tau table through 30, finite Ramanujan bound, mod-27 congruence, sigma equivalence, and plotted q-approx bounds remain"

deltaModularParity : AristotleMathModuleParity
deltaModularParity = aristotleMathModuleParity
  "RequestProject.DeltaModular"
  "13616656b8f7f6b585ae89a36251b2c74794dcac3f159d87073052dccead5fe7"
  323
  31
  partial
  "DASHI.Moonshine.EisensteinDiscriminantWeight12Exact;DASHI.Moonshine.ModularCurveJFrickeInterfaceExact"
  "weight-12 transformation of unnormalised E4^3-E6^2 derived from existing Eisenstein law; true eta^24 Delta, nonvanishing/holomorphy, E2/log-derivative proof, S/T normalization, conjugation/unit-circle reflection and arc phase theorem remain"

deltaWordGraphsParity : AristotleMathModuleParity
deltaWordGraphsParity = aristotleMathModuleParity
  "RequestProject.DeltaWordGraphs"
  "2aff96beec88c28999131f5ec06ecfe395f070bb7382dde3ea55a97659d0da34"
  272
  32
  partial
  "DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact;DASHI.Moonshine.Hecke23AntiparallelExact;DASHI.Moonshine.AristotleDeltaWordT2T3FiniteParityExact"
  "five source word multipliers and the certified m=1..3 T2/T3 comparison rows are ported; 60-term tau table, wider finite-range coefficient equalities, divisibility/trinity, norm/log/phase graph theorems remain"

fibVortexParity : AristotleMathModuleParity
fibVortexParity = aristotleMathModuleParity
  "RequestProject.FibVortex"
  "a93ad8757124c7aeb863c6813f3fc953be0665ad9d8b244f2367225983622560"
  121
  7
  nearCoreParity
  "DASHI.Arithmetic.FibonacciNonaryPeriodExact"
  "exact mod9 state period 24, minimality and every-fourth triadic residues ported; source Nat fib digitalRoot statement packaging and cycle-sum theorem remain"

hecke23Parity : AristotleMathModuleParity
hecke23Parity = aristotleMathModuleParity
  "RequestProject.Hecke23"
  "c433699f95c7f067c772fd9223e444869ba4e4e54907b37d4db34616572676bc"
  115
  10
  substantialCore
  "DASHI.Moonshine.AristotleHeckeRecurrenceCoreExact;DASHI.Moonshine.RamanujanTauHecke23Exact;DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact"
  "prime-power recurrence uniqueness and exact two-prime smooth assembly are ported together with low closed identities; full Nat HeckeSystem coprime packaging, divisor-count example, and source Set Smooth3 packaging remain"

heckeGeneralParity : AristotleMathModuleParity
heckeGeneralParity = aristotleMathModuleParity
  "RequestProject.HeckeGeneral"
  "a45235046a9f46c7fb0b8c86282db5be52f8637ee309096e0dfbc0b4b013c2cf"
  155
  8
  partial
  "DASHI.Moonshine.AristotleHeckeRecurrenceCoreExact;DASHI.Moonshine.AristotleHeckeGeneralPrimePowerDecompositionExact;DASHI.Moonshine.CandidateLevelRepresentationHeckeSquareExact"
  "stdlib constructive raw factorisation plus arbitrary-S closure on pairwise-coprime prime-power decompositions are ported; canonical grouping of raw repeated prime factors into prime-power blocks, finite separating bound, and a_zero_undetermined remain"

heckeWordsParity : AristotleMathModuleParity
heckeWordsParity = aristotleMathModuleParity
  "RequestProject.HeckeWords"
  "893eaa885ca57e4698767e38903a02e20702086cb0661e64f295b504d2589a03"
  223
  26
  substantialCore
  "DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact;DASHI.Moonshine.AristotleHeckeWordsSourceParityExact;DASHI.Moonshine.RamanujanTauHecke23Exact"
  "recursive finite word interpreter and all five source word normal forms are ported over the classical divisor-sum structure constants; generic CommRing/Finsupp evaluation presentation remains representation-distinct and source evalT packaging remains"

mainParity : AristotleMathModuleParity
mainParity = aristotleMathModuleParity
  "RequestProject.Main"
  "929b0bddef0b781f3fb42c7a99f252dc0bda7331f698104f7075e12ff637c52d"
  24
  0
  aggregateOnly
  "DASHI.Arithmetic.AristotleArithmeticEverything;DASHI.Moonshine.OggRepresentationReductionEverything"
  "source Main is import aggregator with no named declarations; DASHI aggregation exists but is not intended as theorem parity"

sieve23Parity : AristotleMathModuleParity
sieve23Parity = aristotleMathModuleParity
  "RequestProject.Sieve23"
  "ea9a01ce323cad055781c4649d16269f9cf2f81d6e10e6e8027673e5b0a7cda3"
  109
  12
  substantialCore
  "DASHI.Arithmetic.PrimeModSixSieveExact;DASHI.Arithmetic.SixWheelSieveCountExact;DASHI.Arithmetic.SixWheelCRTExact"
  "exact 6-wheel residue/count/CRT and prime >3 +/-1 mod6 core ported; source prime_digitalRoot and original Finset presentation not yet parity"

sieveGeneralParity : AristotleMathModuleParity
sieveGeneralParity = aristotleMathModuleParity
  "RequestProject.SieveGeneral"
  "eab92a4e044022465ca5e25bab13525147d5eb740bc1fb852cacfa781cc7611e"
  194
  13
  partial
  "DASHI.Arithmetic.FinitePrimeProductSieveExact"
  "generic product-coordinate survivor count ported; source arbitrary finite-prime modulus, periodic block count, coprime/totient identification, and density formula remain"

t2vsT3Parity : AristotleMathModuleParity
t2vsT3Parity = aristotleMathModuleParity
  "RequestProject.T2vsT3"
  "33eda89c443c6060bc1cc3facee7b3154ebaf89f6abe4e2f0fdb3f0f1e9862ab"
  287
  34
  partial
  "DASHI.Moonshine.Hecke23AntiparallelExact;DASHI.Moonshine.AristotleDeltaWordT2T3FiniteParityExact"
  "division-free antiparallel relation plus certified m=1..3 product/difference/Lean-integer quotient/remainder plate are ported; wider finite table, power and trinity behavior remain"

t2vsT3DeltaParity : AristotleMathModuleParity
t2vsT3DeltaParity = aristotleMathModuleParity
  "RequestProject.T2vsT3Delta"
  "7a54bff35360ac70d89bcab98e220d50fa0d2ca2771921376649e2ee01233391"
  320
  31
  minimalPartial
  "DASHI.Moonshine.Hecke23AntiparallelExact;DASHI.Analysis.FiniteRealQSeriesReflectionExact"
  "generic q-series substrate exists, but six panel identities, masks/splits, non-rescaling proofs and logarithmic power panel are not ported"

tesla369Parity : AristotleMathModuleParity
tesla369Parity = aristotleMathModuleParity
  "RequestProject.Tesla369"
  "fdce91aae59877bbbc31dbc96ab86547debb0555e624bec365fd60d63d8faf10"
  304
  29
  partial
  "DASHI.Arithmetic.DecimalDigitalRootNonaryExact;Base369;DASHI.Foundations.Base369NonaryTruthRing"
  "casting-out-nines core and 1..9<->Z/9 chart ported; Nat recursive digitalRoot/repeatedDigitSum, trinity generation/closure, and exact doubling 6-cycle theorem not yet source-parity"

verticalWallsParity : AristotleMathModuleParity
verticalWallsParity = aristotleMathModuleParity
  "RequestProject.VerticalWalls"
  "24619f9250457c3e9e99f52f271f36656ceb836caed098f2a08846503bed3dc7"
  531
  46
  partial
  "DASHI.Analysis.FiniteRealQSeriesReflectionExact"
  "real-coefficient finite-q conjugation/reflection and fixed-phase real-axis core ported; half-integer wall classification, zero-free phase constancy, derivative/gradient/orthogonality, and y>=5 Delta sign bounds remain"

allAristotleMathModuleParity : List AristotleMathModuleParity
allAristotleMathModuleParity =
  archimedes369Parity ∷
  archimedesNinetySixParity ∷
  archimedesSpinParity ∷
  baseGeneralParity ∷
  deltaGraphParity ∷
  deltaModularParity ∷
  deltaWordGraphsParity ∷
  fibVortexParity ∷
  hecke23Parity ∷
  heckeGeneralParity ∷
  heckeWordsParity ∷
  mainParity ∷
  sieve23Parity ∷
  sieveGeneralParity ∷
  t2vsT3Parity ∷
  t2vsT3DeltaParity ∷
  tesla369Parity ∷
  verticalWallsParity ∷
  []

------------------------------------------------------------------------
-- Boundary: inventory completeness and semantic parity are different facts.
------------------------------------------------------------------------

record AristotleMathParityBoundary : Set where
  field
    sourceInventoryComplete : Set
    declarationInventoryExternalTSV : Set
    allModulesSemanticallyPorted : Set

-- Intentionally no canonical inhabitant: the source inventory is complete,
-- but the current parity ledger explicitly contains unported modules.
