module Ontology.DNA.SantaLucia1998Thermodynamics where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source-backed unified DNA nearest-neighbour parameters.
--
-- Primary source:
-- John SantaLucia Jr., PNAS 95 (1998), 1460-1465.
-- DOI 10.1073/pnas.95.4.1460; PMID 9465037; PMCID PMC19045.
--
-- Values below use the conventional unified Watson-Crick table.  Energies are
-- stored as signed fixed-point integers to avoid silently importing floating
-- point semantics into theorem statements.

record SignedScaled : Set where
  constructor scaled
  field
    negative : Bool
    magnitude : Nat

negativeScaled : Nat → SignedScaled
negativeScaled n = scaled true n

record ThermodynamicTriple : Set where
  constructor thermo
  field
    deltaH-kcal-times10 : SignedScaled
    deltaS-cal-times10 : SignedScaled
    deltaG37-kcal-times100 : SignedScaled

data WatsonCrickStack : Set where
  AA-TT AT-TA TA-AT CA-GT GT-CA CT-GA GA-CT CG-GC GC-CG GG-CC : WatsonCrickStack

unified1998 : WatsonCrickStack → ThermodynamicTriple
unified1998 AA-TT = thermo (negativeScaled 79)  (negativeScaled 222) (negativeScaled 100)
unified1998 AT-TA = thermo (negativeScaled 72)  (negativeScaled 204) (negativeScaled 88)
unified1998 TA-AT = thermo (negativeScaled 72)  (negativeScaled 213) (negativeScaled 58)
unified1998 CA-GT = thermo (negativeScaled 85)  (negativeScaled 227) (negativeScaled 145)
unified1998 GT-CA = thermo (negativeScaled 84)  (negativeScaled 224) (negativeScaled 144)
unified1998 CT-GA = thermo (negativeScaled 78)  (negativeScaled 210) (negativeScaled 128)
unified1998 GA-CT = thermo (negativeScaled 82)  (negativeScaled 222) (negativeScaled 130)
unified1998 CG-GC = thermo (negativeScaled 106) (negativeScaled 272) (negativeScaled 217)
unified1998 GC-CG = thermo (negativeScaled 98)  (negativeScaled 244) (negativeScaled 224)
unified1998 GG-CC = thermo (negativeScaled 80)  (negativeScaled 199) (negativeScaled 184)

record ParameterSource : Set where
  constructor parameterSource
  field
    citation : String
    doi : String
    pmid : String
    sampleCount : Nat
    unifiedWatsonCrickTable : Bool

santaLucia1998Source : ParameterSource
santaLucia1998Source = parameterSource
  "SantaLucia J Jr. A unified view of polymer, dumbbell, and oligonucleotide DNA nearest-neighbor thermodynamics. PNAS 95:1460-1465 (1998)."
  "10.1073/pnas.95.4.1460"
  "9465037"
  108
  true

record MismatchSource : Set where
  constructor mismatchSource
  field
    citation : String
    doi : String
    directlyMeasuredOligomers : Nat
    literatureOligomers : Nat
    contextDependent : Bool

allawiSantaLuciaGT1997 : MismatchSource
allawiSantaLuciaGT1997 = mismatchSource
  "Allawi HT, SantaLucia J Jr. Thermodynamics and NMR of internal G.T mismatches in DNA. Biochemistry 36:10581-10594 (1997)."
  "10.1021/bi962590c"
  39
  6
  true

record VersionedUnifiedTable : Set where
  constructor versionedUnifiedTable
  field
    version : Nat
    source : ParameterSource
    stack : WatsonCrickStack → ThermodynamicTriple
    unitsPinned : Bool

versionedSantaLucia1998 : VersionedUnifiedTable
versionedSantaLucia1998 = versionedUnifiedTable 1998 santaLucia1998Source unified1998 true

AA-TT-deltaG37 : ThermodynamicTriple.deltaG37-kcal-times100 (unified1998 AA-TT) ≡ negativeScaled 100
AA-TT-deltaG37 = refl

GC-CG-deltaG37 : ThermodynamicTriple.deltaG37-kcal-times100 (unified1998 GC-CG) ≡ negativeScaled 224
GC-CG-deltaG37 = refl
