module Ontology.DNA.SantaLucia1998SI where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (negsuc)
open import Agda.Builtin.Nat using (Nat; _*_)

open import DASHI.Physics.Units.SI using
  ( DecimalScale; tenTo; deciScale; centiScale
  ; Quantity; quantity
  ; MolarEnergy; MolarEntropy
  ; Unit; joulePerMole; joulePerMoleKelvin
  )
open import Ontology.DNA.SantaLucia1998Thermodynamics using
  ( SignedScaled; scaled
  ; ThermodynamicTriple; thermo
  ; WatsonCrickStack; AA-TT; GC-CG; unified1998
  )

------------------------------------------------------------------------
-- Exact conventional-to-SI conversions.
--
-- Input encodings:
--   delta H   magnitude n = n × 0.1 kcal mol^-1
--   delta S   magnitude n = n × 0.1 cal mol^-1 K^-1
--   delta G37 magnitude n = n × 0.01 kcal mol^-1
--
-- Exact identities:
--   0.1 kcal = 418.4 J = 4184 decijoule
--   0.1 cal  = 0.4184 J = 4184 × 10^-4 J
--   0.01 kcal = 41.84 J = 4184 centijoule

entropyScale : DecimalScale
entropyScale = tenTo (negsuc 3)

copySign : ∀ {d s} → SignedScaled → Nat → Quantity d s
copySign (scaled sign oldMagnitude) newMagnitude = quantity sign newMagnitude

enthalpyToSI : SignedScaled → Quantity MolarEnergy deciScale
enthalpyToSI x@(scaled sign n) = copySign x (n * 4184)

entropyToSI : SignedScaled → Quantity MolarEntropy entropyScale
entropyToSI x@(scaled sign n) = copySign x (n * 4184)

freeEnergyToSI : SignedScaled → Quantity MolarEnergy centiScale
freeEnergyToSI x@(scaled sign n) = copySign x (n * 4184)

record SIThermodynamicTriple : Set where
  constructor siThermo
  field
    deltaH : Quantity MolarEnergy deciScale
    deltaS : Quantity MolarEntropy entropyScale
    deltaG37 : Quantity MolarEnergy centiScale
    deltaHUnit : Unit MolarEnergy
    deltaSUnit : Unit MolarEntropy
    deltaG37Unit : Unit MolarEnergy

unified1998SI : WatsonCrickStack → SIThermodynamicTriple
unified1998SI stack with unified1998 stack
... | thermo h s g =
  siThermo
    (enthalpyToSI h)
    (entropyToSI s)
    (freeEnergyToSI g)
    joulePerMole
    joulePerMoleKelvin
    joulePerMole

AA-TT-H-SI :
  SIThermodynamicTriple.deltaH (unified1998SI AA-TT)
    ≡ quantity true (79 * 4184)
AA-TT-H-SI = refl

GC-CG-G-SI :
  SIThermodynamicTriple.deltaG37 (unified1998SI GC-CG)
    ≡ quantity true (224 * 4184)
GC-CG-G-SI = refl
