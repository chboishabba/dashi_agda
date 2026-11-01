module DASHI.Physics.QuantumVacuum.ParallelPlateRegulatorFiniteParsevalWeldExact where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (map)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoTorusTrigonometricPolynomialExact as Torus
import DASHI.Physics.Closure.NSTriadKNLuoTorusTrigonometricParsevalExact as Parseval
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q
import DASHI.Physics.QuantumVacuum.ParallelPlateModeSpectrumCutsetExact as Cutset
import DASHI.Physics.QuantumVacuum.PerfectConductorFiniteCutoffParsevalBidiExact as FiniteParseval

------------------------------------------------------------------------
-- LITERAL REGULATOR LIST -> EXISTING TORUS PARSEVAL
------------------------------------------------------------------------

record RegulatorFiniteTorusParsevalWeld
    {r : Level}
    (F : C3.RealField r)
    {kernel : Casimir.CasimirScalarModel}
    (spectrum : Cutset.ParallelPlateSpectralModel kernel)
    (regulator : Cutset.ParallelPlateRegulator spectrum) : Set (lsuc r) where
  field
    separation : Q.Length
    cutoff : Cutset.Cutoff regulator

    torus : Torus.TorusCharacterIntegral F
    encode : Cutset.Mode spectrum → Torus.TorusTerm F (Torus.Mode torus)

    sameFiniteCutoffModeLabels : Set
    sameCoefficientNormalisation : Set
    physicalRegulatedEnergyMatchesTorusPolynomialEnergy : Set
    reading : String

open RegulatorFiniteTorusParsevalWeld public

asFiniteCutoffTorusRealisation :
  ∀ {r} {F : C3.RealField r} {kernel spectrum regulator} →
  RegulatorFiniteTorusParsevalWeld F {kernel} spectrum regulator →
  FiniteParseval.FiniteCutoffTorusRealisation F
asFiniteCutoffTorusRealisation
    {spectrum = spectrum} {regulator = regulator} W = record
  { FiniteParseval.PlateMode = Cutset.Mode spectrum
  ; FiniteParseval.plateModes =
      Cutset.plateModes regulator (separation W) (cutoff W)
  ; FiniteParseval.torus = torus W
  ; FiniteParseval.encode = encode W
  ; FiniteParseval.terms =
      map (encode W)
        (Cutset.plateModes regulator (separation W) (cutoff W))
  ; FiniteParseval.termsAreEncodedPlateModes = refl
  ; FiniteParseval.sameCutoffModeLabels = sameFiniteCutoffModeLabels W
  ; FiniteParseval.sameCoefficientNormalisation = sameCoefficientNormalisation W
  ; FiniteParseval.physicalEnergyMatchesTorusEnergy =
      physicalRegulatedEnergyMatchesTorusPolynomialEnergy W
  ; FiniteParseval.reading = reading W
  }

literalRegulatorFiniteParseval :
  ∀ {r} {F : C3.RealField r} {kernel spectrum regulator} →
  (W : RegulatorFiniteTorusParsevalWeld F {kernel} spectrum regulator) →
  let R = asFiniteCutoffTorusRealisation W
  in
  Parseval.physicalPolynomialEnergy
      (FiniteParseval.torus R) (FiniteParseval.terms R)
  ≡ Parseval.polynomialCoefficientEnergy
      (FiniteParseval.torus R) (FiniteParseval.terms R) (FiniteParseval.terms R)
literalRegulatorFiniteParseval W =
  FiniteParseval.finiteCutoffParseval (asFiniteCutoffTorusRealisation W)
