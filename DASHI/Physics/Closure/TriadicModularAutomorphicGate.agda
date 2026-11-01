module DASHI.Physics.Closure.TriadicModularAutomorphicGate where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.TriadicSectorQSeries as QS

------------------------------------------------------------------------
-- A genuine modular/automorphic lane begins with a transformation law.

record ModularTransformationGate
  (C : QS.QSeriesCarrier)
  (T : QS.SectorTraceTower C) : Set₁ where
  field
    sector : QS.Sector T

    ParameterDomain : Set
    ModularElement : Set

    act : ModularElement → ParameterDomain → ParameterDomain
    automorphyFactor :
      ModularElement →
      ParameterDomain →
      QS.Coeff C

    evaluateSeries : ParameterDomain → QS.Coeff C

    weight : Nat
    level : Nat

    transformationLaw :
      (g : ModularElement) →
      (τ : ParameterDomain) →
      evaluateSeries (act g τ)
      ≡ QS._*ᶜ_ C
          (automorphyFactor g τ)
          (evaluateSeries τ)

    coefficientAgreement :
      (n : Nat) → Set

open ModularTransformationGate public

------------------------------------------------------------------------
-- Eisenstein/cusp basis decomposition.
--
-- assembleCoefficient is deliberately explicit: an instance must implement
-- the finite basis sum and prove that it reconstructs every tracked coefficient.

record EisensteinBasisGate
  (C : QS.QSeriesCarrier)
  (T : QS.SectorTraceTower C)
  (M : ModularTransformationGate C T) : Set₁ where
  field
    EisensteinIndex : Set
    CuspIndex : Set

    eisensteinCoordinate : EisensteinIndex → QS.Coeff C
    cuspCoordinate : CuspIndex → QS.Coeff C

    eisensteinCoefficient :
      EisensteinIndex →
      Nat →
      QS.Coeff C

    cuspCoefficient :
      CuspIndex →
      Nat →
      QS.Coeff C

    assembleCoefficient : Nat → QS.Coeff C

    basisReconstruction :
      (n : Nat) →
      assembleCoefficient n
      ≡ QS.traceCoefficient T n (sector M)

    finiteDimensionalBasis : Set
    basisLinearIndependence : Set

open EisensteinBasisGate public

------------------------------------------------------------------------
-- Hecke and p-adic interpolation gates.

record HeckeEigenGate
  (C : QS.QSeriesCarrier)
  (T : QS.SectorTraceTower C)
  (M : ModularTransformationGate C T) : Set₁ where
  field
    heckeProbe : QS.HeckeProbe C T
    probeTracksModularSector :
      QS.HeckeProbe.sector heckeProbe ≡ sector M
    simultaneousEigenReceipt : Set
    commutingHeckeOperators : Set

open HeckeEigenGate public

record PAdicWeightFamilyGate
  (C : QS.QSeriesCarrier) : Set₁ where
  field
    WeightSpace : Set
    PAdicParameter : Set
    weightCoordinate : PAdicParameter → WeightSpace
    familyCoefficient : PAdicParameter → Nat → QS.Coeff C
    interpolationLaw : (parameter : PAdicParameter) → Set
    overconvergenceOrRadiusControl : Set

open PAdicWeightFamilyGate public

------------------------------------------------------------------------
-- Compression by modular coordinates.

record AutomorphicCompressionReceipt
  (C : QS.QSeriesCarrier)
  (T : QS.SectorTraceTower C)
  (M : ModularTransformationGate C T) : Set₁ where
  field
    eisensteinGate : EisensteinBasisGate C T M
    heckeGate : HeckeEigenGate C T M

    LatentCoordinate : Set
    encodeCoordinates : LatentCoordinate
    decodeCoefficient : LatentCoordinate → Nat → QS.Coeff C

    exactCoefficientRecovery :
      (n : Nat) →
      decodeCoefficient encodeCoordinates n
      ≡ QS.traceCoefficient T n (sector M)

    descriptionLengthReduced : Set

open AutomorphicCompressionReceipt public

------------------------------------------------------------------------
-- Promotion boundary.

modularGateStatement : String
modularGateStatement =
  "Eisenstein, cusp, Hecke, and p-adic-family structure is available only after a genuine modular transformation law and coefficient agreement are supplied."

modularGateBoundary : String
modularGateBoundary =
  "A depth trace, partition function, theta candidate, or q-series name is not by itself a modular form. No Eisenstein expansion or automorphic compression is promoted without ModularTransformationGate and EisensteinBasisGate receipts."
