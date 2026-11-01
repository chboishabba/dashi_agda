module DASHI.Moonshine.OggPrimeModularControlRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Data.Integer using (+_; -[1+_])

import DASHI.Foundations.BinaryPolyhedralMcKayDimensionExact as McKay
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Moonshine.CandidateLevelExternalOggPredicateExact as External
import DASHI.Moonshine.CandidateLevelRepresentationHeckeSquareExact as Candidate
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.PrimeFrickeGenusControlExact as Fricke
import DASHI.Moonshine.RamanujanTauCandidateFingerprintJ0To35Exact as Tau

------------------------------------------------------------------------
-- The unbiased prime matrix contains every odd prime control below 72.
------------------------------------------------------------------------

nineteenOddPrimeControls :
  Matrix.listCount Matrix.allOddPrimeControlsUnder72 ≡ 19
nineteenOddPrimeControls = Matrix.oddPrimeControlCountIsNineteen

fiveNonOggPrimeControls :
  Matrix.listCount Matrix.nonOggPrimeControls ≡ 5
fiveNonOggPrimeControls = Matrix.nonOggPrimeControlCountIsFive

prime37Negative : Matrix.externalOggLabel Matrix.prime37 ≡ false
prime37Negative = Matrix.prime37ExternallyNegative

prime43Negative : Matrix.externalOggLabel Matrix.prime43 ≡ false
prime43Negative = Matrix.prime43ExternallyNegative

prime53Negative : Matrix.externalOggLabel Matrix.prime53 ≡ false
prime53Negative = Matrix.prime53ExternallyNegative

prime61Negative : Matrix.externalOggLabel Matrix.prime61 ≡ false
prime61Negative = Matrix.prime61ExternallyNegative

prime67Negative : Matrix.externalOggLabel Matrix.prime67 ≡ false
prime67Negative = Matrix.prime67ExternallyNegative

------------------------------------------------------------------------
-- The internally computed modular genus-zero column reproduces the external
-- odd-prime Ogg labels on this finite scan.
------------------------------------------------------------------------

frickeZeroLocusMatchesExternalOgg :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  Fricke.frickeGenusZero prime ≡ Matrix.externalOggLabel prime
frickeZeroLocusMatchesExternalOgg =
  Fricke.frickeGenusZeroMatchesExternalOggLabel

prime37PositiveFrickeGenus :
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime37) ≡ 1
prime37PositiveFrickeGenus = Fricke.prime37FrickeGenusIsOne

prime43PositiveFrickeGenus :
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime43) ≡ 1
prime43PositiveFrickeGenus = Fricke.prime43FrickeGenusIsOne

prime53PositiveFrickeGenus :
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime53) ≡ 1
prime53PositiveFrickeGenus = Fricke.prime53FrickeGenusIsOne

prime61PositiveFrickeGenus :
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime61) ≡ 1
prime61PositiveFrickeGenus = Fricke.prime61FrickeGenusIsOne

prime67PositiveFrickeGenus :
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime67) ≡ 2
prime67PositiveFrickeGenus = Fricke.prime67FrickeGenusIsTwo

------------------------------------------------------------------------
-- External authority remains separately typed; the finite agreement above is
-- not used to redefine the external predicate.
------------------------------------------------------------------------

external37StillNegative : External.ExternalOggAt 37 → ⊥
external37StillNegative = External.dimension37IsNotExternallyOgg

external61StillNegative : External.ExternalOggAt 61 → ⊥
external61StillNegative = External.dimension61IsNotExternallyOgg

------------------------------------------------------------------------
-- The arithmetic fingerprint exists on both Ogg and non-Ogg controls.
------------------------------------------------------------------------

tau29OggControl :
  Tau.tauAtCandidateLevel (Candidate.spatialLevel Spin.j14)
  ≡ + 128406630
tau29OggControl = Tau.tauAt29

tau35CompositeControl :
  Tau.tauAtCandidateLevel (Candidate.spatialLevel Spin.j17)
  ≡ -[1+ 80873519 ]
tau35CompositeControl = Tau.tauAt35

------------------------------------------------------------------------
-- p=2 remains an SU(2) boundary; the McKay skeleton gives an independent
-- exceptional-symmetry neighbour rather than forcing p=2 through SO(3).
------------------------------------------------------------------------

spinorDimensionTwo : Spin.su2Dimension 1 ≡ 2
spinorDimensionTwo = McKay.naturalSU2DoubletDimensionIsTwo

e6BinaryTetrahedralOrder24 : McKay.e6DimensionSquareSum ≡ 24
e6BinaryTetrahedralOrder24 = McKay.e6BinaryTetrahedralOrder

e7BinaryOctahedralOrder48 : McKay.e7DimensionSquareSum ≡ 48
e7BinaryOctahedralOrder48 = McKay.e7BinaryOctahedralOrder

e8BinaryIcosahedralOrder120 : McKay.e8DimensionSquareSum ≡ 120
e8BinaryIcosahedralOrder120 = McKay.e8BinaryIcosahedralOrder

e8DoubletDimensionEquation :
  (node : McKay.E8Node) →
  2 * McKay.e8Dimension node
  ≡ McKay.sumNodeDimensions McKay.e8Dimension (McKay.e8Neighbours node)
e8DoubletDimensionEquation = McKay.e8McKayDimensionEquation

------------------------------------------------------------------------
-- The representation/modular exceptional-locus identification remains open.
------------------------------------------------------------------------

candidateExceptionalLocusNotDeclaredClosed :
  Candidate.exceptionalLocusEqualityConstructed
    Candidate.canonicalCandidateLevelSquareBoundary
  ≡ false
candidateExceptionalLocusNotDeclaredClosed = refl
