module DASHI.Physics.Closure.NSTriadKNOutputRelocationKatoPonceBonyScopeAudit where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator estimates and the Euler and Navier-Stokes equations".
-- Venue/year: Communications on Pure and Applied Mathematics 41 (1988),
-- 891--907.
-- DOI: 10.1002/cpa.3160410704.
-- Uses: the classical commutator/fractional-Leibniz fallback mechanism.
-- Relationship: relevant when a derivative cannot be relocated by the exact
-- Fourier transversality identity; it is not silently identified with the
-- literal output-low shell coefficient theorem.
--
-- Authors: Loukas Grafakos; Seungly Oh.
-- Title: "The Kato-Ponce Inequality".
-- Venue/year: Communications in Partial Differential Equations 39 (2014),
-- 1128--1157.
-- DOI: 10.1080/03605302.2013.822885.
-- arXiv/DataCite DOI: 10.48550/arXiv.1303.5144.
-- Uses: Littlewood--Paley diagonal decomposition, square functions and
-- frequency-index Cauchy--Schwarz.
-- Relationship: proof-pattern authority for the finite diagonal convolution
-- estimate, not a ready-made DASHI orbit/shell/Galerkin theorem.
--
-- Authors: Seungly Oh; Xinfeng Wu.
-- Title: "The Kato-Ponce Inequality with Polynomial Weights".
-- Venue/year: Mathematische Zeitschrift 302 (2022), 1489--1526.
-- DOI: 10.1007/s00209-022-03120-6.
-- arXiv/DataCite DOI: 10.48550/arXiv.2108.10412.
-- Relationship: records that arXiv:2108.10412 is the polynomial-weight paper,
-- not the Grafakos--Oh 2014 article used by the existing repository audit.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- Venue/year: Annales scientifiques de l'Ecole Normale Superieure 14 (1981),
-- 209--246.
-- DOI: 10.24033/asens.1404.
-- Relationship: source of the paraproduct decomposition.  For the output-low
-- DASHI row, the exact identity u_p dot q = u_p dot k already relocates the
-- derivative, so the remaining proof is finite Bernstein/Cauchy--Schwarz and
-- representation transport rather than a new commutator theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighHighToLowCancellationProgram as Relocation
import DASHI.Physics.Closure.NSTriadKNComplex3RelocationInstantiation as Concrete
import DASHI.Physics.Closure.NSTriadKNRationalDirectConvolutionBound as Direct
import DASHI.Physics.Closure.NSTriadKNOutputRelocationFiniteSquaredCoefficientMajorant as Finite

record OutputRelocationSourceScopeReceipt : Set where
  constructor receipt
  field
    exactRelocationIdentityClosed :
      Relocation.outputRelocationAlgebraTheoremClosed ≡ true
    concreteComplexRelocationClosed :
      Concrete.concreteComplexCarrierOutputRelocationClosed ≡ true
    finiteDirectConvolutionCoreClosed :
      Direct.finiteDirectConvolutionAlgebraClosed ≡ true
    finiteSquaredShellMajorantClosed :
      Finite.finiteSquaredOutputCoefficientMajorantClosed ≡ true

open OutputRelocationSourceScopeReceipt public

outputRelocationSourceScopeReceipt : OutputRelocationSourceScopeReceipt
outputRelocationSourceScopeReceipt = receipt
  Relocation.outputRelocationAlgebraTheoremClosedIsTrue
  Concrete.concreteComplexCarrierOutputRelocationClosedIsTrue
  Direct.finiteDirectConvolutionAlgebraClosedIsTrue
  Finite.finiteSquaredOutputCoefficientMajorantClosedIsTrue

arXiv2108IsOhWuPolynomialWeightPaper : Bool
arXiv2108IsOhWuPolynomialWeightPaper = true

grafakosOh2014IsArXiv1303 : Bool
grafakosOh2014IsArXiv1303 = true

katoPonceRequiredForOutputLowRelocationIdentity : Bool
katoPonceRequiredForOutputLowRelocationIdentity = false

katoPonceRemainsValidFallbackForUnfavourableAdjointRows : Bool
katoPonceRemainsValidFallbackForUnfavourableAdjointRows = true

bonyParaproductMechanismRecorded : Bool
bonyParaproductMechanismRecorded = true

outputLowPrimaryRouteIsFiniteRelocationBernsteinCauchySchwarz : Bool
outputLowPrimaryRouteIsFiniteRelocationBernsteinCauchySchwarz = true

arXiv2108IsOhWuPolynomialWeightPaperIsTrue :
  arXiv2108IsOhWuPolynomialWeightPaper ≡ true
arXiv2108IsOhWuPolynomialWeightPaperIsTrue = refl

grafakosOh2014IsArXiv1303IsTrue :
  grafakosOh2014IsArXiv1303 ≡ true
grafakosOh2014IsArXiv1303IsTrue = refl

katoPonceRequiredForOutputLowRelocationIdentityIsFalse :
  katoPonceRequiredForOutputLowRelocationIdentity ≡ false
katoPonceRequiredForOutputLowRelocationIdentityIsFalse = refl

katoPonceRemainsValidFallbackForUnfavourableAdjointRowsIsTrue :
  katoPonceRemainsValidFallbackForUnfavourableAdjointRows ≡ true
katoPonceRemainsValidFallbackForUnfavourableAdjointRowsIsTrue = refl

bonyParaproductMechanismRecordedIsTrue :
  bonyParaproductMechanismRecorded ≡ true
bonyParaproductMechanismRecordedIsTrue = refl

outputLowPrimaryRouteIsFiniteRelocationBernsteinCauchySchwarzIsTrue :
  outputLowPrimaryRouteIsFiniteRelocationBernsteinCauchySchwarz ≡ true
outputLowPrimaryRouteIsFiniteRelocationBernsteinCauchySchwarzIsTrue = refl
