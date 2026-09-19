module DASHI.Analysis.BishopContractiveCompartmentSeriesValidation where

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopContractiveCompartmentSeriesExact as P

majorantAbsoluteConvergenceRegression :
  (problem : P.BishopPolynomialGeometricCompartment) →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (P.compartmentMajorantTerm problem)
majorantAbsoluteConvergenceRegression =
  P.compartmentMajorantAbsolutelyConvergent

majorantConvergenceRegression :
  (problem : P.BishopPolynomialGeometricCompartment) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf
      (P.compartmentMajorantTerm problem))
majorantConvergenceRegression =
  P.compartmentMajorantConvergent
