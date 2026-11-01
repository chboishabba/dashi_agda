module DASHI.Moonshine.JInvariantComplexModulusMultiplicationCompilerValidation where

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Moonshine.JInvariantQPowerModulusExact as QPower
import DASHI.Moonshine.JInvariantComplexModulusMultiplicationCompilerExact as Compiler

compilerProducesExistingQPowerAuthority :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D} →
  Compiler.ComplexNormSquareCompositionLaws C →
  Compiler.NonnegativeSquareRootMultiplicationLaws
    (Real.real (Complex.realPackage C)) D →
  QPower.ComplexModulusMultiplicationLaws C D F
compilerProducesExistingQPowerAuthority =
  Compiler.compileComplexModulusMultiplicationLaws
