module DASHI.Physics.Closure.NSTriadKNCanonicalLiteralProjectedODERound407Exact where

------------------------------------------------------------------------
-- ROUND407 / CONSTRUCT THE R240 EQUATION WITH THE LITERAL ROUND30 RHS
--
-- `Audit.ExactProjectedGalerkinEquation` is structurally weaker than its name:
-- only `projectedODE` is proof-bearing, while `viscousTermMeaning` is merely a
-- Set-valued metadata slot.  Therefore an arbitrary inhabitant of that record
-- does not identify its `timeDerivative` with Round30's literal NS coefficient.
--
-- On the rational physical carrier we can simply construct the correct equation.
-- Set
--
--   u_t(k) = -nu |k|^2 u(k) + N_k(u)
--
-- to the actual Round30 coefficient and set the equation's viscous term to
-- +nu |k|^2 u(k).  Exact finite rational algebra proves
--
--   u_t + nu |k|^2 u = N_k(u).
--
-- Thus the canonical equation has `timeDerivative = literal coefficient`
-- definitionally.  No PDE estimate or analytic theorem is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
open import Data.Rational.Base using (ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as R30

F : C3.RealField _
F = Rational.rationalRealField

positiveViscousCoefficient :
  R30.PhysicalFiniteComplex3GalerkinSystem F →
  Z3.FourierMode → C3.Complex3 F
positiveViscousCoefficient physicalSystem mode =
  C3.complex3Scale
    (C3.realEmbed F
      (R30.viscosity physicalSystem
        * C3.normSquared (R30.physicalInverseSquare physicalSystem) mode))
    (Audit.velocityAt (R30.finiteSystem physicalSystem) mode)

literalCoefficientPlusPositiveViscosityIsNonlinearity :
  (physicalSystem : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (mode : Z3.FourierMode) →
  C3.complex3Add
    (R30.literalViscousQuadraticCoefficient physicalSystem mode)
    (positiveViscousCoefficient physicalSystem mode)
  ≡ Audit.projectedNonlinearity (R30.finiteSystem physicalSystem) mode
literalCoefficientPlusPositiveViscosityIsNonlinearity physicalSystem mode
  with Audit.velocityAt (R30.finiteSystem physicalSystem) mode
     | Audit.projectedNonlinearity (R30.finiteSystem physicalSystem) mode
... | C3.complex3
      (C3.complex ux ui) (C3.complex uy uyi) (C3.complex uz uzi)
    | C3.complex3
      (C3.complex nx ni) (C3.complex ny nyi) (C3.complex nz nzi) =
  let
    nu = R30.viscosity physicalSystem
    k2 = C3.normSquared (R30.physicalInverseSquare physicalSystem) mode
  in
  Field.complex3Ext
    (Field.complexExt
      (solve (nu ∷ k2 ∷ ux ∷ nx ∷ []))
      (solve (nu ∷ k2 ∷ ui ∷ ni ∷ [])))
    (Field.complexExt
      (solve (nu ∷ k2 ∷ uy ∷ ny ∷ []))
      (solve (nu ∷ k2 ∷ uyi ∷ nyi ∷ [])))
    (Field.complexExt
      (solve (nu ∷ k2 ∷ uz ∷ nz ∷ []))
      (solve (nu ∷ k2 ∷ uzi ∷ nzi ∷ [])))

canonicalLiteralProjectedEquation :
  (physicalSystem : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  Audit.ExactProjectedGalerkinEquation (R30.finiteSystem physicalSystem)
canonicalLiteralProjectedEquation physicalSystem = record
  { Audit.timeDerivative = R30.literalViscousQuadraticCoefficient physicalSystem
  ; Audit.viscousTerm = positiveViscousCoefficient physicalSystem
  ; Audit.projectedODE = λ mode listed →
      literalCoefficientPlusPositiveViscosityIsNonlinearity physicalSystem mode
  ; Audit.viscousTermMeaning =
      ∀ mode →
      positiveViscousCoefficient physicalSystem mode
      ≡ positiveViscousCoefficient physicalSystem mode
  ; Audit.divergenceFreePreserved = Set
  ; Audit.realityConditionPreserved = Set
  ; Audit.physicalSpaceProjectedEquation = Set
  ; Audit.finiteFourierTransform = Set
  ; Audit.FourierTransformInjectiveOnCutoff = Set
  ; Audit.FourierTransformOfPhysicalEquationEqualsProjectedODE = Set
  ; Audit.projectedODEImpliesPhysicalEquationOnCutoff = Set
  }

canonicalTimeDerivativeIsLiteralCoefficient :
  (physicalSystem : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (mode : Z3.FourierMode) →
  Audit.timeDerivative (canonicalLiteralProjectedEquation physicalSystem) mode
  ≡ R30.literalViscousQuadraticCoefficient physicalSystem mode
canonicalTimeDerivativeIsLiteralCoefficient physicalSystem mode = refl

round407ArbitraryAuditEquationIdentifiesLiteralDerivative : Bool
round407ArbitraryAuditEquationIdentifiesLiteralDerivative = false

round407CanonicalEquationUsesLiteralRound30Derivative : Bool
round407CanonicalEquationUsesLiteralRound30Derivative = true

round407ProjectedODEClosedByFiniteRationalAlgebra : Bool
round407ProjectedODEClosedByFiniteRationalAlgebra = true
