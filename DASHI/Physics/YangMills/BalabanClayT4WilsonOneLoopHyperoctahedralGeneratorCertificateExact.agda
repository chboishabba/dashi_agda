module DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopHyperoctahedralGeneratorCertificateExact where

------------------------------------------------------------------------
-- PRIMARY / METHOD SOURCES
--
-- Stefano Capitani,
-- "Lattice Perturbation Theory", Physics Reports 382 (2003), 113--302.
-- DOI: 10.1016/S0370-1573(03)00211-4.  arXiv: hep-lat/0211036.
--
-- Martin Luescher and Peter Weisz,
-- "Coordinate space methods for the evaluation of Feynman diagrams in
-- lattice field theories", Nuclear Physics B 445 (1995), 429--450.
-- DOI: 10.1016/0550-3213(95)00185-U.  arXiv: hep-lat/9502017.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Balaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- SOURCE RELATIONSHIP / GUARDRAIL
--
-- Capitani surveys hypercubic lattice perturbation theory and the practical
-- evaluation of lattice integrals.  Luescher--Weisz is a coordinate-SPACE
-- recursion method for lattice Feynman integrals.  The finite 4^4 BOX-orbit
-- quotient proved in DASHI is not identified with that coordinate-space
-- recursion merely because both exploit lattice structure.  This module uses
-- only the standard hypercubic signed-permutation symmetry and makes the
-- finite generator obligation explicit.
--
-- DASHI CONTRIBUTION
--
-- Replace the source-facing statement "the regular integrand is invariant
-- under B4" by exactly seven syntax equalities: four coordinate sign flips
-- and three adjacent transpositions.  These are the generators already acting
-- on the actual DiagramExpression syntax and generated Brillouin cells.
-- Every finite generator word then fixes the expression by induction.
--
-- For external momentum held on axis 0, a separate six-generator certificate
-- uses the four sign flips and the two transverse adjacent swaps.  Thus the
-- physical source leaf is finite and auditable: seven equalities for the
-- 240->4 route, or six equalities for the conservative 240->7 route.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4HyperoctahedralGridOrbitExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopJointMomentumEquivarianceExact as Joint

------------------------------------------------------------------------
-- Full B4: exactly seven nonidentity generators.
------------------------------------------------------------------------

record SevenGeneratorInvariantExpression
    (expression : Eval.DiagramExpression) : Set where
  field
    flip0Exact : Joint.transformExpression Orbit.flip0 expression ≡ expression
    flip1Exact : Joint.transformExpression Orbit.flip1 expression ≡ expression
    flip2Exact : Joint.transformExpression Orbit.flip2 expression ≡ expression
    flip3Exact : Joint.transformExpression Orbit.flip3 expression ≡ expression
    swap01Exact : Joint.transformExpression Orbit.swap01 expression ≡ expression
    swap12Exact : Joint.transformExpression Orbit.swap12 expression ≡ expression
    swap23Exact : Joint.transformExpression Orbit.swap23 expression ≡ expression
open SevenGeneratorInvariantExpression public

asJointMomentumInvariant : ∀ {expression} →
  SevenGeneratorInvariantExpression expression →
  Joint.JointMomentumInvariantExpression expression
asJointMomentumInvariant certificate = record
  { invariantGenerator = λ
      { Orbit.identity → refl
      ; Orbit.flip0 → flip0Exact certificate
      ; Orbit.flip1 → flip1Exact certificate
      ; Orbit.flip2 → flip2Exact certificate
      ; Orbit.flip3 → flip3Exact certificate
      ; Orbit.swap01 → swap01Exact certificate
      ; Orbit.swap12 → swap12Exact certificate
      ; Orbit.swap23 → swap23Exact certificate
      }
  }

applyGeneratorWord :
  List Orbit.HyperoctahedralGenerator →
  Eval.DiagramExpression → Eval.DiagramExpression
applyGeneratorWord [] expression = expression
applyGeneratorWord (generator ∷ generators) expression =
  applyGeneratorWord generators (Joint.transformExpression generator expression)

sevenGeneratorsFixEveryWord : ∀ {expression} →
  (certificate : SevenGeneratorInvariantExpression expression) →
  (generators : List Orbit.HyperoctahedralGenerator) →
  applyGeneratorWord generators expression ≡ expression
sevenGeneratorsFixEveryWord certificate [] = refl
sevenGeneratorsFixEveryWord certificate (generator ∷ generators)
  rewrite Joint.invariantGenerator (asJointMomentumInvariant certificate) generator =
  sevenGeneratorsFixEveryWord certificate generators

------------------------------------------------------------------------
-- Fixed external axis: exactly six nonidentity stabilizer generators.
------------------------------------------------------------------------

data Axis0StabilizerGenerator : Set where
  fixedFlip0 fixedFlip1 fixedFlip2 fixedFlip3 fixedSwap12 fixedSwap23 :
    Axis0StabilizerGenerator

asHyperoctahedralGenerator :
  Axis0StabilizerGenerator → Orbit.HyperoctahedralGenerator
asHyperoctahedralGenerator fixedFlip0 = Orbit.flip0
asHyperoctahedralGenerator fixedFlip1 = Orbit.flip1
asHyperoctahedralGenerator fixedFlip2 = Orbit.flip2
asHyperoctahedralGenerator fixedFlip3 = Orbit.flip3
asHyperoctahedralGenerator fixedSwap12 = Orbit.swap12
asHyperoctahedralGenerator fixedSwap23 = Orbit.swap23

record SixGeneratorFixedAxisInvariantExpression
    (expression : Eval.DiagramExpression) : Set where
  field
    fixedFlip0Exact : Joint.transformExpression Orbit.flip0 expression ≡ expression
    fixedFlip1Exact : Joint.transformExpression Orbit.flip1 expression ≡ expression
    fixedFlip2Exact : Joint.transformExpression Orbit.flip2 expression ≡ expression
    fixedFlip3Exact : Joint.transformExpression Orbit.flip3 expression ≡ expression
    fixedSwap12Exact : Joint.transformExpression Orbit.swap12 expression ≡ expression
    fixedSwap23Exact : Joint.transformExpression Orbit.swap23 expression ≡ expression
open SixGeneratorFixedAxisInvariantExpression public

asFixedAxisInvariant : ∀ {expression} →
  SixGeneratorFixedAxisInvariantExpression expression →
  Joint.FixedAxisInvariantExpression expression
asFixedAxisInvariant certificate = record
  { transverseSwap12 = fixedSwap12Exact certificate
  ; transverseSwap23 = fixedSwap23Exact certificate
  ; sign0 = fixedFlip0Exact certificate
  ; sign1 = fixedFlip1Exact certificate
  ; sign2 = fixedFlip2Exact certificate
  ; sign3 = fixedFlip3Exact certificate
  }

applyAxis0StabilizerWord :
  List Axis0StabilizerGenerator →
  Eval.DiagramExpression → Eval.DiagramExpression
applyAxis0StabilizerWord [] expression = expression
applyAxis0StabilizerWord (generator ∷ generators) expression =
  applyAxis0StabilizerWord generators
    (Joint.transformExpression (asHyperoctahedralGenerator generator) expression)

fixedAxisGeneratorExact : ∀ {expression} →
  SixGeneratorFixedAxisInvariantExpression expression →
  (generator : Axis0StabilizerGenerator) →
  Joint.transformExpression (asHyperoctahedralGenerator generator) expression ≡ expression
fixedAxisGeneratorExact certificate fixedFlip0 = fixedFlip0Exact certificate
fixedAxisGeneratorExact certificate fixedFlip1 = fixedFlip1Exact certificate
fixedAxisGeneratorExact certificate fixedFlip2 = fixedFlip2Exact certificate
fixedAxisGeneratorExact certificate fixedFlip3 = fixedFlip3Exact certificate
fixedAxisGeneratorExact certificate fixedSwap12 = fixedSwap12Exact certificate
fixedAxisGeneratorExact certificate fixedSwap23 = fixedSwap23Exact certificate

sixFixedAxisGeneratorsFixEveryWord : ∀ {expression} →
  (certificate : SixGeneratorFixedAxisInvariantExpression expression) →
  (generators : List Axis0StabilizerGenerator) →
  applyAxis0StabilizerWord generators expression ≡ expression
sixFixedAxisGeneratorsFixEveryWord certificate [] = refl
sixFixedAxisGeneratorsFixEveryWord certificate (generator ∷ generators)
  rewrite fixedAxisGeneratorExact certificate generator =
  sixFixedAxisGeneratorsFixEveryWord certificate generators

------------------------------------------------------------------------
-- Literal source-facing certificates.  These carry the ACTUAL regularIntegrand
-- object; no parallel symbolic surrogate is introduced.
------------------------------------------------------------------------

record LiteralRegularIntegrandB4GeneratorCertificate
    {expressions : Eval.LiteralDiagramExpressions}
    {ward : Eval.LiteralWardExpressionProofs expressions}
    (scalarData : Eval.LiteralScalarIntegrandExpression expressions ward) : Set where
  field
    sevenGeneratorExact :
      SevenGeneratorInvariantExpression (Eval.regularIntegrand scalarData)
open LiteralRegularIntegrandB4GeneratorCertificate public

literalRegularIntegrandB4Invariant :
  ∀ {expressions ward scalarData} →
  LiteralRegularIntegrandB4GeneratorCertificate
    {expressions = expressions} {ward = ward} scalarData →
  Joint.JointMomentumInvariantExpression (Eval.regularIntegrand scalarData)
literalRegularIntegrandB4Invariant certificate =
  asJointMomentumInvariant (sevenGeneratorExact certificate)

record LiteralRegularIntegrandFixedAxisGeneratorCertificate
    {expressions : Eval.LiteralDiagramExpressions}
    {ward : Eval.LiteralWardExpressionProofs expressions}
    (scalarData : Eval.LiteralScalarIntegrandExpression expressions ward) : Set where
  field
    sixGeneratorExact :
      SixGeneratorFixedAxisInvariantExpression (Eval.regularIntegrand scalarData)
open LiteralRegularIntegrandFixedAxisGeneratorCertificate public

literalRegularIntegrandFixedAxisInvariant :
  ∀ {expressions ward scalarData} →
  LiteralRegularIntegrandFixedAxisGeneratorCertificate
    {expressions = expressions} {ward = ward} scalarData →
  Joint.FixedAxisInvariantExpression (Eval.regularIntegrand scalarData)
literalRegularIntegrandFixedAxisInvariant certificate =
  asFixedAxisInvariant (sixGeneratorExact certificate)

sevenGeneratorReductionLevel : ProofLevel
sevenGeneratorReductionLevel = machineChecked

finiteGeneratorWordClosureLevel : ProofLevel
finiteGeneratorWordClosureLevel = machineChecked

sixGeneratorFixedAxisReductionLevel : ProofLevel
sixGeneratorFixedAxisReductionLevel = machineChecked

-- Still source-specific: construct one of the two literal certificates from
-- the explicit Wilson/ghost/Haar regular-integrand syntax tree.  The former
-- unbounded-looking equivariance leaf is now reduced to 7 or 6 equations.
literalRegularIntegrandFiniteGeneratorCertificateLevel : ProofLevel
literalRegularIntegrandFiniteGeneratorCertificateLevel = conditional
