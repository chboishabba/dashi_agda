module DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as EF

------------------------------------------------------------------------
-- LITERAL TARGET-CENTRED EXPLICIT-FORMULA BRIDGE
--
-- Existing RiemannExplicitFormula gives, for an admissible test f,
--
--   arithmeticForm f = spectralZeroForm f
--
-- with prime/Gamma/pole/trivial-zero decomposition on the arithmetic side.
--
-- What RH currently needs is not that generic theorem in the abstract.  It is
-- a test f_{t,J} whose spectral side decomposes EXACTLY as
--
--   target/same-ordinate cluster + finite pole-near signed response
--   + explicit far zero remainder,
--
-- with the finite near term preserving the literal g_pole,
-- multiplicities, and target-relative phase b_sigma-t.
------------------------------------------------------------------------

record PoleNearTargetWindow
    (space : Weil.WeilTestSpace)
    (formula : EF.RiemannExplicitFormula space) : Set₁ where
  open Weil.WeilTestSpace space
  open EF.RiemannExplicitFormula formula
  constructor pole-near-target-window
  field
    targetWindowTest : Test
    targetWindowAdmissible : admissible targetWindowTest

    sameOrdinateCluster : Scalar
    finitePoleNearSigned : Scalar
    farZeroRemainder : Scalar

    spectralWindowDecomposition :
      spectralZeroForm targetWindowTest
      ≡
      (sameOrdinateCluster +S
       (finitePoleNearSigned +S farZeroRemainder))

    poleTaperPreserved : Set
    targetRelativePhasePreserved : Set
    multiplicitiesPreserved : Set
    nearOffFinsetPreserved : Set

    bridgeReference : String

open PoleNearTargetWindow public

------------------------------------------------------------------------
-- Forward compiler: once the literal spectral identification exists, the
-- existing generic explicit formula immediately transports arithmetic data to
-- the exact cluster+near+far zero decomposition.
------------------------------------------------------------------------

arithmeticEqualsPoleNearWindow :
  (space : Weil.WeilTestSpace) →
  (formula : EF.RiemannExplicitFormula space) →
  (w : PoleNearTargetWindow space formula) →
  EF.RiemannExplicitFormula.arithmeticForm formula (targetWindowTest w)
  ≡
  Weil.WeilTestSpace._+S_ space
    (sameOrdinateCluster w)
    (Weil.WeilTestSpace._+S_ space
      (finitePoleNearSigned w)
      (farZeroRemainder w))
arithmeticEqualsPoleNearWindow space formula w =
  Weil.≡-trans
    (EF.RiemannExplicitFormula.explicitFormula formula
      (targetWindowTest w)
      (targetWindowAdmissible w))
    (spectralWindowDecomposition w)

------------------------------------------------------------------------
-- Arithmetic side remains decomposed into the canonical four channels.
------------------------------------------------------------------------

arithmeticChannelDecompositionAtPoleNearWindow :
  (space : Weil.WeilTestSpace) →
  (formula : EF.RiemannExplicitFormula space) →
  (w : PoleNearTargetWindow space formula) →
  EF.RiemannExplicitFormula.arithmeticForm formula (targetWindowTest w)
  ≡
  Weil.WeilTestSpace._+S_ space
    (EF.RiemannExplicitFormula.primePowerTerm formula (targetWindowTest w))
    (Weil.WeilTestSpace._+S_ space
      (EF.RiemannExplicitFormula.archimedeanGammaTerm formula (targetWindowTest w))
      (Weil.WeilTestSpace._+S_ space
        (EF.RiemannExplicitFormula.poleTerm formula (targetWindowTest w))
        (EF.RiemannExplicitFormula.trivialZeroTerm formula (targetWindowTest w))))
arithmeticChannelDecompositionAtPoleNearWindow space formula w =
  EF.RiemannExplicitFormula.arithmeticDecomposition formula
    (targetWindowTest w)
    (targetWindowAdmissible w)

------------------------------------------------------------------------
-- To turn the transported identity into an EVALUATION of the finite near term
-- one still needs a lawful extraction/cancellation operation.  It is typed
-- explicitly so generic equality is not mistaken for an isolated near value.
------------------------------------------------------------------------

record PoleNearExtraction
    (space : Weil.WeilTestSpace)
    (formula : EF.RiemannExplicitFormula space)
    (w : PoleNearTargetWindow space formula) : Set₁ where
  open Weil.WeilTestSpace space
  open EF.RiemannExplicitFormula formula
  constructor pole-near-extraction
  field
    extractedNear : Scalar
    extract : Scalar → Scalar → Scalar → Scalar

    extractionFromSpectralWindow :
      extract
        (spectralZeroForm (targetWindowTest w))
        (sameOrdinateCluster w)
        (farZeroRemainder w)
      ≡ finitePoleNearSigned w

    extractionFromArithmeticWindow :
      extract
        (arithmeticForm (targetWindowTest w))
        (sameOrdinateCluster w)
        (farZeroRemainder w)
      ≡ extractedNear

    extractionReference : String

open PoleNearExtraction public

explicitFormulaExtractsSameFiniteNear :
  (space : Weil.WeilTestSpace) →
  (formula : EF.RiemannExplicitFormula space) →
  (w : PoleNearTargetWindow space formula) →
  (x : PoleNearExtraction space formula w) →
  extractedNear x ≡ finitePoleNearSigned w
explicitFormulaExtractsSameFiniteNear space formula w x =
  Weil.≡-trans
    (Weil.≡-sym (extractionFromArithmeticWindow x))
    (Weil.≡-trans
      (congExtract
        (EF.RiemannExplicitFormula.explicitFormula formula
          (targetWindowTest w)
          (targetWindowAdmissible w)))
      (extractionFromSpectralWindow x))
  where
  congExtract :
    {a b : Weil.WeilTestSpace.Scalar space} →
    a ≡ b →
    PoleNearExtraction.extract x a (sameOrdinateCluster w) (farZeroRemainder w)
      ≡
    PoleNearExtraction.extract x b (sameOrdinateCluster w) (farZeroRemainder w)
  congExtract refl = refl

record PoleNearExplicitFormulaBoundary : Set where
  constructor pole-near-explicit-formula-boundary
  field
    genericExplicitFormulaOwned : Bool
    genericExplicitFormulaOwnedIsTrue : genericExplicitFormulaOwned ≡ true

    genericFormulaAlreadyIdentifiesPoleNearWindow : Bool
    genericFormulaAlreadyIdentifiesPoleNearWindowIsFalse :
      genericFormulaAlreadyIdentifiesPoleNearWindow ≡ false

    literalTargetWindowBridgeRequired : Bool
    literalTargetWindowBridgeRequiredIsTrue : literalTargetWindowBridgeRequired ≡ true

    lawfulNearExtractionRequired : Bool
    lawfulNearExtractionRequiredIsTrue : lawfulNearExtractionRequired ≡ true

    explicitFormulaRouteClosed : Bool
    explicitFormulaRouteClosedIsFalse : explicitFormulaRouteClosed ≡ false

    nextTheorem : String

canonicalPoleNearExplicitFormulaBoundary : PoleNearExplicitFormulaBoundary
canonicalPoleNearExplicitFormulaBoundary =
  pole-near-explicit-formula-boundary
    true refl
    false refl
    true refl
    true refl
    false refl
    "Construct an admissible target-window test f_{t,J} in the canonical WeilTestSpace whose spectralZeroForm is exactly same-ordinate cluster + literal finite reflection-paired pole-near sum + explicit far remainder, preserving g_pole, multiplicity, nearOffFinset and b_sigma-t; then supply the exact additive extraction/cancellation needed to isolate the near term on the arithmetic side."
