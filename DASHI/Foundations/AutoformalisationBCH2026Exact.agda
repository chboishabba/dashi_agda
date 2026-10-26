module DASHI.Foundations.AutoformalisationBCH2026Exact where

-- Alexander Bastounis, Fabian Circelli, Anders C. Hansen (2026-10-06),
-- "Navier-Stokes lost in translation", arXiv:2610.08144v1,
-- Examples 2.1, 2.2, 3.1, 3.3 and 4.3.
-- Original text/evidence are owned by those authors; these finite
-- information-loss witnesses are DASHI reconstructions.
-- Existing generic proof owner is IntersectionalNonFactorability.
-- Neither full semantic faithfulness nor SCI=infinity is proved here.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.InterpretiveFormalisationCoreExact as Interpretation

-- A checked theorem conclusion cannot identify which proof route
-- was used (Examples 2.1 and 2.2).
data ProofRoute : Set where
  originalFactorisation : ProofRoute
  correctedFactorisation : ProofRoute

data Conclusion : Set where
  polynomialNonnegative : Conclusion

conclusionOnly : ProofRoute → Conclusion
conclusionOnly originalFactorisation = polynomialNonnegative
conclusionOnly correctedFactorisation = polynomialNonnegative

routeIsOriginal : ProofRoute → ProofRoute
routeIsOriginal originalFactorisation = originalFactorisation
routeIsOriginal correctedFactorisation = correctedFactorisation

distinctRoutes :
  originalFactorisation ≡ correctedFactorisation → ⊥
distinctRoutes ()

proofRouteCollision :
  NF.NonFactorabilityWitness conclusionOnly routeIsOriginal
proofRouteCollision =
  NF.nonFactorabilityWitness
    originalFactorisation correctedFactorisation refl distinctRoutes

conclusionDoesNotDetermineProofRoute :
  NF.FactorsThrough conclusionOnly routeIsOriginal → ⊥
conclusionDoesNotDetermineProofRoute =
  NF.witnessRulesOutEveryFlatFactorisation proofRouteCollision

-- Example 2.2 also distinguishes the diagonalisation route from a
-- direct entrywise sum-of-squares route for symmetric matrix traces.
-- The actual general entrywise algebra appears in companion Lean.
data MatrixArgument : Set where
  NLorthogonalDiagonalisation : MatrixArgument
  LeanDirectEntries : MatrixArgument

data MatrixConclusion : Set where
  symmetricTraceSquareNonnegative : MatrixConclusion

recordMatrixConclusion : MatrixArgument → MatrixConclusion
recordMatrixConclusion NLorthogonalDiagonalisation =
  symmetricTraceSquareNonnegative
recordMatrixConclusion LeanDirectEntries =
  symmetricTraceSquareNonnegative

matrixArgumentIdentity : MatrixArgument → MatrixArgument
matrixArgumentIdentity argument = argument

distinctMatrixArguments :
  NLorthogonalDiagonalisation ≡ LeanDirectEntries → ⊥
distinctMatrixArguments ()

matrixArgumentCollision :
  NF.NonFactorabilityWitness
    recordMatrixConclusion matrixArgumentIdentity
matrixArgumentCollision =
  NF.nonFactorabilityWitness
    NLorthogonalDiagonalisation LeanDirectEntries
    refl distinctMatrixArguments

correctTraceStatementDoesNotDetermineMethod :
  NF.FactorsThrough
    recordMatrixConclusion matrixArgumentIdentity → ⊥
correctTraceStatementDoesNotDetermineMethod =
  NF.witnessRulesOutEveryFlatFactorisation
    matrixArgumentCollision

-- Example 3.1: NL Lemma 8.6 has m+4 torus derivatives;
-- cited Lean at f9e8bc5 requires m+5 coordinate jets.
data InverseCase : Set where
  nl819 : InverseCase
  leanAtF9e8bc5 : InverseCase

data InverseLabel : Set where
  inverseEstimate : InverseLabel

data DerivativeDebt : Set where
  plusFourTorus : DerivativeDebt
  plusFiveJets : DerivativeDebt

eraseInverse : InverseCase → InverseLabel
eraseInverse nl819 = inverseEstimate
eraseInverse leanAtF9e8bc5 = inverseEstimate

sourceDerivativeDebt : InverseCase → DerivativeDebt
sourceDerivativeDebt nl819 = plusFourTorus
sourceDerivativeDebt leanAtF9e8bc5 = plusFiveJets

distinctDerivativeDebt : plusFourTorus ≡ plusFiveJets → ⊥
distinctDerivativeDebt ()

derivativeDebtWitness :
  NF.NonFactorabilityWitness eraseInverse sourceDerivativeDebt
derivativeDebtWitness =
  NF.nonFactorabilityWitness
    nl819 leanAtF9e8bc5 refl distinctDerivativeDebt

inverseLabelCannotCertifyDerivativeBudget :
  NF.FactorsThrough eraseInverse sourceDerivativeDebt → ⊥
inverseLabelCannotCertifyDerivativeBudget =
  NF.witnessRulesOutEveryFlatFactorisation derivativeDebtWitness

-- Example 3.3: NL equation (10.19) B_R-only versus historical
-- Lean bound with additional A_R input; dependency, not mere naming.
data FluxCase : Set where
  nl1019 : FluxCase
  leanPressureFlux : FluxCase

data FluxLabel : Set where
  pressureFluxBound : FluxLabel

data FluxDependency : Set where
  onlyBR : FluxDependency
  alsoAR : FluxDependency

eraseFlux : FluxCase → FluxLabel
eraseFlux nl1019 = pressureFluxBound
eraseFlux leanPressureFlux = pressureFluxBound

actualFluxDependency : FluxCase → FluxDependency
actualFluxDependency nl1019 = onlyBR
actualFluxDependency leanPressureFlux = alsoAR

distinctFluxDependency : onlyBR ≡ alsoAR → ⊥
distinctFluxDependency ()

fluxWitness : NF.NonFactorabilityWitness eraseFlux actualFluxDependency
fluxWitness =
  NF.nonFactorabilityWitness
    nl1019 leanPressureFlux refl distinctFluxDependency

fluxLabelCannotDiscardGradientTerm :
  NF.FactorsThrough eraseFlux actualFluxDependency → ⊥
fluxLabelCannotDiscardGradientTerm =
  NF.witnessRulesOutEveryFlatFactorisation fluxWitness

-- Example 4.1: a proved square identity cannot tell whether
-- the source's intended least natural number exists.
data MinimumCase : Set where
  minimumExists : MinimumCase
  emptySetDefaulted : MinimumCase

data AlgebraicLabel : Set where
  squareIdentity : AlgebraicLabel

data SourceDenotation : Set where
  defined : SourceDenotation
  undefined : SourceDenotation

eraseExistence : MinimumCase → AlgebraicLabel
eraseExistence minimumExists = squareIdentity
eraseExistence emptySetDefaulted = squareIdentity

denotation : MinimumCase → SourceDenotation
denotation minimumExists = defined
denotation emptySetDefaulted = undefined

distinctDenotation : defined ≡ undefined → ⊥
distinctDenotation ()

minimumWitness : NF.NonFactorabilityWitness eraseExistence denotation
minimumWitness =
  NF.nonFactorabilityWitness
    minimumExists emptySetDefaulted refl distinctDenotation

identityCannotCertifyDenotation :
  NF.FactorsThrough eraseExistence denotation → ⊥
identityCannotCertifyDenotation =
  NF.witnessRulesOutEveryFlatFactorisation minimumWitness

record StatementCorrespondence (Source Formal : Set) : Set where
  field
    formalImpliesSource : Formal → Source
    sourceImpliesFormal : Source → Formal

interpretiveGuard : Interpretation.InterpretiveFormalisationBoundary
interpretiveGuard =
  Interpretation.canonicalInterpretiveFormalisationBoundary
