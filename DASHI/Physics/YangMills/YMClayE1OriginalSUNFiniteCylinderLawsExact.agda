module DASHI.Physics.YangMills.YMClayE1OriginalSUNFiniteCylinderLawsExact where

------------------------------------------------------------------------
-- E1: finite normalized state laws of the ACTUAL variable-size SU(N)
-- Wilson/Haar family, reusing the existing normalized physical numerator
-- algebra AT EACH distinct cutoff carrier.
--
-- The only finite-source inputs below are actual integration laws and
-- original partition nonvanishing. There are NO independent finite
-- normalization/linearity/positivity assumptions.
--
-- This is finite mathematics. It does not assert a physical continuum
-- limit, clustering, spectral gap, noncollapse, or all compact simple G.
-- The real arithmetic is the repository's explicit non-safe axiom socket.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _≤ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayE1OriginalSUNDependentCylinderExact as Native
import DASHI.Physics.YangMills.YMClayE1VariableCutoffCylinderLimitExact as E1
import DASHI.Physics.YangMills.YMClayOriginalVariableWilsonCovarianceSourceExact as OriginalWilson
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws) quotient)
  where

  nativeMeasure :
    (n : Nat) →
    Physical.PhysicalFiniteYMMeasure
      (Native.ActualLinks theory traceData exponential beta oneLink
        bilateral (Quotient.divide quotient) n) ℝ
  nativeMeasure = Native.actualOriginalWilsonMeasureAt
    theory traceData exponential beta oneLink bilateral
    (Quotient.divide quotient)

  nativeExpectation :
    (n : Nat) →
    Native.Cylinder theory traceData exponential beta oneLink
      bilateral (Quotient.divide quotient) → ℝ
  nativeExpectation = Native.actualOriginalWilsonCylinderExpectation
    theory traceData exponential beta oneLink bilateral
    (Quotient.divide quotient)

  record ActualNativeFiniteIntegration : Set₁ where
    field
      integrals : ∀ n →
        Finite.PhysicalFiniteMeasureIntegrationLaws
          (nativeMeasure n)

      nonzero : ∀ n →
        Quotient.Nonzero quotient
          (Physical.partitionFunction (nativeMeasure n))

  open ActualNativeFiniteIntegration public

  -- Existing finite-cylinder normalized laws apply at any ONE n by
  -- making an irrelevant constant family at that fixed link carrier.
  -- The actual source across n is STILL the varying nativeMeasure.
  fixedCutoffFiniteLaws :
    ActualNativeFiniteIntegration →
    (n : Nat) →
    Limit.FinitePhysicalNormalizedFamily
      (Native.ActualLinks theory traceData exponential beta
        oneLink bilateral (Quotient.divide quotient) n)
      limitLaws quotient division
  fixedCutoffFiniteLaws source n = record
    { Limit.FinitePhysicalNormalizedFamily.finiteMeasure =
        λ _ → nativeMeasure n
    ; Limit.FinitePhysicalNormalizedFamily.integrationLaws =
        λ _ → integrals source n
    ; Limit.FinitePhysicalNormalizedFamily.partitionNonzero =
        λ _ → nonzero source n
    }

  -- Notice: finiteExpectation (fixedCutoffFiniteLaws source n) zero
  -- is definitionally the true original Wilson normalized expectation
  -- at cutoff n, because the quotient/divide are the same function.
  nativeExpectationZero :
    (source : ActualNativeFiniteIntegration) →
    ∀ n →
    nativeExpectation n
      (Native.zeroCylinder theory traceData exponential beta oneLink
        bilateral (Quotient.divide quotient))
    ≡ 0ℝ
  nativeExpectationZero source n =
    Limit.finiteExpectationZero (fixedCutoffFiniteLaws source n) zero

  nativeExpectationOne :
    (source : ActualNativeFiniteIntegration) →
    ∀ n →
    nativeExpectation n
      (Native.oneCylinder theory traceData exponential beta oneLink
        bilateral (Quotient.divide quotient))
    ≡ 1ℝ
  nativeExpectationOne source n =
    Limit.finiteExpectationOne (fixedCutoffFiniteLaws source n) zero

  nativeExpectationAdd :
    (source : ActualNativeFiniteIntegration) →
    ∀ n left right →
    nativeExpectation n
      (Native.addCylinder theory traceData exponential beta oneLink
        bilateral (Quotient.divide quotient) left right)
    ≡ nativeExpectation n left +ℝ nativeExpectation n right
  nativeExpectationAdd source n left right =
    Limit.finiteExpectationAdd (fixedCutoffFiniteLaws source n)
      zero (λ links → left n links) (λ links → right n links)

  nativeExpectationScale :
    (source : ActualNativeFiniteIntegration) →
    ∀ n scalar cylinder →
    nativeExpectation n
      (Native.scaleCylinder theory traceData exponential beta oneLink
        bilateral (Quotient.divide quotient) scalar cylinder)
    ≡ scalar *ℝ nativeExpectation n cylinder
  nativeExpectationScale source n scalar cylinder =
    Limit.finiteExpectationScale (fixedCutoffFiniteLaws source n)
      zero scalar (λ links → cylinder n links)

  nativeExpectationPositive :
    (source : ActualNativeFiniteIntegration) →
    ∀ n cylinder →
    (∀ links → 0ℝ ≤ℝ cylinder n links) →
    0ℝ ≤ℝ nativeExpectation n cylinder
  nativeExpectationPositive source n cylinder positive =
    Limit.finiteExpectationPositive (fixedCutoffFiniteLaws source n)
      zero (λ links → cylinder n links) positive

  ----------------------------------------------------------------------
  -- ONE ORIGINAL SOURCE: finite integration laws plus the genuinely
  -- source-selected convergence witness are the ONLY inputs. The
  -- generic E1 carrier's five finite-state laws are calculated above.
  --
  -- This does not manufacture convergence or claim ordinary limits
  -- from an arbitrary function Nat -> Real -> Real.
  ----------------------------------------------------------------------

  realSelectedScalarLaws : E1.SelectedScalarConvergence ℝ
  realSelectedScalarLaws = record
    { E1.SelectedScalarConvergence.zero = 0ℝ
    ; E1.SelectedScalarConvergence.one = 1ℝ
    ; E1.SelectedScalarConvergence.add = _+ℝ_
    ; E1.SelectedScalarConvergence.multiply = _*ℝ_
    ; E1.SelectedScalarConvergence.Nonnegative =
        λ value → 0ℝ ≤ℝ value
    ; E1.SelectedScalarConvergence.Converges =
        RealLimit.Converges sequenceLimit
    ; E1.SelectedScalarConvergence.convergenceUnique =
        λ sequence left right leftProof rightProof →
          trans (sym leftProof) rightProof
    ; E1.SelectedScalarConvergence.constantConverges =
        RealLimit.constantLimit limitLaws
    ; E1.SelectedScalarConvergence.addConverges =
        λ left right leftLimit rightLimit leftProof rightProof →
          trans
            (RealLimit.addLimit limitLaws left right)
            (RealLimit.cong₂ _+ℝ_ leftProof rightProof)
    ; E1.SelectedScalarConvergence.multiplyConstantConverges =
        λ scalar sequence target proof →
          trans
            (RealLimit.multiplyConstantLimit limitLaws scalar sequence)
            (cong (λ value → scalar *ℝ value) proof)
    ; E1.SelectedScalarConvergence.nonnegativeClosed =
        λ sequence target proof pointwise →
          subst (λ value → 0ℝ ≤ℝ value) proof
            (RealLimit.nonnegativeLimitClosed limitLaws sequence pointwise)
    ; E1.SelectedScalarConvergence.convergenceCongruent =
        λ first second target pointwise proof →
          trans
            (Seq.limitCongruent sequenceLimit first second pointwise)
            proof
    }


  ----------------------------------------------------------------------
  -- Genuine continuum observable selection: never quantify convergence
  -- over ALL arbitrary n-dependent sections! The latter includes
  -- alternating constants and need not converge.
  --
  -- This chosen algebra carries literal realizations and their
  -- pointwise finite algebra laws. No independent expectation is added.
  ----------------------------------------------------------------------

  record SelectedNativeCylinderAlgebra : Set₁ where
    field
      Observable : Set
      selectedSection : Observable →
        Native.Cylinder theory traceData exponential beta oneLink
          bilateral (Quotient.divide quotient)

      zeroObservable oneObservable : Observable
      addObservable : Observable → Observable → Observable
      scalarObservable : ℝ → Observable → Observable

      zeroMeaning :
        ∀ n links →
        selectedSection zeroObservable n links ≡ 0ℝ

      oneMeaning :
        ∀ n links →
        selectedSection oneObservable n links ≡ 1ℝ

      addMeaning :
        ∀ n left right links →
        selectedSection (addObservable left right) n links
        ≡ selectedSection left n links +ℝ selectedSection right n links

      scalarMeaning :
        ∀ n scalar observable links →
        selectedSection (scalarObservable scalar observable) n links
        ≡ scalar *ℝ selectedSection observable n links

      Nonnegative : Observable → Set
      nonnegativeMeaning :
        ∀ observable →
        Nonnegative observable →
        ∀ n links → 0ℝ ≤ℝ selectedSection observable n links

      -- This is the actual gauge action on each original n-dependent
      -- Wilson link carrier, not a new abstract gauge-invariance token.
      gaugeInvariantSelection :
        ∀ observable →
        OriginalWilson.OriginalGaugeInvariantSection
          theory traceData exponential beta oneLink bilateral
          (Quotient.divide quotient)
          (selectedSection observable)

  open SelectedNativeCylinderAlgebra public

  selectedRealization :
    (selection : SelectedNativeCylinderAlgebra) →
    E1.CylinderRealization
      (Native.ActualLinks theory traceData exponential beta oneLink
        bilateral (Quotient.divide quotient))
      (Observable selection) ℝ
  selectedRealization selection = record
    { E1.CylinderRealization.realization =
        λ n observable → selectedSection selection observable n
    ; E1.CylinderRealization.zeroObservable = zeroObservable selection
    ; E1.CylinderRealization.oneObservable = oneObservable selection
    ; E1.CylinderRealization.addObservable = addObservable selection
    ; E1.CylinderRealization.scalarObservable = scalarObservable selection
    }

  nativeExpectationExtensional :
    (n : Nat)
    (left right :
      Native.Cylinder theory traceData exponential beta oneLink
        bilateral (Quotient.divide quotient)) →
    (∀ links → left n links ≡ right n links) →
    nativeExpectation n left ≡ nativeExpectation n right
  nativeExpectationExtensional n left right same =
    OriginalWilson.originalWilsonExpectationExtensional
      theory traceData exponential beta oneLink bilateral
      (Quotient.divide quotient)
      n (left n) (right n) same

  nativeSelectedExpectationZero :
    (finite : ActualNativeFiniteIntegration)
    (selection : SelectedNativeCylinderAlgebra) →
    ∀ n →
    nativeExpectation n (selectedSection selection (zeroObservable selection))
      ≡ 0ℝ
  nativeSelectedExpectationZero finite selection n =
    trans
      (nativeExpectationExtensional n
        (selectedSection selection (zeroObservable selection))
        (Native.zeroCylinder theory traceData exponential beta oneLink
          bilateral (Quotient.divide quotient))
        (zeroMeaning selection n))
      (nativeExpectationZero finite n)

  nativeSelectedExpectationOne :
    (finite : ActualNativeFiniteIntegration)
    (selection : SelectedNativeCylinderAlgebra) →
    ∀ n →
    nativeExpectation n (selectedSection selection (oneObservable selection))
      ≡ 1ℝ
  nativeSelectedExpectationOne finite selection n =
    trans
      (nativeExpectationExtensional n
        (selectedSection selection (oneObservable selection))
        (Native.oneCylinder theory traceData exponential beta oneLink
          bilateral (Quotient.divide quotient))
        (oneMeaning selection n))
      (nativeExpectationOne finite n)

  nativeSelectedExpectationAdd :
    (finite : ActualNativeFiniteIntegration)
    (selection : SelectedNativeCylinderAlgebra) →
    ∀ n left right →
    nativeExpectation n
      (selectedSection selection (addObservable selection left right))
    ≡
    nativeExpectation n (selectedSection selection left)
      +ℝ nativeExpectation n (selectedSection selection right)
  nativeSelectedExpectationAdd finite selection n left right =
    trans
      (nativeExpectationExtensional n
        (selectedSection selection (addObservable selection left right))
        (λ cutoff links →
          selectedSection selection left cutoff links
            +ℝ selectedSection selection right cutoff links)
        (addMeaning selection n left right))
      (nativeExpectationAdd finite n
        (selectedSection selection left)
        (selectedSection selection right))

  nativeSelectedExpectationScale :
    (finite : ActualNativeFiniteIntegration)
    (selection : SelectedNativeCylinderAlgebra) →
    ∀ n scalar observable →
    nativeExpectation n
      (selectedSection selection
        (scalarObservable selection scalar observable))
    ≡
    scalar *ℝ nativeExpectation n
      (selectedSection selection observable)
  nativeSelectedExpectationScale finite selection n scalar observable =
    trans
      (nativeExpectationExtensional n
        (selectedSection selection
          (scalarObservable selection scalar observable))
        (λ cutoff links →
          scalar *ℝ selectedSection selection observable cutoff links)
        (scalarMeaning selection n scalar observable))
      (nativeExpectationScale finite n scalar
        (selectedSection selection observable))

  record ActualSelectedOriginalSUNConvergence
      (finite : ActualNativeFiniteIntegration)
      (selection : SelectedNativeCylinderAlgebra) : Set₁ where
    field
      continuumExpectation : Observable selection → ℝ

      originalWilsonCylinderConverges :
        ∀ observable →
        RealLimit.Converges sequenceLimit
          (λ n → nativeExpectation n
            (selectedSection selection observable))
          (continuumExpectation observable)

  open ActualSelectedOriginalSUNConvergence public

  -- A faithful, physically selectable original E1 source:
  -- actual native finite Wilson measures; derived finite scalar laws;
  -- proof-bearing gauge-invariant selected cylinder representation;
  -- one explicit selected physical convergence theorem.
  nativeSUNAsDependentE1Source :
    (finite : ActualNativeFiniteIntegration)
    (selection : SelectedNativeCylinderAlgebra)
    (selected : ActualSelectedOriginalSUNConvergence finite selection) →
    E1.ActualVariableCutoffCylinderFamily
      (Native.ActualLinks theory traceData exponential beta oneLink
        bilateral (Quotient.divide quotient))
      (λ n → Physical.PhysicalFiniteYMMeasure
        (Native.ActualLinks theory traceData exponential beta oneLink
          bilateral (Quotient.divide quotient) n) ℝ)
      (Observable selection)
      ℝ
      (selectedRealization selection)
      realSelectedScalarLaws
  nativeSUNAsDependentE1Source finite selection selected = record
    { E1.ActualVariableCutoffCylinderFamily.finitePhysicalMeasure =
        nativeMeasure
    ; E1.ActualVariableCutoffCylinderFamily.originalNormalizedExpectation =
        λ n → Physical.normalizedExpectation
    ; E1.ActualVariableCutoffCylinderFamily.finiteExpectation =
        λ n observable →
          nativeExpectation n (selectedSection selection observable)
    ; E1.ActualVariableCutoffCylinderFamily.finiteExpectationIsOriginalWilson =
        λ n observable → refl
    ; E1.ActualVariableCutoffCylinderFamily.finiteZero =
        nativeSelectedExpectationZero finite selection
    ; E1.ActualVariableCutoffCylinderFamily.finiteOne =
        nativeSelectedExpectationOne finite selection
    ; E1.ActualVariableCutoffCylinderFamily.finiteAdd =
        nativeSelectedExpectationAdd finite selection
    ; E1.ActualVariableCutoffCylinderFamily.finiteScale =
        nativeSelectedExpectationScale finite selection
    ; E1.ActualVariableCutoffCylinderFamily.PositiveCylinder =
        Nonnegative selection
    ; E1.ActualVariableCutoffCylinderFamily.finitePositive =
        λ n observable positive →
          nativeExpectationPositive finite n
            (selectedSection selection observable)
            (nonnegativeMeaning selection observable positive n)
    ; E1.ActualVariableCutoffCylinderFamily.continuumExpectation =
        continuumExpectation selected
    ; E1.ActualVariableCutoffCylinderFamily.originalWilsonConverges =
        originalWilsonCylinderConverges selected
    }

  ----------------------------------------------------------------------
  -- A CONCRETE NONEMPTY SELECTED ALGEBRA from the actual original
  -- gauge-invariant local plaquette trace at the canonical origin.
  -- No arbitrary new physical observable carrier: the syntax evaluates
  -- at EVERY n to the genuine original Wilson link configuration.
  --
  -- Warning: this plaquette is microscopic; a fixed physical-size
  -- local continuum observable and its UV renormalization remain E1.
  ----------------------------------------------------------------------

  data OriginWilsonPolynomial : Set where
    zeroP oneP plaquetteP : OriginWilsonPolynomial
    addP multiplyP :
      OriginWilsonPolynomial → OriginWilsonPolynomial →
      OriginWilsonPolynomial
    scaleP : ℝ → OriginWilsonPolynomial → OriginWilsonPolynomial

  evalOriginWilsonPolynomial :
    OriginWilsonPolynomial →
    Native.Cylinder theory traceData exponential beta oneLink
      bilateral (Quotient.divide quotient)
  evalOriginWilsonPolynomial zeroP =
    OriginalWilson.originalZeroCylinderSection
      theory traceData exponential beta oneLink bilateral
      (Quotient.divide quotient)
  evalOriginWilsonPolynomial oneP =
    OriginalWilson.originalUnitCylinderSection
      theory traceData exponential beta oneLink bilateral
      (Quotient.divide quotient)
  evalOriginWilsonPolynomial plaquetteP =
    OriginalWilson.originalLocalPlaquetteTraceSection
      theory traceData exponential beta oneLink bilateral
      (Quotient.divide quotient)
  evalOriginWilsonPolynomial (addP left right) n links =
    evalOriginWilsonPolynomial left n links
      +ℝ evalOriginWilsonPolynomial right n links
  evalOriginWilsonPolynomial (multiplyP left right) n links =
    evalOriginWilsonPolynomial left n links
      *ℝ evalOriginWilsonPolynomial right n links
  evalOriginWilsonPolynomial (scaleP scalar expr) n links =
    scalar *ℝ evalOriginWilsonPolynomial expr n links

  originPolynomialGaugeInvariant :
    (expr : OriginWilsonPolynomial) →
    OriginalWilson.OriginalGaugeInvariantSection
      theory traceData exponential beta oneLink bilateral
      (Quotient.divide quotient)
      (evalOriginWilsonPolynomial expr)
  originPolynomialGaugeInvariant zeroP =
    OriginalWilson.originalGaugeInvariantZeroCylinder
      theory traceData exponential beta oneLink bilateral
      (Quotient.divide quotient)
  originPolynomialGaugeInvariant oneP =
    OriginalWilson.originalGaugeInvariantUnitCylinder
      theory traceData exponential beta oneLink bilateral
      (Quotient.divide quotient)
  originPolynomialGaugeInvariant plaquetteP =
    OriginalWilson.originalLocalPlaquetteTraceIsGaugeInvariantSection
      theory traceData exponential beta oneLink bilateral
      (Quotient.divide quotient)
  originPolynomialGaugeInvariant (addP left right) =
    OriginalWilson.originalGaugeInvariantSectionAdd
      theory traceData exponential beta oneLink bilateral
      (Quotient.divide quotient)
      (evalOriginWilsonPolynomial left)
      (evalOriginWilsonPolynomial right)
      (originPolynomialGaugeInvariant left)
      (originPolynomialGaugeInvariant right)
  originPolynomialGaugeInvariant (multiplyP left right) =
    OriginalWilson.originalGaugeInvariantSectionProduct
      theory traceData exponential beta oneLink bilateral
      (Quotient.divide quotient)
      (evalOriginWilsonPolynomial left)
      (evalOriginWilsonPolynomial right)
      (originPolynomialGaugeInvariant left)
      (originPolynomialGaugeInvariant right)
  originPolynomialGaugeInvariant (scaleP scalar expr) =
    OriginalWilson.originalGaugeInvariantSectionScale
      theory traceData exponential beta oneLink bilateral
      (Quotient.divide quotient)
      scalar (evalOriginWilsonPolynomial expr)
      (originPolynomialGaugeInvariant expr)

  originWilsonPolynomialSelectedAlgebra :
    SelectedNativeCylinderAlgebra
  originWilsonPolynomialSelectedAlgebra = record
    { SelectedNativeCylinderAlgebra.Observable = OriginWilsonPolynomial
    ; SelectedNativeCylinderAlgebra.selectedSection =
        evalOriginWilsonPolynomial
    ; SelectedNativeCylinderAlgebra.zeroObservable = zeroP
    ; SelectedNativeCylinderAlgebra.oneObservable = oneP
    ; SelectedNativeCylinderAlgebra.addObservable = addP
    ; SelectedNativeCylinderAlgebra.scalarObservable = scaleP
    ; SelectedNativeCylinderAlgebra.zeroMeaning =
        λ n links → refl
    ; SelectedNativeCylinderAlgebra.oneMeaning =
        λ n links → refl
    ; SelectedNativeCylinderAlgebra.addMeaning =
        λ n left right links → refl
    ; SelectedNativeCylinderAlgebra.scalarMeaning =
        λ n scalar expr links → refl
    ; SelectedNativeCylinderAlgebra.Nonnegative =
        λ expr → ∀ n links →
          0ℝ ≤ℝ evalOriginWilsonPolynomial expr n links
    ; SelectedNativeCylinderAlgebra.nonnegativeMeaning =
        λ expr positive n links → positive n links
    ; SelectedNativeCylinderAlgebra.gaugeInvariantSelection =
        originPolynomialGaugeInvariant
    }
