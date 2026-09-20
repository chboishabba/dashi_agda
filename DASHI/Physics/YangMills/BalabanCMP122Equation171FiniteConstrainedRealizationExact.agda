module DASHI.Physics.YangMills.BalabanCMP122Equation171FiniteConstrainedRealizationExact where

------------------------------------------------------------------------
-- CMP122 EQ.(1.71) FINITE-REALIZATION ABI
--
-- Decompose source T-mass -> Gate4 finite T-operation into:
--
-- G1 source integration fibre = Gate4 fastFibre
-- G2 source coarse selector = Gate4 coarseMatches
-- G3 source exponential density = embedded Gate4 one-integrand
-- G4 source localized integral = finite real selected fold
--
-- Any Eq.(1.71) normalization/Jacobian/measure factors belong in G3.  The
-- compiler below then proves the total source-mass = embedded Gate4 mass.
--
-- G4 is intentionally explicit: if the literal source integral is not
-- definitionally the selected finite quadrature, this is the genuine
-- quadrature/Haar-realization theorem rather than bookkeeping.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as AddEmbed
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as BaseEmbed
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanEmbeddedCanonicalRationalConstrainedFoldExact as Embedded

embedQ :
  RingEmbed.RationalRealRingEmbedding → ℚ → ℝ
embedQ embedding =
  BaseEmbed.embed
    (AddEmbed.base (RingEmbed.additive embedding))

record CMP122Equation171FiniteConstrainedRealization
    {Scale Fine SlowField Component Functional : Set}
    (construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional)
    (source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField)
    (embedding :
      RingEmbed.RationalRealRingEmbedding) : Set₁ where
  field
    scaleAt : Nat → Scale

    selectedAt : ∀ cutoff →
      T.SecondClassComponent
        (T.classData (PhysicalT.canonicalPhysicalTData construction))
        (scaleAt cutoff)

    -- G1: literal Eq.(1.71) integration variables / fibre.
    sourceFibre :
      Nat → SlowField → List Fine

    fibreIsGate4FastFibre :
      ∀ cutoff slow →
      sourceFibre cutoff slow
      ≡
      T.fastFibre
        (PhysicalT.canonicalPhysicalTData construction)
        (scaleAt cutoff)
        (T.component (selectedAt cutoff))

    -- G2: literal source coarse/block constraint.
    sourceCoarseMatches :
      Nat → Fine → SlowField → Bool

    sourceCoarseMatchesIsGate4 :
      ∀ cutoff fine slow →
      sourceCoarseMatches cutoff fine slow
      ≡
      Integral.coarseMatches
        (T.sumData (PhysicalT.canonicalPhysicalTData construction))
        fine slow

    sourceSelectedIntegrand :
      Nat → SlowField → Fine → ℝ

    sourceSelectedWhenTrue :
      ∀ cutoff slow fine →
      sourceCoarseMatches cutoff fine slow ≡ true →
      sourceSelectedIntegrand cutoff slow fine
      ≡
      Eq171.equation171ExponentialDensity source cutoff slow fine

    sourceSelectedWhenFalse :
      ∀ cutoff slow fine →
      sourceCoarseMatches cutoff fine slow ≡ false →
      sourceSelectedIntegrand cutoff slow fine
      ≡ 0ℝ

    -- G3/G5: all pointwise source density, Jacobian, determinant,
    -- localization, patch and functional-one factors are identified here.
    exponentialDensityIsEmbeddedGate4OneIntegrand :
      ∀ cutoff slow fine →
      Eq171.equation171ExponentialDensity source cutoff slow fine
      ≡
      embedQ embedding
        (T.localIntegrand
          (PhysicalT.canonicalPhysicalTData construction)
          (scaleAt cutoff)
          (T.component (selectedAt cutoff))
          slow
          (T.oneFunctional
            (PhysicalT.canonicalPhysicalTData construction))
          fine)

    -- G4: literal localized integration -> selected finite real fold.
    -- This is the genuine finite quadrature/Haar realization if not definitional.
    equation171IntegralIsFiniteSelectedFold :
      ∀ cutoff slow →
      Eq171.equation171ConstrainedIntegral source cutoff slow
        (Eq171.equation171ExponentialDensity source cutoff slow)
      ≡
      RingEmbed.realSum
        (sourceFibre cutoff slow)
        (sourceSelectedIntegrand cutoff slow)

open CMP122Equation171FiniteConstrainedRealization public

sourceSelectedIntegrandIsEmbeddedGate4Selected :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    (realization :
      CMP122Equation171FiniteConstrainedRealization
        construction source embedding)
    cutoff slow fine →
  sourceSelectedIntegrand realization cutoff slow fine
  ≡
  embedQ embedding
    (Integral.selectedWith
      (T.sumData (PhysicalT.canonicalPhysicalTData construction))
      (T.localIntegrand
        (PhysicalT.canonicalPhysicalTData construction)
        (scaleAt realization cutoff)
        (T.component (selectedAt realization cutoff))
        slow
        (T.oneFunctional
          (PhysicalT.canonicalPhysicalTData construction)))
      slow fine)
sourceSelectedIntegrandIsEmbeddedGate4Selected
  {construction = construction} {embedding = embedding}
  realization cutoff slow fine
  with sourceCoarseMatches realization cutoff fine slow
     | Integral.coarseMatches
         (T.sumData (PhysicalT.canonicalPhysicalTData construction))
         fine slow
     | sourceCoarseMatchesIsGate4 realization cutoff fine slow
... | true | true | refl =
  trans
    (sourceSelectedWhenTrue realization cutoff slow fine refl)
    (exponentialDensityIsEmbeddedGate4OneIntegrand
      realization cutoff slow fine)
... | false | false | refl =
  trans
    (sourceSelectedWhenFalse realization cutoff slow fine refl)
    (sym
      (BaseEmbed.zeroExact
        (AddEmbed.base (RingEmbed.additive embedding))))

sourceFiniteFoldIsEmbeddedGate4Fold :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    (realization :
      CMP122Equation171FiniteConstrainedRealization
        construction source embedding)
    cutoff slow →
  RingEmbed.realSum
    (sourceFibre realization cutoff slow)
    (sourceSelectedIntegrand realization cutoff slow)
  ≡
  embedQ embedding
    (T.localizedTOperation
      (PhysicalT.canonicalPhysicalTData construction)
      (scaleAt realization cutoff)
      (selectedAt realization cutoff)
      slow
      (T.oneFunctional
        (PhysicalT.canonicalPhysicalTData construction)))
sourceFiniteFoldIsEmbeddedGate4Fold
  {construction = construction} {embedding = embedding}
  realization cutoff slow
  rewrite fibreIsGate4FastFibre realization cutoff slow =
  trans
    (RingEmbed.realSumCong
      (T.fastFibre
        (PhysicalT.canonicalPhysicalTData construction)
        (scaleAt realization cutoff)
        (T.component (selectedAt realization cutoff)))
      (sourceSelectedIntegrandIsEmbeddedGate4Selected
        realization cutoff slow))
    (sym
      (Embedded.embeddedConstrainedIntegralExact
        embedding
        (PhysicalT.sumCarrier construction)
        (T.fastFibre
          (PhysicalT.canonicalPhysicalTData construction)
          (scaleAt realization cutoff)
          (T.component (selectedAt realization cutoff)))
        (T.localIntegrand
          (PhysicalT.canonicalPhysicalTData construction)
          (scaleAt realization cutoff)
          (T.component (selectedAt realization cutoff))
          slow
          (T.oneFunctional
            (PhysicalT.canonicalPhysicalTData construction)))
        slow))

equation171SourceMassIsEmbeddedGate4TOperation :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField}
    {embedding : RingEmbed.RationalRealRingEmbedding}
    (realization :
      CMP122Equation171FiniteConstrainedRealization
        construction source embedding)
    cutoff slow →
  Eq171.sourceTOperationMass source cutoff slow
  ≡
  embedQ embedding
    (T.localizedTOperation
      (PhysicalT.canonicalPhysicalTData construction)
      (scaleAt realization cutoff)
      (selectedAt realization cutoff)
      slow
      (T.oneFunctional
        (PhysicalT.canonicalPhysicalTData construction)))
equation171SourceMassIsEmbeddedGate4TOperation realization cutoff slow =
  trans
    (Eq171.equation171DefinesTOperationMass _ cutoff slow)
    (trans
      (equation171IntegralIsFiniteSelectedFold realization cutoff slow)
      (sourceFiniteFoldIsEmbeddedGate4Fold realization cutoff slow))

equation171FiniteFibreCompilerLevel : ProofLevel
equation171FiniteFibreCompilerLevel = machineChecked

equation171FiniteSelectorCompilerLevel : ProofLevel
equation171FiniteSelectorCompilerLevel = machineChecked

equation171FiniteIntegrandCompilerLevel : ProofLevel
equation171FiniteIntegrandCompilerLevel = machineChecked

equation171FiniteFoldTransportCompilerLevel : ProofLevel
equation171FiniteFoldTransportCompilerLevel = machineChecked

equation171TotalPhysicalTOperationCompilerLevel : ProofLevel
equation171TotalPhysicalTOperationCompilerLevel = machineChecked

-- The actual remaining realization leaves.
literalEquation171FibreIsGate4FastFibreLevel : ProofLevel
literalEquation171FibreIsGate4FastFibreLevel = conditional

literalEquation171ConstraintIsGate4SelectorLevel : ProofLevel
literalEquation171ConstraintIsGate4SelectorLevel = conditional

literalEquation171DensityIsEmbeddedGate4OneIntegrandLevel : ProofLevel
literalEquation171DensityIsEmbeddedGate4OneIntegrandLevel = conditional

literalEquation171IntegralIsFiniteSelectedFoldLevel : ProofLevel
literalEquation171IntegralIsFiniteSelectedFoldLevel = conditional

-- G5 is not a separate equality in the compiler: any source normalization,
-- Jacobian, determinant, localization or patch factor must be paid inside G3.
literalEquation171MeasureFactorsAbsorbedInIntegrandLevel : ProofLevel
literalEquation171MeasureFactorsAbsorbedInIntegrandLevel = conditional
