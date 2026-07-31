module DASHI.Physics.YangMills.BalabanClayGate4TwoFamilyChannelMajorantExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Two-family reduction of the five physical Hessian channels.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
-- Relationship: the curvature, transport and chart channels share the same
-- quantitative SU(2) nonlinearity data (Ad, dexp and dexp^{-1}).
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics (1995 reprint).
-- DOI: 10.1007/978-3-642-66282-9.
-- Relationship: the gauge and constraint channels share inverse/resolvent and
-- relative-boundedness estimates.
--
-- The point of this module is architectural but theorem-bearing: five direct
-- uniform estimates are reduced to two reusable defect majorants.  Each of the
-- first three channels is locally dominated by a coefficient times one SU(2)
-- defect; each of the last two is dominated by a coefficient times one
-- resolvent defect.  Two uniform defect bounds then produce all five physical
-- form estimates in the exact scalar order used by the consumer.
------------------------------------------------------------------------

record OrderedScaleAlgebra (Bound : Set) : Set₁ where
  field
    LessEqual : Bound → Bound → Set
    multiply : Bound → Bound → Bound

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    multiplyMonotoneLeft : ∀ coefficient {lower upper} →
      LessEqual lower upper →
      LessEqual (multiply coefficient lower) (multiply coefficient upper)

open OrderedScaleAlgebra public

record FiveChannelForms (Vector Bound : Set) : Set₁ where
  field
    curvatureForm transportForm chartForm : Vector → Bound
    gaugeForm constraintForm : Vector → Bound

open FiveChannelForms public

record TwoFamilyChannelMajorant
    (Vector Bound : Set) : Set₁ where
  field
    algebra : OrderedScaleAlgebra Bound
    forms : FiveChannelForms Vector Bound

    UnitState : Vector → Set

    su2Defect resolventDefect : Vector → Bound
    su2DefectBudget resolventDefectBudget : Bound

    curvatureCoefficient transportCoefficient chartCoefficient : Bound
    gaugeCoefficient constraintCoefficient : Bound

    curvatureToSU2 : ∀ vector → UnitState vector →
      LessEqual algebra
        (curvatureForm forms vector)
        (multiply algebra curvatureCoefficient (su2Defect vector))

    transportToSU2 : ∀ vector → UnitState vector →
      LessEqual algebra
        (transportForm forms vector)
        (multiply algebra transportCoefficient (su2Defect vector))

    chartToSU2 : ∀ vector → UnitState vector →
      LessEqual algebra
        (chartForm forms vector)
        (multiply algebra chartCoefficient (su2Defect vector))

    gaugeToResolvent : ∀ vector → UnitState vector →
      LessEqual algebra
        (gaugeForm forms vector)
        (multiply algebra gaugeCoefficient (resolventDefect vector))

    constraintToResolvent : ∀ vector → UnitState vector →
      LessEqual algebra
        (constraintForm forms vector)
        (multiply algebra constraintCoefficient (resolventDefect vector))

    su2DefectUniform : ∀ vector → UnitState vector →
      LessEqual algebra (su2Defect vector) su2DefectBudget

    resolventDefectUniform : ∀ vector → UnitState vector →
      LessEqual algebra (resolventDefect vector) resolventDefectBudget

open TwoFamilyChannelMajorant public

curvatureBudget :
  ∀ {Vector Bound} → TwoFamilyChannelMajorant Vector Bound → Bound
curvatureBudget dataSet =
  multiply (algebra dataSet)
    (curvatureCoefficient dataSet) (su2DefectBudget dataSet)

transportBudget :
  ∀ {Vector Bound} → TwoFamilyChannelMajorant Vector Bound → Bound
transportBudget dataSet =
  multiply (algebra dataSet)
    (transportCoefficient dataSet) (su2DefectBudget dataSet)

chartBudget :
  ∀ {Vector Bound} → TwoFamilyChannelMajorant Vector Bound → Bound
chartBudget dataSet =
  multiply (algebra dataSet)
    (chartCoefficient dataSet) (su2DefectBudget dataSet)

gaugeBudget :
  ∀ {Vector Bound} → TwoFamilyChannelMajorant Vector Bound → Bound
gaugeBudget dataSet =
  multiply (algebra dataSet)
    (gaugeCoefficient dataSet) (resolventDefectBudget dataSet)

constraintBudget :
  ∀ {Vector Bound} → TwoFamilyChannelMajorant Vector Bound → Bound
constraintBudget dataSet =
  multiply (algebra dataSet)
    (constraintCoefficient dataSet) (resolventDefectBudget dataSet)

curvatureUniformFromSU2Majorant :
  ∀ {Vector Bound}
    (dataSet : TwoFamilyChannelMajorant Vector Bound)
    vector → UnitState dataSet vector →
  LessEqual (algebra dataSet)
    (curvatureForm (forms dataSet) vector)
    (curvatureBudget dataSet)
curvatureUniformFromSU2Majorant dataSet vector unit =
  transitive (algebra dataSet)
    (curvatureToSU2 dataSet vector unit)
    (multiplyMonotoneLeft (algebra dataSet)
      (curvatureCoefficient dataSet)
      (su2DefectUniform dataSet vector unit))

transportUniformFromSU2Majorant :
  ∀ {Vector Bound}
    (dataSet : TwoFamilyChannelMajorant Vector Bound)
    vector → UnitState dataSet vector →
  LessEqual (algebra dataSet)
    (transportForm (forms dataSet) vector)
    (transportBudget dataSet)
transportUniformFromSU2Majorant dataSet vector unit =
  transitive (algebra dataSet)
    (transportToSU2 dataSet vector unit)
    (multiplyMonotoneLeft (algebra dataSet)
      (transportCoefficient dataSet)
      (su2DefectUniform dataSet vector unit))

chartUniformFromSU2Majorant :
  ∀ {Vector Bound}
    (dataSet : TwoFamilyChannelMajorant Vector Bound)
    vector → UnitState dataSet vector →
  LessEqual (algebra dataSet)
    (chartForm (forms dataSet) vector)
    (chartBudget dataSet)
chartUniformFromSU2Majorant dataSet vector unit =
  transitive (algebra dataSet)
    (chartToSU2 dataSet vector unit)
    (multiplyMonotoneLeft (algebra dataSet)
      (chartCoefficient dataSet)
      (su2DefectUniform dataSet vector unit))

gaugeUniformFromResolventMajorant :
  ∀ {Vector Bound}
    (dataSet : TwoFamilyChannelMajorant Vector Bound)
    vector → UnitState dataSet vector →
  LessEqual (algebra dataSet)
    (gaugeForm (forms dataSet) vector)
    (gaugeBudget dataSet)
gaugeUniformFromResolventMajorant dataSet vector unit =
  transitive (algebra dataSet)
    (gaugeToResolvent dataSet vector unit)
    (multiplyMonotoneLeft (algebra dataSet)
      (gaugeCoefficient dataSet)
      (resolventDefectUniform dataSet vector unit))

constraintUniformFromResolventMajorant :
  ∀ {Vector Bound}
    (dataSet : TwoFamilyChannelMajorant Vector Bound)
    vector → UnitState dataSet vector →
  LessEqual (algebra dataSet)
    (constraintForm (forms dataSet) vector)
    (constraintBudget dataSet)
constraintUniformFromResolventMajorant dataSet vector unit =
  transitive (algebra dataSet)
    (constraintToResolvent dataSet vector unit)
    (multiplyMonotoneLeft (algebra dataSet)
      (constraintCoefficient dataSet)
      (resolventDefectUniform dataSet vector unit))

record FiveChannelUniformBounds
    (Vector Bound : Set)
    (dataSet : TwoFamilyChannelMajorant Vector Bound) : Set₁ where
  field
    curvatureUniform : ∀ vector → UnitState dataSet vector →
      LessEqual (algebra dataSet)
        (curvatureForm (forms dataSet) vector)
        (curvatureBudget dataSet)

    transportUniform : ∀ vector → UnitState dataSet vector →
      LessEqual (algebra dataSet)
        (transportForm (forms dataSet) vector)
        (transportBudget dataSet)

    chartUniform : ∀ vector → UnitState dataSet vector →
      LessEqual (algebra dataSet)
        (chartForm (forms dataSet) vector)
        (chartBudget dataSet)

    gaugeUniform : ∀ vector → UnitState dataSet vector →
      LessEqual (algebra dataSet)
        (gaugeForm (forms dataSet) vector)
        (gaugeBudget dataSet)

    constraintUniform : ∀ vector → UnitState dataSet vector →
      LessEqual (algebra dataSet)
        (constraintForm (forms dataSet) vector)
        (constraintBudget dataSet)

open FiveChannelUniformBounds public

fiveChannelBoundsFromTwoFamilies :
  ∀ {Vector Bound}
    (dataSet : TwoFamilyChannelMajorant Vector Bound) →
  FiveChannelUniformBounds Vector Bound dataSet
fiveChannelBoundsFromTwoFamilies dataSet = record
  { curvatureUniform = curvatureUniformFromSU2Majorant dataSet
  ; transportUniform = transportUniformFromSU2Majorant dataSet
  ; chartUniform = chartUniformFromSU2Majorant dataSet
  ; gaugeUniform = gaugeUniformFromResolventMajorant dataSet
  ; constraintUniform = constraintUniformFromResolventMajorant dataSet
  }

twoFamilyFiveChannelReductionLevel : ProofLevel
twoFamilyFiveChannelReductionLevel = machineChecked

su2NonlinearityFamilyProvenanceLevel : ProofLevel
su2NonlinearityFamilyProvenanceLevel = standardImported

resolventRelativeBoundFamilyProvenanceLevel : ProofLevel
resolventRelativeBoundFamilyProvenanceLevel = standardImported

physicalSU2DefectMajorantInputsLevel : ProofLevel
physicalSU2DefectMajorantInputsLevel = conditional

physicalResolventDefectMajorantInputsLevel : ProofLevel
physicalResolventDefectMajorantInputsLevel = conditional
