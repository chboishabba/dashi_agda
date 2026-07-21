module DASHI.Physics.YangMills.BalabanPatchTransferAnalyticReduction where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Highest-alpha analytic reduction.
--
-- The five patch estimates need not be proved independently.  Boundary,
-- interface, corner and nested-restriction estimates are transported from a
-- bulk estimate through explicit extension/restriction comparison maps.  The
-- remaining analytic leaves are therefore one bulk estimate plus four
-- quantitative transfer estimates for each operator family.
------------------------------------------------------------------------

record OrderedBoundCarrier : Set₁ where
  field
    Bound : Set
    one : Bound
    add multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    reflexive : ∀ x → LessEqual x x
    transitive : ∀ {x y z} → LessEqual x y → LessEqual y z → LessEqual x z
    multiplyMonotone : ∀ {a b c d} →
      LessEqual a b → LessEqual c d →
      LessEqual (multiply a c) (multiply b d)

open OrderedBoundCarrier public

record PatchTransferFactors (O : OrderedBoundCarrier) : Set where
  field
    boundaryFactor interfaceFactor cornerFactor nestedFactor : Bound O

open PatchTransferFactors public

------------------------------------------------------------------------
-- Hodge coercivity transfer.
------------------------------------------------------------------------

record HodgeTransferData (O : OrderedBoundCarrier)
    (Index State : Set) : Set₁ where
  field
    bulkEnergy patchEnergy normSq : Index → State → Bound O
    cBulk cBoundary cInterface cCorner cNested : Bound O

    bulkCoercive : ∀ i h →
      LessEqual O (multiply O cBulk (normSq i h)) (bulkEnergy i h)

    boundaryCompare interfaceCompare cornerCompare nestedCompare :
      ∀ i h → LessEqual O (bulkEnergy i h) (patchEnergy i h)

    boundaryConstantTransport :
      LessEqual O cBoundary cBulk
    interfaceConstantTransport :
      LessEqual O cInterface cBulk
    cornerConstantTransport :
      LessEqual O cCorner cBulk
    nestedConstantTransport :
      LessEqual O cNested cBulk

open HodgeTransferData public

boundaryHodgeFromBulk :
  ∀ {Index State} {O : OrderedBoundCarrier} →
  (D : HodgeTransferData O Index State) → ∀ i h →
  LessEqual O
    (multiply O (cBoundary D) (normSq D i h))
    (patchEnergy D i h)
boundaryHodgeFromBulk D i h =
  transitive _
    (multiplyMonotone _ (boundaryConstantTransport D) (reflexive _ (normSq D i h)))
    (transitive _ (bulkCoercive D i h) (boundaryCompare D i h))

interfaceHodgeFromBulk :
  ∀ {Index State} {O : OrderedBoundCarrier} →
  (D : HodgeTransferData O Index State) → ∀ i h →
  LessEqual O
    (multiply O (cInterface D) (normSq D i h))
    (patchEnergy D i h)
interfaceHodgeFromBulk D i h =
  transitive _
    (multiplyMonotone _ (interfaceConstantTransport D) (reflexive _ (normSq D i h)))
    (transitive _ (bulkCoercive D i h) (interfaceCompare D i h))

cornerHodgeFromBulk :
  ∀ {Index State} {O : OrderedBoundCarrier} →
  (D : HodgeTransferData O Index State) → ∀ i h →
  LessEqual O
    (multiply O (cCorner D) (normSq D i h))
    (patchEnergy D i h)
cornerHodgeFromBulk D i h =
  transitive _
    (multiplyMonotone _ (cornerConstantTransport D) (reflexive _ (normSq D i h)))
    (transitive _ (bulkCoercive D i h) (cornerCompare D i h))

nestedHodgeFromBulk :
  ∀ {Index State} {O : OrderedBoundCarrier} →
  (D : HodgeTransferData O Index State) → ∀ i h →
  LessEqual O
    (multiply O (cNested D) (normSq D i h))
    (patchEnergy D i h)
nestedHodgeFromBulk D i h =
  transitive _
    (multiplyMonotone _ (nestedConstantTransport D) (reflexive _ (normSq D i h)))
    (transitive _ (bulkCoercive D i h) (nestedCompare D i h))

------------------------------------------------------------------------
-- Green and derivative-Green transfer.
------------------------------------------------------------------------

record GreenTransferData (O : OrderedBoundCarrier)
    (Index State : Set) : Set₁ where
  field
    norm : State → Bound O
    bulkGreen patchGreen : Index → State → State
    bulkGradient patchGradient : Index → State → State
    bulkSecond patchSecond : Index → State → State

    cBulkGreen cBoundaryGreen cInterfaceGreen cCornerGreen cNestedGreen : Bound O
    cBulkGradient cBoundaryGradient cInterfaceGradient cCornerGradient cNestedGradient : Bound O
    cBulkSecond cBoundarySecond cInterfaceSecond cCornerSecond cNestedSecond : Bound O

    bulkGreenBound : ∀ i f →
      LessEqual O (norm (bulkGreen i f)) (multiply O cBulkGreen (norm f))
    bulkGradientBound : ∀ i f →
      LessEqual O (norm (bulkGradient i f)) (multiply O cBulkGradient (norm f))
    bulkSecondBound : ∀ i f →
      LessEqual O (norm (bulkSecond i f)) (multiply O cBulkSecond (norm f))

    boundaryGreenTransfer : ∀ i f →
      LessEqual O (norm (patchGreen i f)) (norm (bulkGreen i f))
    interfaceGreenTransfer : ∀ i f →
      LessEqual O (norm (patchGreen i f)) (norm (bulkGreen i f))
    cornerGreenTransfer : ∀ i f →
      LessEqual O (norm (patchGreen i f)) (norm (bulkGreen i f))
    nestedGreenTransfer : ∀ i f →
      LessEqual O (norm (patchGreen i f)) (norm (bulkGreen i f))

    boundaryGradientTransfer interfaceGradientTransfer
      cornerGradientTransfer nestedGradientTransfer : ∀ i f →
      LessEqual O (norm (patchGradient i f)) (norm (bulkGradient i f))

    boundarySecondTransfer interfaceSecondTransfer
      cornerSecondTransfer nestedSecondTransfer : ∀ i f →
      LessEqual O (norm (patchSecond i f)) (norm (bulkSecond i f))

    boundaryGreenConstant : LessEqual O cBulkGreen cBoundaryGreen
    interfaceGreenConstant : LessEqual O cBulkGreen cInterfaceGreen
    cornerGreenConstant : LessEqual O cBulkGreen cCornerGreen
    nestedGreenConstant : LessEqual O cBulkGreen cNestedGreen

    boundaryGradientConstant : LessEqual O cBulkGradient cBoundaryGradient
    interfaceGradientConstant : LessEqual O cBulkGradient cInterfaceGradient
    cornerGradientConstant : LessEqual O cBulkGradient cCornerGradient
    nestedGradientConstant : LessEqual O cBulkGradient cNestedGradient

    boundarySecondConstant : LessEqual O cBulkSecond cBoundarySecond
    interfaceSecondConstant : LessEqual O cBulkSecond cInterfaceSecond
    cornerSecondConstant : LessEqual O cBulkSecond cCornerSecond
    nestedSecondConstant : LessEqual O cBulkSecond cNestedSecond

open GreenTransferData public

private
  promoteOperatorBound :
    ∀ {O : OrderedBoundCarrier} {State : Set}
      (norm : State → Bound O) {local patch source : State}
      {cLocal cPatch : Bound O} →
    LessEqual O (norm patch) (norm local) →
    LessEqual O (norm local) (multiply O cLocal (norm source)) →
    LessEqual O cLocal cPatch →
    LessEqual O (norm patch) (multiply O cPatch (norm source))
  promoteOperatorBound {O} norm patch≤local local≤bound c≤c′ =
    transitive O patch≤local
      (transitive O local≤bound
        (multiplyMonotone O c≤c′ (reflexive O _)))

boundaryGreenFromBulk :
  ∀ {Index State O} (D : GreenTransferData O Index State) i f →
  LessEqual O (norm D (patchGreen D i f))
    (multiply O (cBoundaryGreen D) (norm D f))
boundaryGreenFromBulk D i f =
  promoteOperatorBound (norm D)
    (boundaryGreenTransfer D i f)
    (bulkGreenBound D i f)
    (boundaryGreenConstant D)

interfaceGreenFromBulk :
  ∀ {Index State O} (D : GreenTransferData O Index State) i f →
  LessEqual O (norm D (patchGreen D i f))
    (multiply O (cInterfaceGreen D) (norm D f))
interfaceGreenFromBulk D i f =
  promoteOperatorBound (norm D)
    (interfaceGreenTransfer D i f)
    (bulkGreenBound D i f)
    (interfaceGreenConstant D)

cornerGreenFromBulk :
  ∀ {Index State O} (D : GreenTransferData O Index State) i f →
  LessEqual O (norm D (patchGreen D i f))
    (multiply O (cCornerGreen D) (norm D f))
cornerGreenFromBulk D i f =
  promoteOperatorBound (norm D)
    (cornerGreenTransfer D i f)
    (bulkGreenBound D i f)
    (cornerGreenConstant D)

nestedGreenFromBulk :
  ∀ {Index State O} (D : GreenTransferData O Index State) i f →
  LessEqual O (norm D (patchGreen D i f))
    (multiply O (cNestedGreen D) (norm D f))
nestedGreenFromBulk D i f =
  promoteOperatorBound (norm D)
    (nestedGreenTransfer D i f)
    (bulkGreenBound D i f)
    (nestedGreenConstant D)

------------------------------------------------------------------------
-- Residual transfer and strict q reduction.
------------------------------------------------------------------------

record ResidualTransferData (O : OrderedBoundCarrier)
    (Index State : Set) : Set₁ where
  field
    norm : State → Bound O
    bulkResidual patchResidual : Index → State → State
    qBulk qBoundary qInterface qCorner qNested qCommon one : Bound O

    bulkResidualBound : ∀ i f →
      LessEqual O (norm (bulkResidual i f)) (multiply O qBulk (norm f))

    boundaryResidualTransfer interfaceResidualTransfer
      cornerResidualTransfer nestedResidualTransfer : ∀ i f →
      LessEqual O (norm (patchResidual i f)) (norm (bulkResidual i f))

    bulkBelowBoundary : LessEqual O qBulk qBoundary
    bulkBelowInterface : LessEqual O qBulk qInterface
    bulkBelowCorner : LessEqual O qBulk qCorner
    bulkBelowNested : LessEqual O qBulk qNested

    boundaryBelowCommon : LessEqual O qBoundary qCommon
    interfaceBelowCommon : LessEqual O qInterface qCommon
    cornerBelowCommon : LessEqual O qCorner qCommon
    nestedBelowCommon : LessEqual O qNested qCommon

    StrictlyBelow : Bound O → Bound O → Set
    qCommonStrict : StrictlyBelow qCommon one

open ResidualTransferData public

boundaryResidualFromBulk :
  ∀ {Index State O} (D : ResidualTransferData O Index State) i f →
  LessEqual O (norm D (patchResidual D i f))
    (multiply O (qBoundary D) (norm D f))
boundaryResidualFromBulk D i f =
  promoteOperatorBound (norm D)
    (boundaryResidualTransfer D i f)
    (bulkResidualBound D i f)
    (bulkBelowBoundary D)

interfaceResidualFromBulk :
  ∀ {Index State O} (D : ResidualTransferData O Index State) i f →
  LessEqual O (norm D (patchResidual D i f))
    (multiply O (qInterface D) (norm D f))
interfaceResidualFromBulk D i f =
  promoteOperatorBound (norm D)
    (interfaceResidualTransfer D i f)
    (bulkResidualBound D i f)
    (bulkBelowInterface D)

cornerResidualFromBulk :
  ∀ {Index State O} (D : ResidualTransferData O Index State) i f →
  LessEqual O (norm D (patchResidual D i f))
    (multiply O (qCorner D) (norm D f))
cornerResidualFromBulk D i f =
  promoteOperatorBound (norm D)
    (cornerResidualTransfer D i f)
    (bulkResidualBound D i f)
    (bulkBelowCorner D)

nestedResidualFromBulk :
  ∀ {Index State O} (D : ResidualTransferData O Index State) i f →
  LessEqual O (norm D (patchResidual D i f))
    (multiply O (qNested D) (norm D f))
nestedResidualFromBulk D i f =
  promoteOperatorBound (norm D)
    (nestedResidualTransfer D i f)
    (bulkResidualBound D i f)
    (bulkBelowNested D)

------------------------------------------------------------------------
-- One coherent reduction certificate.
------------------------------------------------------------------------

record PatchTransferAnalyticInputs
    (O : OrderedBoundCarrier) (Index State : Set) : Set₁ where
  field
    hodge : HodgeTransferData O Index State
    green : GreenTransferData O Index State
    residual : ResidualTransferData O Index State

record PatchTransferAnalyticCertificate
    {O : OrderedBoundCarrier} {Index State : Set}
    (I : PatchTransferAnalyticInputs O Index State) : Set₁ where
  open PatchTransferAnalyticInputs I
  field
    boundaryHodge : ∀ i h →
      LessEqual O
        (multiply O (cBoundary hodge) (normSq hodge i h))
        (patchEnergy hodge i h)
    boundaryGreen : ∀ i f →
      LessEqual O (norm green (patchGreen green i f))
        (multiply O (cBoundaryGreen green) (norm green f))
    boundaryResidual : ∀ i f →
      LessEqual O (norm residual (patchResidual residual i f))
        (multiply O (qBoundary residual) (norm residual f))
    strictCommonResidual : StrictlyBelow residual (qCommon residual) (one residual)

assemblePatchTransferAnalyticReduction :
  ∀ {O Index State} →
  (I : PatchTransferAnalyticInputs O Index State) →
  PatchTransferAnalyticCertificate I
assemblePatchTransferAnalyticReduction I = record
  { boundaryHodge = boundaryHodgeFromBulk (PatchTransferAnalyticInputs.hodge I)
  ; boundaryGreen = boundaryGreenFromBulk (PatchTransferAnalyticInputs.green I)
  ; boundaryResidual = boundaryResidualFromBulk (PatchTransferAnalyticInputs.residual I)
  ; strictCommonResidual = qCommonStrict (PatchTransferAnalyticInputs.residual I)
  }

patchTransferAnalyticReductionAssemblyLevel : ProofLevel
patchTransferAnalyticReductionAssemblyLevel = machineChecked

bulkAndTransferEstimateInputsLevel : ProofLevel
bulkAndTransferEstimateInputsLevel = conditional
