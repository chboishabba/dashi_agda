module DASHI.Moonshine.VNaturalOrbifoldConstruction where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (ℤ)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)

import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA

------------------------------------------------------------------------
-- FLM-shaped orbifold construction surface for V^natural.
--
-- This module does not postulate that the moonshine module exists.  Instead it
-- isolates the exact construction data required by the standard Leech-lattice
-- involution/orbifold route:
--
--   V_Λ  -- fixed-point VOA under θ
--       \-- θ-twisted module, integral/even sector
--
--   V^natural = V_Λ^+ ⊕ (V_Λ^T)^+.
--
-- The original tagged coproduct carrier below is only a set-level interface;
-- the genuine two-summand linear carrier is the paired product defined below.
-- Promotion to a VOA requires real original mixed-sector mode, Jacobi,
-- locality, conformal, linear and simplicity witnesses.

record VOAInvolution (V : VOA.VertexOperatorAlgebra) : Setω where
  field
    theta :
      VOA.GradedModule.Carrier (VOA.VertexOperatorAlgebra.gradedModule V) →
      VOA.GradedModule.Carrier (VOA.VertexOperatorAlgebra.gradedModule V)
    involutive : ∀ x → theta (theta x) ≡ x
    preservesVacuum : Set
    preservesConformalVector : Set
    preservesVertexModes : Set
    preservesGrading : Set

open VOAInvolution public

record FixedPointVOA
  (V : VOA.VertexOperatorAlgebra)
  (involution : VOAInvolution V) : Setω where
  field
    fixedCarrier : Set
    includeFixed :
      fixedCarrier →
      VOA.GradedModule.Carrier (VOA.VertexOperatorAlgebra.gradedModule V)
    fixedByTheta :
      ∀ x →
      VOAInvolution.theta involution (includeFixed x) ≡ includeFixed x
    fixedVOA : VOA.VertexOperatorAlgebra
    inclusionPreservesVOA : Set

open FixedPointVOA public

record TwistedModule
  (V : VOA.VertexOperatorAlgebra)
  (involution : VOAInvolution V) : Setω where
  field
    Scalar : Set
    Carrier : Set
    TwistIndex : Set
    twistedMode :
      VOA.GradedModule.Carrier (VOA.VertexOperatorAlgebra.gradedModule V) →
      TwistIndex → Carrier → Carrier
    twistedLowerTruncation : Set
    twistedVacuumCompatibility : Set
    twistedTranslationCovariance : Set
    twistedJacobiIdentity : Set
    thetaMonodromy : Set
    conformalWeight : Carrier → Set

open TwistedModule public

record TwistedEvenSector
  {V : VOA.VertexOperatorAlgebra}
  {involution : VOAInvolution V}
  (twisted : TwistedModule V involution) : Setω where
  field
    CarrierPlus : Set
    includePlus : CarrierPlus → TwistedModule.Carrier twisted
    integralWeight : ∀ x → TwistedModule.conformalWeight twisted (includePlus x)
    thetaEven : Set

open TwistedEvenSector public

OrbifoldCarrier :
  ∀ {V involution}
  (fixed : FixedPointVOA V involution)
  (twisted : TwistedModule V involution)
  (plus : TwistedEvenSector twisted) → Set
OrbifoldCarrier fixed twisted plus =
  FixedPointVOA.fixedCarrier fixed ⊎ TwistedEvenSector.CarrierPlus plus



------------------------------------------------------------------------
-- Correct *linear* direct-sum carrier, beside the legacy tagged sum.
-- This is additive pair data A × B, NOT A ⊎ B. The old carrier is kept
-- for compatibility until an original FLM sectorwise VOA structure
-- and a source-native migration are proved. No physical model is
-- asserted merely from this set-level product.
------------------------------------------------------------------------

LinearOrbifoldCarrier :
  ∀ {V involution}
  (fixed : FixedPointVOA V involution)
  (twisted : TwistedModule V involution)
  (plus : TwistedEvenSector twisted) → Set
LinearOrbifoldCarrier fixed twisted plus =
  FixedPointVOA.fixedCarrier fixed × TwistedEvenSector.CarrierPlus plus

module LinearOrbifoldSummandInclusions
  {V involution}
  (fixed : FixedPointVOA V involution)
  (twisted : TwistedModule V involution)
  (plus : TwistedEvenSector twisted)
  (fixedZero : FixedPointVOA.fixedCarrier fixed)
  (twistedZero : TwistedEvenSector.CarrierPlus plus) where

  Fixed : Set
  Fixed = FixedPointVOA.fixedCarrier fixed

  Twisted : Set
  Twisted = TwistedEvenSector.CarrierPlus plus

  Whole : Set
  Whole = LinearOrbifoldCarrier fixed twisted plus

  includeFixedLinear : Fixed → Whole
  includeFixedLinear x = x , twistedZero

  includeTwistedLinear : Twisted → Whole
  includeTwistedLinear y = fixedZero , y

  originalSummandZerosAgree :
    includeFixedLinear fixedZero ≡ includeTwistedLinear twistedZero
  originalSummandZerosAgree = refl

  -- Pair carriers admit *both* summands in one state, unlike A ⊎ B.
  recoverLinearComponents :
    (x : Fixed) (y : Twisted) →
    Data.Product.proj₁ (x , y) ≡ x
    × Data.Product.proj₂ (x , y) ≡ y
  recoverLinearComponents x y = refl , refl

  linearFixedInclusionInjective :
    (x y : Fixed) →
    includeFixedLinear x ≡ includeFixedLinear y → x ≡ y
  linearFixedInclusionInjective x y refl = refl

  linearTwistedInclusionInjective :
    (x y : Twisted) →
    includeTwistedLinear x ≡ includeTwistedLinear y → x ≡ y
  linearTwistedInclusionInjective x y refl = refl

record OrbifoldVOAAssembly
  {V : VOA.VertexOperatorAlgebra}
  {involution : VOAInvolution V}
  (fixed : FixedPointVOA V involution)
  (twisted : TwistedModule V involution)
  (plus : TwistedEvenSector twisted) : Setω where
  field
    orbifoldVOA : VOA.VertexOperatorAlgebra
    identifyCarrier :
      VOA.GradedModule.Carrier
        (VOA.VertexOperatorAlgebra.gradedModule orbifoldVOA)
      → OrbifoldCarrier fixed twisted plus
    includeFixedSummand :
      FixedPointVOA.fixedCarrier fixed →
      VOA.GradedModule.Carrier
        (VOA.VertexOperatorAlgebra.gradedModule orbifoldVOA)
    includeTwistedSummand :
      TwistedEvenSector.CarrierPlus plus →
      VOA.GradedModule.Carrier
        (VOA.VertexOperatorAlgebra.gradedModule orbifoldVOA)
    fixedSummandIdentifies :
      ∀ x → identifyCarrier (includeFixedSummand x) ≡ inj₁ x
    twistedSummandIdentifies :
      ∀ x → identifyCarrier (includeTwistedSummand x) ≡ inj₂ x
    mixedVertexProductsClosed : Set
    localityAcrossSummands : Set
    JacobiAcrossSummands : Set
    conformalVectorAgrees : Set
    centralCharge24 : Set
    CFTType : Set
    holomorphic : Set
    simple : Set

open OrbifoldVOAAssembly public

record LeechLatticeVOAInput : Setω where
  field
    leechLatticeVOA : VOA.VertexOperatorAlgebra
    leechInvolution : VOAInvolution leechLatticeVOA
    fixedPoint : FixedPointVOA leechLatticeVOA leechInvolution
    canonicalTwistedModule : TwistedModule leechLatticeVOA leechInvolution
    twistedEvenSector : TwistedEvenSector canonicalTwistedModule
    leechRootless : Set
    latticeVOACentralCharge24 : Set

open LeechLatticeVOAInput public

record VNaturalConstruction : Setω where
  field
    leechInput : LeechLatticeVOAInput
    orbifoldAssembly :
      OrbifoldVOAAssembly
        (LeechLatticeVOAInput.fixedPoint leechInput)
        (LeechLatticeVOAInput.canonicalTwistedModule leechInput)
        (LeechLatticeVOAInput.twistedEvenSector leechInput)

  Vnatural : VOA.VertexOperatorAlgebra
  Vnatural = OrbifoldVOAAssembly.orbifoldVOA orbifoldAssembly

  -- Legacy tagged set-level carrier used by earlier source compilers.
  -- NOT a linear direct sum: two linear summand zeroes cannot be disjoint.
  VnaturalCarrier : Set
  VnaturalCarrier =
    OrbifoldCarrier
      (LeechLatticeVOAInput.fixedPoint leechInput)
      (LeechLatticeVOAInput.canonicalTwistedModule leechInput)
      (LeechLatticeVOAInput.twistedEvenSector leechInput)

  -- Correct same-source finite vector-direct-sum carrier (pair shape).
  -- This is a carrier target only: an all-mode VOA equivalence to
  -- Vnatural must still be constructed from genuine mixed-sector laws.
  VnaturalLinearCarrier : Set
  VnaturalLinearCarrier =
    LinearOrbifoldCarrier
      (LeechLatticeVOAInput.fixedPoint leechInput)
      (LeechLatticeVOAInput.canonicalTwistedModule leechInput)
      (LeechLatticeVOAInput.twistedEvenSector leechInput)

  centralCharge24 : Set
  centralCharge24 = OrbifoldVOAAssembly.centralCharge24 orbifoldAssembly

  holomorphic : Set
  holomorphic = OrbifoldVOAAssembly.holomorphic orbifoldAssembly

  simple : Set
  simple = OrbifoldVOAAssembly.simple orbifoldAssembly

open VNaturalConstruction public

constructVNatural :
  (input : LeechLatticeVOAInput) →
  OrbifoldVOAAssembly
    (LeechLatticeVOAInput.fixedPoint input)
    (LeechLatticeVOAInput.canonicalTwistedModule input)
    (LeechLatticeVOAInput.twistedEvenSector input) →
  VNaturalConstruction
constructVNatural input assembly =
  record
    { leechInput = input
    ; orbifoldAssembly = assembly
    }


------------------------------------------------------------------------
-- Actual source-specific direct-summand embedding properties.
-- Unlike weight-two dimension accounting, these proofs identify the
-- original fixed/twisted inclusion maps of the SAME orbifold assembly.
------------------------------------------------------------------------

open import Data.Empty using (⊥)

cong : ∀ {A B : Set} (f : A → B) {x y : A} →
  x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} →
  x ≡ y → y ≡ z → x ≡ z
trans refl q = q

leftSumInjective : ∀ {A B : Set} {x y : A} →
  (inj₁ {B = B} x ≡ inj₁ y) → x ≡ y
leftSumInjective refl = refl

rightSumInjective : ∀ {A B : Set} {x y : B} →
  (inj₂ {A = A} x ≡ inj₂ y) → x ≡ y
rightSumInjective refl = refl

leftRightSumDistinct : ∀ {A B : Set} (x : A) (y : B) →
  inj₁ x ≡ inj₂ y → ⊥
leftRightSumDistinct x y ()

module ActualSelectedSummandInclusions
  (construction : VNaturalConstruction) where

  input : LeechLatticeVOAInput
  input = VNaturalConstruction.leechInput construction

  assembly :
    OrbifoldVOAAssembly
      (LeechLatticeVOAInput.fixedPoint input)
      (LeechLatticeVOAInput.canonicalTwistedModule input)
      (LeechLatticeVOAInput.twistedEvenSector input)
  assembly = VNaturalConstruction.orbifoldAssembly construction

  Fixed : Set
  Fixed = FixedPointVOA.fixedCarrier
    (LeechLatticeVOAInput.fixedPoint input)

  Twisted : Set
  Twisted = TwistedEvenSector.CarrierPlus
    (LeechLatticeVOAInput.twistedEvenSector input)

  originalFixedInclusionInjective : (x y : Fixed) →
    includeFixedSummand assembly x ≡ includeFixedSummand assembly y →
    x ≡ y
  originalFixedInclusionInjective x y eq =
    leftSumInjective
      (trans (sym (fixedSummandIdentifies assembly x))
        (trans (cong (identifyCarrier assembly) eq)
          (fixedSummandIdentifies assembly y)))

  originalTwistedInclusionInjective : (x y : Twisted) →
    includeTwistedSummand assembly x ≡ includeTwistedSummand assembly y →
    x ≡ y
  originalTwistedInclusionInjective x y eq =
    rightSumInjective
      (trans (sym (twistedSummandIdentifies assembly x))
        (trans (cong (identifyCarrier assembly) eq)
          (twistedSummandIdentifies assembly y)))

  originalFixedTwistedDisjoint : (x : Fixed) (y : Twisted) →
    includeFixedSummand assembly x ≡ includeTwistedSummand assembly y →
    ⊥
  originalFixedTwistedDisjoint x y eq =
    leftRightSumDistinct x y
      (trans (sym (fixedSummandIdentifies assembly x))
        (trans (cong (identifyCarrier assembly) eq)
          (twistedSummandIdentifies assembly y)))


  -- Original summands construct a section of the selected carrier
  -- identification. This proves that every tagged direct-sum state is
  -- realized by a selected orbifold state, without asserting that ALL
  -- selected states are in the image (that needs the reverse law).
  SelectedState : Set
  SelectedState =
    VOA.GradedModule.Carrier
      (VOA.VertexOperatorAlgebra.gradedModule
        (OrbifoldVOAAssembly.orbifoldVOA assembly))

  reconstructTaggedState : Fixed ⊎ Twisted → SelectedState
  reconstructTaggedState (inj₁ x) = includeFixedSummand assembly x
  reconstructTaggedState (inj₂ y) = includeTwistedSummand assembly y

  identifyAfterReconstruct :
    (s : Fixed ⊎ Twisted) →
    identifyCarrier assembly (reconstructTaggedState s) ≡ s
  identifyAfterReconstruct (inj₁ x) = fixedSummandIdentifies assembly x
  identifyAfterReconstruct (inj₂ y) = twistedSummandIdentifies assembly y

  reconstructTaggedStateInjective :
    (s t : Fixed ⊎ Twisted) →
    reconstructTaggedState s ≡ reconstructTaggedState t →
    s ≡ t
  reconstructTaggedStateInjective s t eq =
    trans (sym (identifyAfterReconstruct s))
      (trans (cong (identifyCarrier assembly) eq)
        (identifyAfterReconstruct t))


  ----------------------------------------------------------------------
  -- ORIGINAL SOURCE FIBRE NORMALISATION / EXACT V0 NO-JUNK EQUIVALENCE
  --
  -- A retraction from the selected weak VOA carrier to the ACTUAL
  -- orbifold tagged sum is already given by identifyAfterReconstruct.
  -- The canonical state normalizer is therefore an idempotent, and
  -- it distinguishes exactly the fibres of the original identify map.
  -- The missing opposite inverse is EQUIVALENT to identify injectivity:
  -- either one is an acceptable, source-specific V0 acceptance lemma.
  ----------------------------------------------------------------------

  normalizeSelectedState : SelectedState → SelectedState
  normalizeSelectedState w =
    reconstructTaggedState (identifyCarrier assembly w)

  identifyAfterNormalize : (w : SelectedState) →
    identifyCarrier assembly (normalizeSelectedState w)
    ≡ identifyCarrier assembly w
  identifyAfterNormalize w =
    identifyAfterReconstruct (identifyCarrier assembly w)

  normalizeSelectedStateIdempotent : (w : SelectedState) →
    normalizeSelectedState (normalizeSelectedState w)
    ≡ normalizeSelectedState w
  normalizeSelectedStateIdempotent w =
    cong reconstructTaggedState (identifyAfterNormalize w)

  reconstructedStatesAlreadyNormal : (s : Fixed ⊎ Twisted) →
    normalizeSelectedState (reconstructTaggedState s)
    ≡ reconstructTaggedState s
  reconstructedStatesAlreadyNormal s =
    cong reconstructTaggedState (identifyAfterReconstruct s)

  originalSameTagImpliesSameNormalization :
    (x y : SelectedState) →
    identifyCarrier assembly x ≡ identifyCarrier assembly y →
    normalizeSelectedState x ≡ normalizeSelectedState y
  originalSameTagImpliesSameNormalization x y eq =
    cong reconstructTaggedState eq

  sameNormalizationImpliesOriginalSameTag :
    (x y : SelectedState) →
    normalizeSelectedState x ≡ normalizeSelectedState y →
    identifyCarrier assembly x ≡ identifyCarrier assembly y
  sameNormalizationImpliesOriginalSameTag x y eq =
    trans (sym (identifyAfterNormalize x))
      (trans (cong (identifyCarrier assembly) eq)
        (identifyAfterNormalize y))

  -- The exact extra theorem needed for a bidirectional original
  -- selected-carrier identification is injectivity of identifyCarrier.
  -- Do NOT fill it with an arbitrary external Set label.
  NoExtraSelectedStates : Set
  NoExtraSelectedStates =
    (w : SelectedState) → normalizeSelectedState w ≡ w

  OriginalIdentificationInjective : Set
  OriginalIdentificationInjective =
    (x y : SelectedState) →
    identifyCarrier assembly x ≡ identifyCarrier assembly y →
    x ≡ y

  noExtraStatesFromOriginalIdentificationInjective :
    OriginalIdentificationInjective → NoExtraSelectedStates
  noExtraStatesFromOriginalIdentificationInjective injective w =
    injective (normalizeSelectedState w) w
      (identifyAfterNormalize w)

  originalIdentificationInjectiveFromNoExtraStates :
    NoExtraSelectedStates → OriginalIdentificationInjective
  originalIdentificationInjectiveFromNoExtraStates noExtra x y eq =
    trans (sym (noExtra x))
      (trans (cong reconstructTaggedState eq)
        (noExtra y))

  -- Exact two-way replacement for the outstanding V0 no-junk gate.
  -- Neither direction asserts that the needed source evidence exists.
  originalNoExtraStatesIffIdentificationInjective :
    (OriginalIdentificationInjective → NoExtraSelectedStates)
    × (NoExtraSelectedStates → OriginalIdentificationInjective)
  originalNoExtraStatesIffIdentificationInjective =
    noExtraStatesFromOriginalIdentificationInjective ,
    originalIdentificationInjectiveFromNoExtraStates


  ----------------------------------------------------------------------
  -- DECISIVE V0 NO-GO: A TAGGED COPRODUCT IS NOT A VECTOR DIRECT SUM.
  --
  -- A genuine linear embedding of both nonempty summand vector spaces
  -- into one VOA state space must send both zeros to the SAME zero.
  -- The original assembly's two tag-identification equations instead
  -- force disjoint summand images. Hence the old A ⊎ B shape cannot
  -- be promoted as the linear direct sum A ⊕ B with both embeddings
  -- linear. This is not a choice-of-normal-form or kernel issue.
  ----------------------------------------------------------------------

  originalLinearSummandZerosImpossible :
    (fixedZero : Fixed) (twistedZero : Twisted)
    (selectedZero : SelectedState) →
    includeFixedSummand assembly fixedZero ≡ selectedZero →
    includeTwistedSummand assembly twistedZero ≡ selectedZero →
    ⊥
  originalLinearSummandZerosImpossible fixedZero twistedZero
    selectedZero fixedPreservesZero twistedPreservesZero =
    originalFixedTwistedDisjoint fixedZero twistedZero
      (trans fixedPreservesZero (sym twistedPreservesZero))

  originalVOAZeroCannotBeBothSummandZeros :
    (fixedZero : Fixed) (twistedZero : Twisted) →
    includeFixedSummand assembly fixedZero
      ≡ VOA.GradedModule.zero
          (VOA.VertexOperatorAlgebra.gradedModule
            (OrbifoldVOAAssembly.orbifoldVOA assembly)) →
    includeTwistedSummand assembly twistedZero
      ≡ VOA.GradedModule.zero
          (VOA.VertexOperatorAlgebra.gradedModule
            (OrbifoldVOAAssembly.orbifoldVOA assembly)) →
    ⊥
  originalVOAZeroCannotBeBothSummandZeros fixedZero twistedZero
    fixedPreservesZero twistedPreservesZero =
    originalLinearSummandZerosImpossible fixedZero twistedZero
      (VOA.GradedModule.zero
        (VOA.VertexOperatorAlgebra.gradedModule
          (OrbifoldVOAAssembly.orbifoldVOA assembly)))
      fixedPreservesZero twistedPreservesZero


------------------------------------------------------------------------
-- V0.3: SAME-SOURCE GRADED PAIR CONSTRUCTION
--
-- The actual summand carriers are taken from the original selected
-- Leech-orbifold input. Operations and gradings on those carriers MUST
-- be supplied by the genuine original summand sources. This constructor
-- is not a proof of their linear/VOA laws. Unlike the legacy tagged
-- coproduct it does construct the exact paired GradedModule, with both
-- sectors represented at every grade.
------------------------------------------------------------------------

module SelectedPairedGradedModule
  (construction : VNaturalConstruction) where

  input : LeechLatticeVOAInput
  input = VNaturalConstruction.leechInput construction

  fixed : FixedPointVOA
      (LeechLatticeVOAInput.leechLatticeVOA input)
      (LeechLatticeVOAInput.leechInvolution input)
  fixed = LeechLatticeVOAInput.fixedPoint input

  twisted : TwistedModule
      (LeechLatticeVOAInput.leechLatticeVOA input)
      (LeechLatticeVOAInput.leechInvolution input)
  twisted = LeechLatticeVOAInput.canonicalTwistedModule input

  plus : TwistedEvenSector twisted
  plus = LeechLatticeVOAInput.twistedEvenSector input

  Fixed : Set
  Fixed = FixedPointVOA.fixedCarrier fixed

  Twisted : Set
  Twisted = TwistedEvenSector.CarrierPlus plus

  -- Scalar carrier of the actual source fixed-point VOA. The twisted
  -- sector must represent the same scalar action, not a second ring.
  fixedGM : VOA.GradedModule
  fixedGM =
    VOA.VertexOperatorAlgebra.gradedModule
      (FixedPointVOA.fixedVOA fixed)

  Scalar : Set
  Scalar = VOA.GradedModule.Scalar fixedGM

  record SourceSectorGrading : Setω where
    field
      fixedZero : Fixed
      twistedZero : Twisted
      fixedAdd : Fixed → Fixed → Fixed
      twistedAdd : Twisted → Twisted → Twisted
      fixedScale : Scalar → Fixed → Fixed
      twistedScale : Scalar → Twisted → Twisted
      fixedGrade : Nat → Set
      twistedGrade : Nat → Set
      fixedIncludeGrade : (n : Nat) →
        fixedGrade n → Fixed
      twistedIncludeGrade : (n : Nat) →
        twistedGrade n → Twisted

  open SourceSectorGrading public

  -- The original source dimensions are not replaced by a chosen
  -- numeric grade profile. The graded piece is literally their product.
  pairedGradedModule : SourceSectorGrading → VOA.GradedModule
  pairedGradedModule source = record
    { VOA.GradedModule.Scalar = Scalar
    ; VOA.GradedModule.Carrier =
        LinearOrbifoldCarrier fixed twisted plus
    ; VOA.GradedModule.gradePiece = λ n →
        fixedGrade source n × twistedGrade source n
    ; VOA.GradedModule.includeGrade = λ n p →
        fixedIncludeGrade source n (Data.Product.proj₁ p) ,
        twistedIncludeGrade source n (Data.Product.proj₂ p)
    ; VOA.GradedModule.zero =
        fixedZero source , twistedZero source
    ; VOA.GradedModule._+_ = λ x y →
        fixedAdd source (Data.Product.proj₁ x) (Data.Product.proj₁ y) ,
        twistedAdd source (Data.Product.proj₂ x) (Data.Product.proj₂ y)
    ; VOA.GradedModule._·_ = λ s x →
        fixedScale source s (Data.Product.proj₁ x) ,
        twistedScale source s (Data.Product.proj₂ x)
    }

  originalPairedZero :
    (source : SourceSectorGrading) →
    VOA.GradedModule.zero (pairedGradedModule source)
      ≡ (fixedZero source , twistedZero source)
  originalPairedZero source = refl

  originalPairedGradeInclusion :
    (source : SourceSectorGrading)
    (n : Nat)
    (x : fixedGrade source n)
    (y : twistedGrade source n) →
    VOA.GradedModule.includeGrade (pairedGradedModule source) n
      (x , y)
      ≡ (fixedIncludeGrade source n x ,
         twistedIncludeGrade source n y)
  originalPairedGradeInclusion source n x y = refl

  originalPairedAddition :
    (source : SourceSectorGrading)
    (x x' : Fixed) (y y' : Twisted) →
    VOA.GradedModule._+_ (pairedGradedModule source)
      (x , y) (x' , y')
      ≡ (fixedAdd source x x' , twistedAdd source y y')
  originalPairedAddition source x x' y y' = refl

  originalPairedScaling :
    (source : SourceSectorGrading)
    (s : Scalar) (x : Fixed) (y : Twisted) →
    VOA.GradedModule._·_ (pairedGradedModule source)
      s (x , y)
      ≡ (fixedScale source s x , twistedScale source s y)
  originalPairedScaling source s x y = refl

  -- Strong source-local exclusion of the previous, incorrect A ⊎ B:
  -- both canonical zero embeddings now coincide by definition.
  pairedOriginalZerosAgree :
    (source : SourceSectorGrading) →
    (fixedZero source , twistedZero source)
      ≡ (fixedZero source , twistedZero source)
  pairedOriginalZerosAgree source = refl


  ----------------------------------------------------------------------
  -- Stronger original-source producer: fixed-sector operations are NOT
  -- picked afresh. They are transported from fixedPoint.fixedVOA.
  -- Only the twisted-even sector has to supply still-missing native
  -- linear/graded operations plus the actual fixedCarrier equivalence.
  ----------------------------------------------------------------------

  FixedOriginalState : Set
  FixedOriginalState = VOA.GradedModule.Carrier fixedGM

  record OriginalFixedVOAAndTwistedEvenSource : Setω where
    field
      fixedToOriginal : Fixed → FixedOriginalState
      fixedFromOriginal : FixedOriginalState → Fixed
      fixedOriginalAfterFrom : (w : FixedOriginalState) →
        fixedToOriginal (fixedFromOriginal w) ≡ w
      fixedFromAfterOriginal : (w : Fixed) →
        fixedFromOriginal (fixedToOriginal w) ≡ w

      twistedZeroOriginal : Twisted
      twistedAddOriginal : Twisted → Twisted → Twisted
      twistedScaleOriginal : Scalar → Twisted → Twisted
      twistedGradeOriginal : Nat → Set
      twistedIncludeGradeOriginal :
        (n : Nat) → twistedGradeOriginal n → Twisted

  open OriginalFixedVOAAndTwistedEvenSource public

  nativeFixedAndTwistedGrading :
    OriginalFixedVOAAndTwistedEvenSource → SourceSectorGrading
  nativeFixedAndTwistedGrading source = record
    { fixedZero =
        fixedFromOriginal source (VOA.GradedModule.zero fixedGM)
    ; twistedZero = twistedZeroOriginal source
    ; fixedAdd = λ x y →
        fixedFromOriginal source
          (VOA.GradedModule._+_ fixedGM
            (fixedToOriginal source x) (fixedToOriginal source y))
    ; twistedAdd = twistedAddOriginal source
    ; fixedScale = λ s x →
        fixedFromOriginal source
          (VOA.GradedModule._·_ fixedGM s (fixedToOriginal source x))
    ; twistedScale = twistedScaleOriginal source
    ; fixedGrade = VOA.GradedModule.gradePiece fixedGM
    ; twistedGrade = twistedGradeOriginal source
    ; fixedIncludeGrade = λ n x →
        fixedFromOriginal source
          (VOA.GradedModule.includeGrade fixedGM n x)
    ; twistedIncludeGrade = twistedIncludeGradeOriginal source
    }

  originalFixedZeroDecoded :
    (source : OriginalFixedVOAAndTwistedEvenSource) →
    fixedToOriginal source
      (fixedZero (nativeFixedAndTwistedGrading source))
    ≡ VOA.GradedModule.zero fixedGM
  originalFixedZeroDecoded source =
    fixedOriginalAfterFrom source (VOA.GradedModule.zero fixedGM)

  originalFixedAdditionDecoded :
    (source : OriginalFixedVOAAndTwistedEvenSource)
    (x y : Fixed) →
    fixedToOriginal source
      (fixedAdd (nativeFixedAndTwistedGrading source) x y)
    ≡ VOA.GradedModule._+_ fixedGM
         (fixedToOriginal source x) (fixedToOriginal source y)
  originalFixedAdditionDecoded source x y =
    fixedOriginalAfterFrom source
      (VOA.GradedModule._+_ fixedGM
        (fixedToOriginal source x) (fixedToOriginal source y))

  originalFixedScalingDecoded :
    (source : OriginalFixedVOAAndTwistedEvenSource)
    (s : Scalar) (x : Fixed) →
    fixedToOriginal source
      (fixedScale (nativeFixedAndTwistedGrading source) s x)
    ≡ VOA.GradedModule._·_ fixedGM s (fixedToOriginal source x)
  originalFixedScalingDecoded source s x =
    fixedOriginalAfterFrom source
      (VOA.GradedModule._·_ fixedGM s (fixedToOriginal source x))

  originalFixedGradeDecoded :
    (source : OriginalFixedVOAAndTwistedEvenSource)
    (n : Nat) (x : VOA.GradedModule.gradePiece fixedGM n) →
    fixedToOriginal source
      (fixedIncludeGrade (nativeFixedAndTwistedGrading source) n x)
    ≡ VOA.GradedModule.includeGrade fixedGM n x
  originalFixedGradeDecoded source n x =
    fixedOriginalAfterFrom source
      (VOA.GradedModule.includeGrade fixedGM n x)

  actualSourceGradedPair :
    OriginalFixedVOAAndTwistedEvenSource → VOA.GradedModule
  actualSourceGradedPair source =
    pairedGradedModule (nativeFixedAndTwistedGrading source)


  ----------------------------------------------------------------------
  -- V0.4: ORIGINAL Z/2-PARITY FOUR-BLOCK MODE SOURCE
  --
  -- Fixed x fixed -> fixed is transported from the original fixedVOA.
  -- Fixed x twisted -> twisted is tied to the ORIGINAL Leech theta-
  -- twisted module via an explicit integer-index conversion and a
  -- source-equality proof. The opposite mixed and twisted x twisted
  -- operations remain genuine missing original FLM orbifold data.
  -- The formula expands (x+y)_(n)(u+v) into its four parity channels.
  -- This is NOT yet an all-mode VOA or a Jacobi/locality theorem.
  ----------------------------------------------------------------------

  FixedOriginalModes : Set
  FixedOriginalModes = FixedOriginalState

  originalFixedSectorMode :
    (source : OriginalFixedVOAAndTwistedEvenSource) →
    Fixed → ℤ → Fixed → Fixed
  originalFixedSectorMode source x k y =
    fixedFromOriginal source
      (VOA.VertexOperatorData.mode
        (VOA.VertexOperatorAlgebra.vertexData
          (FixedPointVOA.fixedVOA fixed))
        (fixedToOriginal source x) k (fixedToOriginal source y))

  originalFixedModeDecoded :
    (source : OriginalFixedVOAAndTwistedEvenSource)
    (x y : Fixed) (k : ℤ) →
    fixedToOriginal source (originalFixedSectorMode source x k y)
    ≡ VOA.VertexOperatorData.mode
        (VOA.VertexOperatorAlgebra.vertexData
          (FixedPointVOA.fixedVOA fixed))
        (fixedToOriginal source x) k (fixedToOriginal source y)
  originalFixedModeDecoded source x y k =
    fixedOriginalAfterFrom source
      (VOA.VertexOperatorData.mode
        (VOA.VertexOperatorAlgebra.vertexData
          (FixedPointVOA.fixedVOA fixed))
        (fixedToOriginal source x) k (fixedToOriginal source y))

  record OriginalMixedParitySource
    (source : OriginalFixedVOAAndTwistedEvenSource) : Setω where
    field
      integerTwistIndex :
        ℤ → TwistedModule.TwistIndex twisted

      -- Native original Leech twisted module's fixed-twisted mode.
      fixedTwistedMode :
        Fixed → ℤ → Twisted → Twisted

      fixedTwistedIsOriginal :
        (x : Fixed) (k : ℤ) (y : Twisted) →
        TwistedEvenSector.includePlus plus (fixedTwistedMode x k y)
        ≡ TwistedModule.twistedMode twisted
            (FixedPointVOA.includeFixed fixed x)
            (integerTwistIndex k)
            (TwistedEvenSector.includePlus plus y)

      -- Independent source laws needed by FLM cross/intertwining.
      twistedFixedMode :
        Twisted → ℤ → Fixed → Twisted
      twistedTwistedMode :
        Twisted → ℤ → Twisted → Fixed

  open OriginalMixedParitySource public

  originalParityPairMode :
    (source : OriginalFixedVOAAndTwistedEvenSource) →
    OriginalMixedParitySource source →
    (Fixed × Twisted) →
    ℤ →
    (Fixed × Twisted) →
    (Fixed × Twisted)
  originalParityPairMode source cross (x , y) k (u , v) =
    ( fixedAdd (nativeFixedAndTwistedGrading source)
        (originalFixedSectorMode source x k u)
        (twistedTwistedMode cross y k v)
    , twistedAdd (nativeFixedAndTwistedGrading source)
        (fixedTwistedMode cross x k v)
        (twistedFixedMode cross y k u)
    )

  -- Two parity projections of the SAME explicitly constructed mode.
  originalParityFixedOutput :
    (source : OriginalFixedVOAAndTwistedEvenSource)
    (cross : OriginalMixedParitySource source)
    (x u : Fixed) (y v : Twisted)
    (k : ℤ) →
    Data.Product.proj₁
      (originalParityPairMode source cross (x , y) k (u , v))
    ≡ fixedAdd (nativeFixedAndTwistedGrading source)
        (originalFixedSectorMode source x k u)
        (twistedTwistedMode cross y k v)
  originalParityFixedOutput source cross x u y v k = refl

  originalParityTwistedOutput :
    (source : OriginalFixedVOAAndTwistedEvenSource)
    (cross : OriginalMixedParitySource source)
    (x u : Fixed) (y v : Twisted)
    (k : ℤ) →
    Data.Product.proj₂
      (originalParityPairMode source cross (x , y) k (u , v))
    ≡ twistedAdd (nativeFixedAndTwistedGrading source)
        (fixedTwistedMode cross x k v)
        (twistedFixedMode cross y k u)
  originalParityTwistedOutput source cross x u y v k = refl


  ----------------------------------------------------------------------
  -- V0.4: ACTUAL PAIRED VERTEX-DATA PRODUCER (NOT YET A VOA).
  --
  -- Vacuum and conformal vectors come from the ORIGINAL fixedVOA
  -- using fixedFromOriginal. The twisted component of each is zero,
  -- as in the concrete Popov–Rastelli/FLM Vnat. Fixed translation is
  -- transported from the original fixedVOA; twisted translation must
  -- be provided by the true original even-twisted source. The mode is
  -- exactly the four-parity-block source constructed above.
  ----------------------------------------------------------------------

  record OriginalEvenTwistedTranslation
    (source : OriginalFixedVOAAndTwistedEvenSource) : Setω where
    field
      twistedTranslation : Twisted → Twisted
  open OriginalEvenTwistedTranslation public

  actualSourcePairedVertexData :
    (source : OriginalFixedVOAAndTwistedEvenSource) →
    OriginalMixedParitySource source →
    OriginalEvenTwistedTranslation source →
    VOA.VertexOperatorData (actualSourceGradedPair source)
  actualSourcePairedVertexData source cross time = record
    { VOA.VertexOperatorData.vacuum =
        ( fixedFromOriginal source
            (VOA.VertexOperatorData.vacuum
              (VOA.VertexOperatorAlgebra.vertexData
                (FixedPointVOA.fixedVOA fixed)))
        , twistedZeroOriginal source )
    ; VOA.VertexOperatorData.conformalVector =
        ( fixedFromOriginal source
            (VOA.VertexOperatorData.conformalVector
              (VOA.VertexOperatorAlgebra.vertexData
                (FixedPointVOA.fixedVOA fixed)))
        , twistedZeroOriginal source )
    ; VOA.VertexOperatorData.mode =
        originalParityPairMode source cross
    ; VOA.VertexOperatorData.translation = λ p →
        ( fixedFromOriginal source
            (VOA.VertexOperatorData.translation
              (VOA.VertexOperatorAlgebra.vertexData
                (FixedPointVOA.fixedVOA fixed))
              (fixedToOriginal source (Data.Product.proj₁ p)))
        , twistedTranslation time (Data.Product.proj₂ p) )
    }

  actualPairedVacuumDecoded :
    (source : OriginalFixedVOAAndTwistedEvenSource)
    (cross : OriginalMixedParitySource source)
    (time : OriginalEvenTwistedTranslation source) →
    fixedToOriginal source
      (Data.Product.proj₁
        (VOA.VertexOperatorData.vacuum
          (actualSourcePairedVertexData source cross time)))
    ≡ VOA.VertexOperatorData.vacuum
        (VOA.VertexOperatorAlgebra.vertexData
          (FixedPointVOA.fixedVOA fixed))
  actualPairedVacuumDecoded source cross time =
    fixedOriginalAfterFrom source
      (VOA.VertexOperatorData.vacuum
        (VOA.VertexOperatorAlgebra.vertexData
          (FixedPointVOA.fixedVOA fixed)))

  actualPairedConformalDecoded :
    (source : OriginalFixedVOAAndTwistedEvenSource)
    (cross : OriginalMixedParitySource source)
    (time : OriginalEvenTwistedTranslation source) →
    fixedToOriginal source
      (Data.Product.proj₁
        (VOA.VertexOperatorData.conformalVector
          (actualSourcePairedVertexData source cross time)))
    ≡ VOA.VertexOperatorData.conformalVector
        (VOA.VertexOperatorAlgebra.vertexData
          (FixedPointVOA.fixedVOA fixed))
  actualPairedConformalDecoded source cross time =
    fixedOriginalAfterFrom source
      (VOA.VertexOperatorData.conformalVector
        (VOA.VertexOperatorAlgebra.vertexData
          (FixedPointVOA.fixedVOA fixed)))

  actualPairedModeIsFourBlock :
    (source : OriginalFixedVOAAndTwistedEvenSource)
    (cross : OriginalMixedParitySource source)
    (time : OriginalEvenTwistedTranslation source)
    (p q : Fixed × Twisted) (k : ℤ) →
    VOA.VertexOperatorData.mode
      (actualSourcePairedVertexData source cross time) p k q
    ≡ originalParityPairMode source cross p k q
  actualPairedModeIsFourBlock source cross time p q k = refl
