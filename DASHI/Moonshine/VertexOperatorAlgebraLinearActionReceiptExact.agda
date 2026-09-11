module DASHI.Moonshine.VertexOperatorAlgebraLinearActionReceiptExact where

------------------------------------------------------------------------
-- SOURCE-BACKED LINEARITY RECEIPT FOR THE OLD LITERAL VOA CARRIER
--
-- In the standard definition, a VOA is a vector space and a VOA automorphism
-- is an invertible LINEAR map preserving the vacuum, conformal vector and
-- vertex operation.  `VertexOperatorAlgebraCore` intentionally kept only the
-- raw carrier operations and a literal group action, with `preservesModes :
-- Set` opaque.  That older API is excellent for same-object action recovery,
-- but it cannot itself prove the vector-space laws or linearity needed by the
-- Monster 3B multiplicity/Hom-space lane.
--
-- This owner does not replace the old carrier and does not introduce a second
-- Monster state space.  It attaches proof-bearing vector/module laws and
-- action-linearity receipts to the SAME `GradedModule` / `VOAGroupAction`.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA

------------------------------------------------------------------------
-- 1. Vector/module laws on the existing literal GradedModule carrier.
--
-- The old Scalar field carries no field operations, so this receipt names only
-- the scalar operations actually needed for vector-space reasoning here.
------------------------------------------------------------------------

record GradedModuleVectorSpaceReceipt (moduleCarrier : VOA.GradedModule) : Setω where
  field
    scalarZero scalarOne : VOA.GradedModule.Scalar moduleCarrier
    scalarAdd scalarMul :
      VOA.GradedModule.Scalar moduleCarrier →
      VOA.GradedModule.Scalar moduleCarrier →
      VOA.GradedModule.Scalar moduleCarrier

    zeroAdditiveIdentity :
      (v : VOA.GradedModule.Carrier moduleCarrier) →
      VOA.GradedModule._+_ moduleCarrier (VOA.GradedModule.zero moduleCarrier) v ≡ v

    additionAssociative :
      (u v w : VOA.GradedModule.Carrier moduleCarrier) →
      VOA.GradedModule._+_ moduleCarrier
        (VOA.GradedModule._+_ moduleCarrier u v) w
      ≡ VOA.GradedModule._+_ moduleCarrier
          u (VOA.GradedModule._+_ moduleCarrier v w)

    scalarDistributesAddition :
      (a : VOA.GradedModule.Scalar moduleCarrier) →
      (u v : VOA.GradedModule.Carrier moduleCarrier) →
      VOA.GradedModule._·_ moduleCarrier a
        (VOA.GradedModule._+_ moduleCarrier u v)
      ≡ VOA.GradedModule._+_ moduleCarrier
          (VOA.GradedModule._·_ moduleCarrier a u)
          (VOA.GradedModule._·_ moduleCarrier a v)

    scalarAssociative :
      (a b : VOA.GradedModule.Scalar moduleCarrier) →
      (v : VOA.GradedModule.Carrier moduleCarrier) →
      VOA.GradedModule._·_ moduleCarrier (scalarMul a b) v
      ≡ VOA.GradedModule._·_ moduleCarrier a
          (VOA.GradedModule._·_ moduleCarrier b v)

    scalarOneIdentity :
      (v : VOA.GradedModule.Carrier moduleCarrier) →
      VOA.GradedModule._·_ moduleCarrier scalarOne v ≡ v

open GradedModuleVectorSpaceReceipt public

------------------------------------------------------------------------
-- 2. Linearity of the existing literal VOA group action.
------------------------------------------------------------------------

record VOAGroupActionLinearReceipt
    {G : Set}
    (group : GR.Group G)
    (voa : VOA.VertexOperatorAlgebra)
    (action : VOA.VOAGroupAction G group voa) : Setω where
  field
    moduleCarrier : VOA.GradedModule
    moduleCarrierIsVOAModule : moduleCarrier ≡ VOA.gradedModule voa
    vectorSpaceReceipt : GradedModuleVectorSpaceReceipt moduleCarrier

    actionPreservesZero :
      (g : G) →
      VOA.VOAGroupAction.act action g (VOA.GradedModule.zero moduleCarrier)
      ≡ VOA.GradedModule.zero moduleCarrier

    actionPreservesAddition :
      (g : G) →
      (u v : VOA.GradedModule.Carrier moduleCarrier) →
      VOA.VOAGroupAction.act action g
        (VOA.GradedModule._+_ moduleCarrier u v)
      ≡ VOA.GradedModule._+_ moduleCarrier
          (VOA.VOAGroupAction.act action g u)
          (VOA.VOAGroupAction.act action g v)

    actionPreservesScaling :
      (g : G) →
      (a : VOA.GradedModule.Scalar moduleCarrier) →
      (v : VOA.GradedModule.Carrier moduleCarrier) →
      VOA.VOAGroupAction.act action g
        (VOA.GradedModule._·_ moduleCarrier a v)
      ≡ VOA.GradedModule._·_ moduleCarrier a
          (VOA.VOAGroupAction.act action g v)

open VOAGroupActionLinearReceipt public

------------------------------------------------------------------------
-- 3. Primary/source attribution.
------------------------------------------------------------------------

kac : Attribution.AttributedSource
kac = Attribution.mkNoDOISource
  "Victor G. Kac"
  "Vertex Algebras for Beginners, second edition"
  "American Mathematical Society, University Lecture Series 10"
  "1998"
  "https://bookstore.ams.org/ulect-10-r"
  Attribution.academicArticleSource
  "standard source calibration that a VOA is a vector space and its structure maps are linear where required; no DOI asserted for the book"
  Attribution.publicAttribution

borcherds : Attribution.AttributedSource
borcherds = Attribution.mkDOISource
  "Richard E. Borcherds"
  "Monstrous moonshine and monstrous Lie superalgebras"
  "Inventiones Mathematicae 109, 405-444"
  "1992"
  "10.1007/BF01232032"
  "https://doi.org/10.1007/BF01232032"
  Attribution.academicArticleSource
  "primary moonshine/VOA representation context"
  Attribution.publicAttribution

serre : Attribution.AttributedSource
serre = Attribution.mkDOISource
  "Jean-Pierre Serre"
  "Linear Representations of Finite Groups"
  "Springer"
  "1977"
  "10.1007/978-1-4684-9458-7"
  "https://doi.org/10.1007/978-1-4684-9458-7"
  Attribution.academicArticleSource
  "linear-representation calibration for group actions by linear automorphisms"
  Attribution.publicAttribution

kacAttribution = Snowball.canonicalSourceRoleSnowballReceipt kac
borcherdsAttribution = Snowball.canonicalSourceRoleSnowballReceipt borcherds
serreAttribution = Snowball.canonicalSourceRoleSnowballReceipt serre

------------------------------------------------------------------------
-- 4. Source-definition status and WrongType firewalls.
------------------------------------------------------------------------

voaAutomorphismLinearityIsSourceDefinition : Bool
voaAutomorphismLinearityIsSourceDefinition = true

data OpaquePreservesModesCreatesLinearity : Set where
data LiteralActionCreatesVectorSpaceLaws : Set where
data TraceCreatesLinearity : Set where
data QidCreatesLinearity : Set where
data DeweyCreatesLinearity : Set where
data OeisCreatesLinearity : Set where

opaquePreservesModesDoesNotCreateLinearity :
  OpaquePreservesModesCreatesLinearity → ⊥
opaquePreservesModesDoesNotCreateLinearity ()

literalActionDoesNotCreateVectorSpaceLaws :
  LiteralActionCreatesVectorSpaceLaws → ⊥
literalActionDoesNotCreateVectorSpaceLaws ()

traceDoesNotCreateLinearity : TraceCreatesLinearity → ⊥
traceDoesNotCreateLinearity ()

qidDoesNotCreateLinearity : QidCreatesLinearity → ⊥
qidDoesNotCreateLinearity ()

deweyDoesNotCreateLinearity : DeweyCreatesLinearity → ⊥
deweyDoesNotCreateLinearity ()

oeisDoesNotCreateLinearity : OeisCreatesLinearity → ⊥
oeisDoesNotCreateLinearity ()

------------------------------------------------------------------------
-- 5. Classification coordinates remain navigation only.
------------------------------------------------------------------------

groupRepresentationQid : String
groupRepresentationQid = "Q1055807"

representationCharacterQid : String
representationCharacterQid = "Q600043"

groupRepresentationDewey : String
groupRepresentationDewey = "512.22"

finiteGroupDewey : String
finiteGroupDewey = "512.23"

oeisRole : String
oeisRole = "not applicable: vector-space laws and action linearity are structural receipts, not integer-sequence evidence"

------------------------------------------------------------------------
-- 6. Boundary: the generic receipt is available; no actual Monster inhabitant
--    is manufactured here.
------------------------------------------------------------------------

record VOAActionLinearReceiptBoundary : Set where
  constructor voa-action-linear-receipt-boundary
  field
    oldLiteralCarrierOperationsAlreadyOwned : Bool
    standardVOADefinitionRequiresLinearity : Bool
    explicitVectorSpaceLawsNowTyped : Bool
    explicitActionLinearityNowTyped : Bool
    actualMonsterVOALinearityReceiptInhabitedHere : Bool
open VOAActionLinearReceiptBoundary public

canonicalVOAActionLinearReceiptBoundary : VOAActionLinearReceiptBoundary
canonicalVOAActionLinearReceiptBoundary =
  voa-action-linear-receipt-boundary true true true true false
