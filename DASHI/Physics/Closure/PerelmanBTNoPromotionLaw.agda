module DASHI.Physics.Closure.PerelmanBTNoPromotionLaw where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.PerelmanBTGeometrizationAnalogueIndex as Index
import DASHI.Physics.Closure.PerelmanRicciFlowAndGeometrizationBoundaryReceipt as Boundary
import DASHI.Physics.Closure.SurgeryCanonicalNeighborhoodObligationLadder as Ladder
import DASHI.Physics.Closure.GeometryJSJAnalogueCrosswalk as Crosswalk
import DASHI.Physics.Closure.BTGaussianReducedVolumeSurface as Gaussian
import DASHI.Physics.Closure.BTCanonicalNeckAnalogue as Neck
import DASHI.Physics.Closure.GeometryAnalogueClassification as Geometry
import DASHI.Physics.Closure.SurgeryCanonicalNeighborhoodObstruction as Surgery

------------------------------------------------------------------------
-- No-promotion law for the Perelman/BT/geometrization analogue stack.
--
-- This module is a fail-closed aggregate over existing receipts.  It records
-- the exact places where the analogue stack has discrete BT/bookkeeping
-- witnesses but does not promote them to smooth Ricci-flow, Perelman
-- monotonicity, surgery, JSJ, geometrization, or Clay authority.

listLength : {A : Set} → List A → Nat
listLength [] =
  0
listLength (_ ∷ xs) =
  suc (listLength xs)

data NoPromotionReason : Set where
  noRicciFlowWitness :
    NoPromotionReason

  noPerelmanMonotonicityWitness :
    NoPromotionReason

  noSmoothS2NeckWitness :
    NoPromotionReason

  noSurgeryContinuationWitness :
    NoPromotionReason

  noJSJTheoremWitness :
    NoPromotionReason

  noGeometrizationWitness :
    NoPromotionReason

  noClayPromotionWitness :
    NoPromotionReason

reasonLabel : NoPromotionReason → String
reasonLabel noRicciFlowWitness =
  "No smooth Ricci-flow witness is present in the BT analogue stack"
reasonLabel noPerelmanMonotonicityWitness =
  "No Perelman monotonicity witness is promoted by the Gaussian BT surface"
reasonLabel noSmoothS2NeckWitness =
  "No smooth S2 epsilon-neck witness is promoted by the finite BT neck rows"
reasonLabel noSurgeryContinuationWitness =
  "No surgery continuation witness is discharged by the obligation ladder"
reasonLabel noJSJTheoremWitness =
  "No JSJ theorem witness is available in the geometry/JSJ crosswalk"
reasonLabel noGeometrizationWitness =
  "No Thurston geometrization witness is available in the analogue index"
reasonLabel noClayPromotionWitness =
  "No Clay promotion witness is available from the analogue stack"

record NoPromotionReasonRow : Set where
  constructor noPromotionReasonRow
  field
    reason :
      NoPromotionReason

    label :
      String

    labelIsCanonical :
      label ≡ reasonLabel reason

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

open NoPromotionReasonRow public

mkNoPromotionReasonRow :
  NoPromotionReason →
  NoPromotionReasonRow
mkNoPromotionReasonRow reason =
  noPromotionReasonRow
    reason
    (reasonLabel reason)
    refl
    false
    refl

canonicalNoPromotionReasons :
  List NoPromotionReasonRow
canonicalNoPromotionReasons =
  mkNoPromotionReasonRow noRicciFlowWitness
  ∷ mkNoPromotionReasonRow noPerelmanMonotonicityWitness
  ∷ mkNoPromotionReasonRow noSmoothS2NeckWitness
  ∷ mkNoPromotionReasonRow noSurgeryContinuationWitness
  ∷ mkNoPromotionReasonRow noJSJTheoremWitness
  ∷ mkNoPromotionReasonRow noGeometrizationWitness
  ∷ mkNoPromotionReasonRow noClayPromotionWitness
  ∷ []

noPromotionReasonCount : Nat
noPromotionReasonCount =
  listLength canonicalNoPromotionReasons

noPromotionReasonCountIs7 :
  noPromotionReasonCount ≡ 7
noPromotionReasonCountIs7 =
  refl

record PerelmanBTFalseWitnesses : Setω where
  constructor perelmanBTFalseWitnesses
  field
    analogueIndex :
      Index.PerelmanBTGeometrizationAnalogueIndex

    boundaryReceipt :
      Boundary.PerelmanRicciFlowAndGeometrizationBoundaryReceipt

    surgeryLadder :
      List Ladder.SurgeryObligationLadderRow

    geometryJSJCrosswalk :
      Crosswalk.GeometryJSJAnalogueCrosswalkMatrix

    gaussianSurface :
      Gaussian.BTGaussianReducedVolumeSurface

    noPromotionReasons :
      List NoPromotionReasonRow
    noPromotionReasonsAreCanonical :
      noPromotionReasons ≡ canonicalNoPromotionReasons
    noPromotionReasonCountField :
      Nat
    noPromotionReasonCountFieldIs7 :
      noPromotionReasonCountField ≡ 7
    noPromotionReasonCountMatchesRows :
      noPromotionReasonCountField ≡ listLength noPromotionReasons

    ricciFlowFalse :
      Gaussian.ricciFlowPostulated ≡ false
    boundaryRicciFlowSocketFalse :
      Boundary.authorityAvailable
        (Boundary.smoothRicciFlowExistenceUniquenessSocket boundaryReceipt)
      ≡
      false

    perelmanMonotonicityFalse :
      Gaussian.monotonicityPromoted ≡ false
    gaussianSurfaceMonotonicityFailClosed :
      Gaussian.monotonicityProofStatus gaussianSurface
      ≡
      Gaussian.monotonicityNotProvedForBTGaussianSurface

    smoothS2NeckFalse :
      Neck.smoothS2CrossSectionPromoted (Index.p2Neck analogueIndex)
      ≡
      false
    ladderBTSmoothS2NeckFalse :
      Ladder.smoothS2CrossSectionDischarged
        Ladder.canonicalBTNeckSurgeryObligationRow
      ≡
      false

    surgeryContinuationFalse :
      Surgery.surgeryContinuationAvailable
        (Index.surgeryObstruction analogueIndex)
      ≡
      false
    ladderSurgeryContinuationFalse :
      Ladder.surgeryContinuationAvailable Ladder.oneMinusCanonicalRow
      ≡
      false

    jsjTheoremFalse :
      Crosswalk.jsjTheoremAvailableHere ≡ false
    crosswalkJSJTheoremFalse :
      Crosswalk.jsjTheoremAvailableHere ≡ false

    geometrizationFalse :
      Geometry.geometrizationPromoted
        (Index.geometryClassification analogueIndex)
      ≡
      false
    boundaryThurstonGeometrizationSocketFalse :
      Boundary.authorityAvailable
        (Boundary.thurstonGeometrizationSocket boundaryReceipt)
      ≡
      false

    clayPromotionFalse :
      Gaussian.clayClaimPromoted ≡ false
    indexClayBlockerCount :
      Index.smoothAuthorityBlockerCountField analogueIndex ≡ 9

open PerelmanBTFalseWitnesses public

canonicalPerelmanBTFalseWitnesses :
  PerelmanBTFalseWitnesses
canonicalPerelmanBTFalseWitnesses =
  perelmanBTFalseWitnesses
    Index.canonicalPerelmanBTGeometrizationAnalogueIndex
    Boundary.canonicalPerelmanRicciFlowAndGeometrizationBoundaryReceipt
    Ladder.canonicalSurgeryObligationLadder
    Crosswalk.canonicalGeometryJSJAnalogueCrosswalkMatrix
    Gaussian.canonicalBTGaussianReducedVolumeSurface
    canonicalNoPromotionReasons
    refl
    noPromotionReasonCount
    noPromotionReasonCountIs7
    refl
    Gaussian.ricciFlowPostulatedIsFalse
    refl
    Gaussian.monotonicityPromotedIsFalse
    Gaussian.canonicalSurfaceMonotonicityFailClosed
    (Index.smoothS2CrossSectionsPromotedFalse
      Index.canonicalPerelmanBTGeometrizationAnalogueIndex)
    refl
    (Index.surgeryContinuationFalse
      Index.canonicalPerelmanBTGeometrizationAnalogueIndex)
    refl
    Crosswalk.jsjTheoremAvailableHereIsFalse
    (Crosswalk.jsjTheoremAvailableFalseField
      Crosswalk.canonicalGeometryJSJAnalogueCrosswalkMatrix)
    (Index.geometryClassificationGeometrizationFalse
      Index.canonicalPerelmanBTGeometrizationAnalogueIndex)
    refl
    Gaussian.clayClaimPromotedIsFalse
    refl

organizationString : String
organizationString =
  "O: No-promotion law for the Perelman/BT/geometrization analogue stack."

requirementString : String
requirementString =
  "R: Collect false witnesses for Ricci flow, Perelman monotonicity, smooth S2 neck, surgery continuation, JSJ theorem, geometrization, and Clay promotion."

codeArtifactString : String
codeArtifactString =
  "C: DASHI.Physics.Closure.PerelmanBTNoPromotionLaw imports the analogue index, boundary receipt, surgery ladder, geometry/JSJ crosswalk, and Gaussian surface."

stateString : String
stateString =
  "S: The stack has discrete BT analogue receipts; every smooth promotion reason remains false."

latticeString : String
latticeString =
  "L: Gaussian fail-closed flags -> BT neck false S2 promotion -> surgery ladder false continuation -> JSJ/geometrization sockets -> Clay blocker."

proposalString : String
proposalString =
  "P: Downstream modules should consume the analogue stack through these no-promotion rows when checking authority boundaries."

governanceString : String
governanceString =
  "G: Canonical reason rows and refl false witnesses prevent accidental promotion across the smooth theorem boundary."

gapString : String
gapString =
  "F: External smooth Ricci-flow, Perelman monotonicity, S2 neck, surgery, JSJ, geometrization, and Clay authority remain missing."

record PerelmanBTNoPromotionLawORCSLPGF : Set where
  constructor perelmanBTNoPromotionLawORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ gapString

open PerelmanBTNoPromotionLawORCSLPGF public

canonicalORCSLPGF :
  PerelmanBTNoPromotionLawORCSLPGF
canonicalORCSLPGF =
  perelmanBTNoPromotionLawORCSLPGF
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    gapString
    refl

record PerelmanBTNoPromotionLaw : Setω where
  constructor perelmanBTNoPromotionLaw
  field
    falseWitnesses :
      PerelmanBTFalseWitnesses

    orcslpgf :
      PerelmanBTNoPromotionLawORCSLPGF

    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalORCSLPGF

open PerelmanBTNoPromotionLaw public

canonicalPerelmanBTNoPromotionLaw :
  PerelmanBTNoPromotionLaw
canonicalPerelmanBTNoPromotionLaw =
  perelmanBTNoPromotionLaw
    canonicalPerelmanBTFalseWitnesses
    canonicalORCSLPGF
    refl
