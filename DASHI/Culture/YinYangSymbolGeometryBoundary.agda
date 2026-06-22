module DASHI.Culture.YinYangSymbolGeometryBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Candidate-only Cartesian / set-theoretic yin-yang symbol geometry.
--
-- This module records a thin symbolic geometry surface for a yin-yang
-- symbol centered at the origin with radius R.  The surface preserves
-- exact user-supplied equations and set definitions as string payloads
-- rather than trying to formalize real arithmetic in depth.
--
-- It is candidate-only and non-promoting.  It does not certify
-- metaphysical, empirical, spiritual, clinical, canonical, or doctrinal
-- authority.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data YinYangSymbolGeometryBoundaryStatus : Set where
  candidateOnlyGeometryBoundary :
    YinYangSymbolGeometryBoundaryStatus

data GeometryAuthorityKind : Set where
  empiricalAuthorityKind : GeometryAuthorityKind
  spiritualAuthorityKind : GeometryAuthorityKind
  mysticalAuthorityKind : GeometryAuthorityKind
  clinicalAuthorityKind : GeometryAuthorityKind
  metaphysicalAuthorityKind : GeometryAuthorityKind
  canonicalAuthorityKind : GeometryAuthorityKind
  promotedDoctrineKind : GeometryAuthorityKind

record YinYangGeometryAuthorityBits : Set where
  constructor yinYangGeometryAuthorityBits
  field
    empiricalAuthority : Bool
    spiritualAuthority : Bool
    mysticalAuthority : Bool
    clinicalAuthority : Bool
    metaphysicalAuthority : Bool
    canonicalAuthority : Bool
    promotedDoctrine : Bool
    candidateOnly : Bool
    promoted : Bool

open YinYangGeometryAuthorityBits public

canonicalYinYangGeometryAuthorityBits : YinYangGeometryAuthorityBits
canonicalYinYangGeometryAuthorityBits =
  yinYangGeometryAuthorityBits
    false
    false
    false
    false
    false
    false
    false
    true
    false

record YinYangGeometryAuthorityFailClosed : Set where
  constructor yinYangGeometryAuthorityFailClosed
  field
    empiricalAuthorityFalse :
      empiricalAuthority canonicalYinYangGeometryAuthorityBits ≡ false
    spiritualAuthorityFalse :
      spiritualAuthority canonicalYinYangGeometryAuthorityBits ≡ false
    mysticalAuthorityFalse :
      mysticalAuthority canonicalYinYangGeometryAuthorityBits ≡ false
    clinicalAuthorityFalse :
      clinicalAuthority canonicalYinYangGeometryAuthorityBits ≡ false
    metaphysicalAuthorityFalse :
      metaphysicalAuthority canonicalYinYangGeometryAuthorityBits ≡ false
    canonicalAuthorityFalse :
      canonicalAuthority canonicalYinYangGeometryAuthorityBits ≡ false
    promotedDoctrineFalse :
      promotedDoctrine canonicalYinYangGeometryAuthorityBits ≡ false
    candidateOnlyTrue :
      candidateOnly canonicalYinYangGeometryAuthorityBits ≡ true
    promotedFalse :
      promoted canonicalYinYangGeometryAuthorityBits ≡ false

canonicalYinYangGeometryAuthorityFailClosed :
  YinYangGeometryAuthorityFailClosed
canonicalYinYangGeometryAuthorityFailClosed =
  yinYangGeometryAuthorityFailClosed
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

blockedGeometryAuthorityKinds : List GeometryAuthorityKind
blockedGeometryAuthorityKinds =
  empiricalAuthorityKind
  ∷ spiritualAuthorityKind
  ∷ mysticalAuthorityKind
  ∷ clinicalAuthorityKind
  ∷ metaphysicalAuthorityKind
  ∷ canonicalAuthorityKind
  ∷ promotedDoctrineKind
  ∷ []

data ComponentEquationKind : Set where
  largeEnclosingCircleKind : ComponentEquationKind
  upperInnerCircleKind : ComponentEquationKind
  lowerInnerCircleKind : ComponentEquationKind
  upperEyeDotKind : ComponentEquationKind
  lowerEyeDotKind : ComponentEquationKind

data SetConstructionKind : Set where
  teardropAKind : SetConstructionKind
  teardropBKind : SetConstructionKind
  yangRegionKind : SetConstructionKind
  yinRegionKind : SetConstructionKind

data ParametricCurveKind : Set where
  upperSCurveKind : ParametricCurveKind
  lowerSCurveKind : ParametricCurveKind

record ComponentEquationRow : Set where
  constructor componentEquationRow
  field
    rowId : Nat
    equationKind : ComponentEquationKind
    symbolName : String
    equationPayload : String
    interpretation : String
    candidateOnly : Bool
    promoted : Bool
    authorityBits : YinYangGeometryAuthorityBits

open ComponentEquationRow public

record SetConstructionRow : Set where
  constructor setConstructionRow
  field
    rowId : Nat
    constructionKind : SetConstructionKind
    symbolName : String
    definitionPayload : String
    interpretation : String
    candidateOnly : Bool
    promoted : Bool
    authorityBits : YinYangGeometryAuthorityBits

open SetConstructionRow public

record ParametricCurveRow : Set where
  constructor parametricCurveRow
  field
    rowId : Nat
    curveKind : ParametricCurveKind
    symbolName : String
    parameterPayload : String
    curvePayload : String
    interpretation : String
    candidateOnly : Bool
    promoted : Bool
    authorityBits : YinYangGeometryAuthorityBits

open ParametricCurveRow public

record CandidateOnlyComponentEquationReceipt
  (row : ComponentEquationRow) : Set where
  constructor candidateOnlyComponentEquationReceipt
  field
    candidateOnlyTrue : candidateOnly row ≡ true
    promotedFalse : promoted row ≡ false

record CandidateOnlySetConstructionReceipt
  (row : SetConstructionRow) : Set where
  constructor candidateOnlySetConstructionReceipt
  field
    candidateOnlyTrue : candidateOnly row ≡ true
    promotedFalse : promoted row ≡ false

record CandidateOnlyParametricCurveReceipt
  (row : ParametricCurveRow) : Set where
  constructor candidateOnlyParametricCurveReceipt
  field
    candidateOnlyTrue : candidateOnly row ≡ true
    promotedFalse : promoted row ≡ false

mkComponentEquationRow :
  Nat →
  ComponentEquationKind →
  String →
  String →
  String →
  ComponentEquationRow
mkComponentEquationRow rowId equationKind symbolName equationPayload interpretation =
  componentEquationRow
    rowId
    equationKind
    symbolName
    equationPayload
    interpretation
    true
    false
    canonicalYinYangGeometryAuthorityBits

mkSetConstructionRow :
  Nat →
  SetConstructionKind →
  String →
  String →
  String →
  SetConstructionRow
mkSetConstructionRow rowId constructionKind symbolName definitionPayload interpretation =
  setConstructionRow
    rowId
    constructionKind
    symbolName
    definitionPayload
    interpretation
    true
    false
    canonicalYinYangGeometryAuthorityBits

mkParametricCurveRow :
  Nat →
  ParametricCurveKind →
  String →
  String →
  String →
  String →
  ParametricCurveRow
mkParametricCurveRow rowId curveKind symbolName parameterPayload curvePayload interpretation =
  parametricCurveRow
    rowId
    curveKind
    symbolName
    parameterPayload
    curvePayload
    interpretation
    true
    false
    canonicalYinYangGeometryAuthorityBits

canonicalLargeEnclosingCircleEquation : ComponentEquationRow
canonicalLargeEnclosingCircleEquation =
  mkComponentEquationRow
    (suc zero)
    largeEnclosingCircleKind
    "C0"
    "x^2 + y^2 <= R^2"
    "Large enclosing circle centered at the origin with radius R."

canonicalUpperInnerCircleEquation : ComponentEquationRow
canonicalUpperInnerCircleEquation =
  mkComponentEquationRow
    (suc (suc zero))
    upperInnerCircleKind
    "C1"
    "x^2 + (y - R/2)^2 <= (R/2)^2"
    "Upper inner circle centered at (0, R/2) with radius R/2."

canonicalLowerInnerCircleEquation : ComponentEquationRow
canonicalLowerInnerCircleEquation =
  mkComponentEquationRow
    (suc (suc (suc zero)))
    lowerInnerCircleKind
    "C2"
    "x^2 + (y + R/2)^2 <= (R/2)^2"
    "Lower inner circle centered at (0, -R/2) with radius R/2."

canonicalUpperEyeDotEquation : ComponentEquationRow
canonicalUpperEyeDotEquation =
  mkComponentEquationRow
    (suc (suc (suc (suc zero))))
    upperEyeDotKind
    "E1"
    "x^2 + (y - R/2)^2 <= (R/8)^2"
    "Upper eye dot centered at (0, R/2) with radius R/8."

canonicalLowerEyeDotEquation : ComponentEquationRow
canonicalLowerEyeDotEquation =
  mkComponentEquationRow
    (suc (suc (suc (suc (suc zero)))))
    lowerEyeDotKind
    "E2"
    "x^2 + (y + R/2)^2 <= (R/8)^2"
    "Lower eye dot centered at (0, -R/2) with radius R/8."

canonicalComponentEquations : List ComponentEquationRow
canonicalComponentEquations =
  canonicalLargeEnclosingCircleEquation
  ∷ canonicalUpperInnerCircleEquation
  ∷ canonicalLowerInnerCircleEquation
  ∷ canonicalUpperEyeDotEquation
  ∷ canonicalLowerEyeDotEquation
  ∷ []

componentEquationsAreCandidateOnly :
  List (CandidateOnlyComponentEquationReceipt canonicalLargeEnclosingCircleEquation)
componentEquationsAreCandidateOnly =
  candidateOnlyComponentEquationReceipt refl refl ∷ []

canonicalTeardropARow : SetConstructionRow
canonicalTeardropARow =
  mkSetConstructionRow
    (suc zero)
    teardropAKind
    "Teardrop_A"
    "(({ (x, y) in C0 | x >= 0 } union C1) \\ C2)"
    "Right half of the enclosing disk, union the upper inner circle, then subtract the lower inner circle."

canonicalTeardropBRow : SetConstructionRow
canonicalTeardropBRow =
  mkSetConstructionRow
    (suc (suc zero))
    teardropBKind
    "Teardrop_B"
    "(({ (x, y) in C0 | x < 0 } union C2) \\ C1)"
    "Left half of the enclosing disk, union the lower inner circle, then subtract the upper inner circle."

canonicalTeardropRows : List SetConstructionRow
canonicalTeardropRows =
  canonicalTeardropARow
  ∷ canonicalTeardropBRow
  ∷ []

canonicalYangRegionRow : SetConstructionRow
canonicalYangRegionRow =
  mkSetConstructionRow
    (suc (suc (suc zero)))
    yangRegionKind
    "Yang"
    "((Teardrop_A \\ E1) union E2)"
    "White region: teardrop A without the upper eye, together with the lower eye."

canonicalYinRegionRow : SetConstructionRow
canonicalYinRegionRow =
  mkSetConstructionRow
    (suc (suc (suc (suc zero))))
    yinRegionKind
    "Yin"
    "((Teardrop_B \\ E2) union E1)"
    "Black region: teardrop B without the lower eye, together with the upper eye."

canonicalRegionRows : List SetConstructionRow
canonicalRegionRows =
  canonicalYangRegionRow
  ∷ canonicalYinRegionRow
  ∷ []

canonicalUpperSCurveRow : ParametricCurveRow
canonicalUpperSCurveRow =
  mkParametricCurveRow
    (suc zero)
    upperSCurveKind
    "Upper_S_Curve"
    "theta in [0, pi]"
    "(x(theta), y(theta)) = ((R/2) * sin(theta), R/2 + (R/2) * cos(theta))"
    "Upper parametric S-curve arc separating the two regions."

canonicalLowerSCurveRow : ParametricCurveRow
canonicalLowerSCurveRow =
  mkParametricCurveRow
    (suc (suc zero))
    lowerSCurveKind
    "Lower_S_Curve"
    "theta in [0, pi]"
    "(x(theta), y(theta)) = (-(R/2) * sin(theta), -R/2 + (R/2) * cos(theta))"
    "Lower parametric S-curve arc separating the two regions."

canonicalParametricCurveRows : List ParametricCurveRow
canonicalParametricCurveRows =
  canonicalUpperSCurveRow
  ∷ canonicalLowerSCurveRow
  ∷ []

canonicalLargeEnclosingCircleEquationReceipt :
  CandidateOnlyComponentEquationReceipt canonicalLargeEnclosingCircleEquation
canonicalLargeEnclosingCircleEquationReceipt =
  candidateOnlyComponentEquationReceipt refl refl

canonicalUpperInnerCircleEquationReceipt :
  CandidateOnlyComponentEquationReceipt canonicalUpperInnerCircleEquation
canonicalUpperInnerCircleEquationReceipt =
  candidateOnlyComponentEquationReceipt refl refl

canonicalLowerInnerCircleEquationReceipt :
  CandidateOnlyComponentEquationReceipt canonicalLowerInnerCircleEquation
canonicalLowerInnerCircleEquationReceipt =
  candidateOnlyComponentEquationReceipt refl refl

canonicalUpperEyeDotEquationReceipt :
  CandidateOnlyComponentEquationReceipt canonicalUpperEyeDotEquation
canonicalUpperEyeDotEquationReceipt =
  candidateOnlyComponentEquationReceipt refl refl

canonicalLowerEyeDotEquationReceipt :
  CandidateOnlyComponentEquationReceipt canonicalLowerEyeDotEquation
canonicalLowerEyeDotEquationReceipt =
  candidateOnlyComponentEquationReceipt refl refl

canonicalTeardropARowReceipt :
  CandidateOnlySetConstructionReceipt canonicalTeardropARow
canonicalTeardropARowReceipt =
  candidateOnlySetConstructionReceipt refl refl

canonicalTeardropBRowReceipt :
  CandidateOnlySetConstructionReceipt canonicalTeardropBRow
canonicalTeardropBRowReceipt =
  candidateOnlySetConstructionReceipt refl refl

canonicalYangRegionRowReceipt :
  CandidateOnlySetConstructionReceipt canonicalYangRegionRow
canonicalYangRegionRowReceipt =
  candidateOnlySetConstructionReceipt refl refl

canonicalYinRegionRowReceipt :
  CandidateOnlySetConstructionReceipt canonicalYinRegionRow
canonicalYinRegionRowReceipt =
  candidateOnlySetConstructionReceipt refl refl

canonicalUpperSCurveRowReceipt :
  CandidateOnlyParametricCurveReceipt canonicalUpperSCurveRow
canonicalUpperSCurveRowReceipt =
  candidateOnlyParametricCurveReceipt refl refl

canonicalLowerSCurveRowReceipt :
  CandidateOnlyParametricCurveReceipt canonicalLowerSCurveRow
canonicalLowerSCurveRowReceipt =
  candidateOnlyParametricCurveReceipt refl refl

record YinYangSymbolGeometryBoundary : Set where
  constructor yinYangSymbolGeometryBoundary
  field
    boundaryStatus : YinYangSymbolGeometryBoundaryStatus
    componentEquations : List ComponentEquationRow
    teardropRows : List SetConstructionRow
    regionRows : List SetConstructionRow
    parametricCurveRows : List ParametricCurveRow
    authorityBits : YinYangGeometryAuthorityBits
    failClosed : YinYangGeometryAuthorityFailClosed
    boundaryInterpretation : String

open YinYangSymbolGeometryBoundary public

YinYangSymbolGeometryBoundaryReceipt : Set
YinYangSymbolGeometryBoundaryReceipt =
  YinYangSymbolGeometryBoundary

canonicalYinYangSymbolGeometryBoundary :
  YinYangSymbolGeometryBoundary
canonicalYinYangSymbolGeometryBoundary =
  yinYangSymbolGeometryBoundary
    candidateOnlyGeometryBoundary
    canonicalComponentEquations
    canonicalTeardropRows
    canonicalRegionRows
    canonicalParametricCurveRows
    canonicalYinYangGeometryAuthorityBits
    canonicalYinYangGeometryAuthorityFailClosed
    "Candidate-only Cartesian and set-theoretic geometry boundary for the yin-yang symbol."

canonicalYinYangSymbolGeometryBoundaryReceipt :
  YinYangSymbolGeometryBoundaryReceipt
canonicalYinYangSymbolGeometryBoundaryReceipt =
  canonicalYinYangSymbolGeometryBoundary

canonicalComponentEquationCountIs5 :
  listCount canonicalComponentEquations ≡ suc (suc (suc (suc (suc zero))))
canonicalComponentEquationCountIs5 =
  refl

canonicalTeardropRowCountIs2 :
  listCount canonicalTeardropRows ≡ suc (suc zero)
canonicalTeardropRowCountIs2 =
  refl

canonicalRegionRowCountIs2 :
  listCount canonicalRegionRows ≡ suc (suc zero)
canonicalRegionRowCountIs2 =
  refl

canonicalParametricCurveRowCountIs2 :
  listCount canonicalParametricCurveRows ≡ suc (suc zero)
canonicalParametricCurveRowCountIs2 =
  refl

boundaryPolicySummary : String
boundaryPolicySummary =
  "Symbol geometry is preserved as candidate-only formal payload with blocked authority and theorem-thin string equations."
