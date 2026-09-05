module DASHI.Analysis.ChangeOfVariablesMeasureSourceAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BOUNDED SOURCE AUTHORITY FOR MULTIDIMENSIONAL CHANGE OF VARIABLES
--
-- SOURCE:
-- Encyclopedia of Mathematics, "Change of variables in an integral".
-- For a suitable diffeomorphism Phi, the transformed integral carries the
-- absolute Jacobian determinant |det D Phi|.  This source authority does not
-- identify a generic Euclidean theorem with the Casimir transverse measure.
------------------------------------------------------------------------

record ChangeOfVariablesMeasureSourceAuthority : Set where
  field
    sourceName : String
    sourceLocator : String
    diffeomorphismHypothesesStated : Set
    jacobianAbsoluteDeterminantAppears : Set
    transformedIntegralFormulaStated : Set
    sourceBackedOnly : Set
    reading : String

open ChangeOfVariablesMeasureSourceAuthority public

canonicalChangeOfVariablesAuthority : ChangeOfVariablesMeasureSourceAuthority
canonicalChangeOfVariablesAuthority = record
  { sourceName = "Encyclopedia of Mathematics: Change of variables in an integral"
  ; sourceLocator = "https://encyclopediaofmath.org/wiki/Change_of_variables_in_an_integral"
  ; diffeomorphismHypothesesStated = ⊤
  ; jacobianAbsoluteDeterminantAppears = ⊤
  ; transformedIntegralFormulaStated = ⊤
  ; sourceBackedOnly = ⊤
  ; reading = "The multidimensional substitution theorem with |det D Phi| is source-backed; applying it to the Casimir polar map and exact measure remains a separate same-object weld."
  }

data GenericChangeOfVariablesAutomaticallyClosesCasimirPolarMeasure : Set where

genericMeasureTheoremNeedsCasimirWeld :
  GenericChangeOfVariablesAutomaticallyClosesCasimirPolarMeasure → ⊥
genericMeasureTheoremNeedsCasimirWeld ()
