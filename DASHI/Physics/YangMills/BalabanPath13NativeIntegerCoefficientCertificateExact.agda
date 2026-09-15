module DASHI.Physics.YangMills.BalabanPath13NativeIntegerCoefficientCertificateExact where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.BalabanPath13NativeIntegerCoefficientDataExact public
import DASHI.Physics.YangMills.BalabanIntegerTriangularQuadraticCertificateExact as QuadZ

------------------------------------------------------------------------
-- The 78 independent symmetric coefficients are paid as twelve triangular
-- rows: 12 diagonal cells plus 66 off-diagonal cells.  Every closed operation
-- is native Data.Integer arithmetic; there is no rational normalize/div/gcd.
------------------------------------------------------------------------

gap0 gap1 gap2 gap3 gap4 gap5 gap6 gap7 gap8 gap9 gap10 gap11 gap12 : QuadZ.TriQuadraticZ
gap0 = scaledGapTriZ
gap1 = QuadZ.tailOfZ gap0
gap2 = QuadZ.tailOfZ gap1
gap3 = QuadZ.tailOfZ gap2
gap4 = QuadZ.tailOfZ gap3
gap5 = QuadZ.tailOfZ gap4
gap6 = QuadZ.tailOfZ gap5
gap7 = QuadZ.tailOfZ gap6
gap8 = QuadZ.tailOfZ gap7
gap9 = QuadZ.tailOfZ gap8
gap10 = QuadZ.tailOfZ gap9
gap11 = QuadZ.tailOfZ gap10
gap12 = QuadZ.tailOfZ gap11

ldl0 ldl1 ldl2 ldl3 ldl4 ldl5 ldl6 ldl7 ldl8 ldl9 ldl10 ldl11 ldl12 : QuadZ.TriQuadraticZ
ldl0 = scaledLDLTriZ
ldl1 = QuadZ.tailOfZ ldl0
ldl2 = QuadZ.tailOfZ ldl1
ldl3 = QuadZ.tailOfZ ldl2
ldl4 = QuadZ.tailOfZ ldl3
ldl5 = QuadZ.tailOfZ ldl4
ldl6 = QuadZ.tailOfZ ldl5
ldl7 = QuadZ.tailOfZ ldl6
ldl8 = QuadZ.tailOfZ ldl7
ldl9 = QuadZ.tailOfZ ldl8
ldl10 = QuadZ.tailOfZ ldl9
ldl11 = QuadZ.tailOfZ ldl10
ldl12 = QuadZ.tailOfZ ldl11

row0Diag : QuadZ.diagOfZ gap0 ≡ QuadZ.diagOfZ ldl0
row0Diag = refl
row0Off : QuadZ.rowOfZ gap0 ≡ QuadZ.rowOfZ ldl0
row0Off = refl
row1Diag : QuadZ.diagOfZ gap1 ≡ QuadZ.diagOfZ ldl1
row1Diag = refl
row1Off : QuadZ.rowOfZ gap1 ≡ QuadZ.rowOfZ ldl1
row1Off = refl
row2Diag : QuadZ.diagOfZ gap2 ≡ QuadZ.diagOfZ ldl2
row2Diag = refl
row2Off : QuadZ.rowOfZ gap2 ≡ QuadZ.rowOfZ ldl2
row2Off = refl
row3Diag : QuadZ.diagOfZ gap3 ≡ QuadZ.diagOfZ ldl3
row3Diag = refl
row3Off : QuadZ.rowOfZ gap3 ≡ QuadZ.rowOfZ ldl3
row3Off = refl
row4Diag : QuadZ.diagOfZ gap4 ≡ QuadZ.diagOfZ ldl4
row4Diag = refl
row4Off : QuadZ.rowOfZ gap4 ≡ QuadZ.rowOfZ ldl4
row4Off = refl
row5Diag : QuadZ.diagOfZ gap5 ≡ QuadZ.diagOfZ ldl5
row5Diag = refl
row5Off : QuadZ.rowOfZ gap5 ≡ QuadZ.rowOfZ ldl5
row5Off = refl
row6Diag : QuadZ.diagOfZ gap6 ≡ QuadZ.diagOfZ ldl6
row6Diag = refl
row6Off : QuadZ.rowOfZ gap6 ≡ QuadZ.rowOfZ ldl6
row6Off = refl
row7Diag : QuadZ.diagOfZ gap7 ≡ QuadZ.diagOfZ ldl7
row7Diag = refl
row7Off : QuadZ.rowOfZ gap7 ≡ QuadZ.rowOfZ ldl7
row7Off = refl
row8Diag : QuadZ.diagOfZ gap8 ≡ QuadZ.diagOfZ ldl8
row8Diag = refl
row8Off : QuadZ.rowOfZ gap8 ≡ QuadZ.rowOfZ ldl8
row8Off = refl
row9Diag : QuadZ.diagOfZ gap9 ≡ QuadZ.diagOfZ ldl9
row9Diag = refl
row9Off : QuadZ.rowOfZ gap9 ≡ QuadZ.rowOfZ ldl9
row9Off = refl
row10Diag : QuadZ.diagOfZ gap10 ≡ QuadZ.diagOfZ ldl10
row10Diag = refl
row10Off : QuadZ.rowOfZ gap10 ≡ QuadZ.rowOfZ ldl10
row10Off = refl
row11Diag : QuadZ.diagOfZ gap11 ≡ QuadZ.diagOfZ ldl11
row11Diag = refl
row11Off : QuadZ.rowOfZ gap11 ≡ QuadZ.rowOfZ ldl11
row11Off = refl

row12 : gap12 ≡ ldl12
row12 = refl

row11 : gap11 ≡ ldl11
row11 = QuadZ.qconsCongZ row11Diag row11Off row12
row10 : gap10 ≡ ldl10
row10 = QuadZ.qconsCongZ row10Diag row10Off row11
row9 : gap9 ≡ ldl9
row9 = QuadZ.qconsCongZ row9Diag row9Off row10
row8 : gap8 ≡ ldl8
row8 = QuadZ.qconsCongZ row8Diag row8Off row9
row7 : gap7 ≡ ldl7
row7 = QuadZ.qconsCongZ row7Diag row7Off row8
row6 : gap6 ≡ ldl6
row6 = QuadZ.qconsCongZ row6Diag row6Off row7
row5 : gap5 ≡ ldl5
row5 = QuadZ.qconsCongZ row5Diag row5Off row6
row4 : gap4 ≡ ldl4
row4 = QuadZ.qconsCongZ row4Diag row4Off row5
row3 : gap3 ≡ ldl3
row3 = QuadZ.qconsCongZ row3Diag row3Off row4
row2 : gap2 ≡ ldl2
row2 = QuadZ.qconsCongZ row2Diag row2Off row3
row1 : gap1 ≡ ldl1
row1 = QuadZ.qconsCongZ row1Diag row1Off row2
row0 : gap0 ≡ ldl0
row0 = QuadZ.qconsCongZ row0Diag row0Off row1

scaledIntegerCoefficientCertificate : scaledGapTriZ ≡ scaledLDLTriZ
scaledIntegerCoefficientCertificate = row0
