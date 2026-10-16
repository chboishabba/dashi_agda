module DASHI.Physics.CondensedMatter.MATBG2026PublicAcquisitionRouteValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.CondensedMatter.MATBG2026PublicAcquisitionRouteExact as A

xiao-pmc-route-observed : A.routeObserved A.xiaoPMCRoute ≡ true
xiao-pmc-route-observed = refl

xiao-nims-route-observed : A.routeObserved A.xiaoNIMSMDRRoute ≡ true
xiao-nims-route-observed = refl

zhang-publisher-route-observed : A.routeObserved A.zhangNaturePublisherRoute ≡ true
zhang-publisher-route-observed = refl

qtm-bytes-still-open : A.qtmExperimentalBytesPaid A.canonicalMATBGPublicAcquisitionBoundary ≡ false
qtm-bytes-still-open = refl

entropy-bytes-still-open : A.entropyExperimentalBytesPaid A.canonicalMATBGPublicAcquisitionBoundary ≡ false
entropy-bytes-still-open = refl

route-does-not-create-authority : A.publicRouteDoesNotCreateExperimentalAuthority A.canonicalMATBGPublicAcquisitionBoundary ≡ true
route-does-not-create-authority = refl
