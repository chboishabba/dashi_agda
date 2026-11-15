# NS R854: sharpen ORIGINAL R850/R853 short-time integrated scalar

**Selected original source:** R828 real Fourier finite-mode witness,
R829/R850 exact t=0 selected rate, R853 general original selected
rate normal form, R830 exact horizon and coarse bound.

NOT a Navier–Stokes singularity or a proof of B global regularity.

The original R850 source evaluates

  rate(0) = r0 = -28273644/125.

The R828 real finite Galerkin analysis supplies conservative
rate Lipschitz constant L=391309593930357307785216 and time

  T = 226189/3938540454339300631433585885184 > 0.

If a real finite Galerkin trajectory is constructed with the
literal R853 same-object selected signed rate and the actual
time-bound |rate(t)-r0| <= L t, then for every t in [0,T]

  rate(t) <= r0 + L t <= r0 + L T
          = -284574877153831/1258128000
          < -226189/2 < 0.

Its signed integral thus obeys the STRICTER exact envelope

  I(T) <= r0*T + (L*T²)/2
       = -128735420172278725243
           /9910376049473991249648549085109551104000
       < (-226189/2)*T < 0.

R830 previously source-wrote only the coarser constant upper
bound (-226189/2)*T. R854 replaces no genuine analytic ingredient:
it pays the stronger affine scalar arithmetic and exposes the
actual time-Lipschitz producer still required.

Original field issue: R408 is rational-field-specialized,
whereas a nonconstant REAL ODE trajectory cannot be a continuous
map into Q at all real times. A literal R408 integral transport
needs real-scalar reification or a two-stage selected-snapshot
to real-Galerkin same-object theorem. Do not cast a rational field
of modes into a real-time curve and claim the missing theorem.

New source:
  DASHI/Physics/Closure/
    NSTriadKNR650Rational345LipschitzIntegralRound854Exact.agda
Regression:
  python3 scripts/check_ns_r854_original_affine_integrated_rate_exact.py
Golden local:
  bash scripts/check_ns_r854_affine_integral_local.sh

Negative control: initial negativity alone is not sufficient.
The affine function r(t)=r0+4|r0|t/T has r(0)<0 but strictly
POSITIVE integral on [0,T]. The actual global Lipschitz estimate
is essential.

Status: exact rational arithmetic mathematical/calculationally
verified. The source-written Agda Round854 file is not yet
Agda 2.9 kernel accepted. The real trajectory, its selected
Lipschitz estimate, and the R408/R853 integral identity remain
the decisive mathematical gates. R823 auxiliary reserve
obstruction is NOT an NS Clay singularity.
