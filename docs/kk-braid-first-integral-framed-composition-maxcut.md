# KK magnetic first integral and framed winding semidirect cut

## KK: solve the reduced Maxwell constraint, not simply test a field profile
Given the assumed Jordan-frame KK reduction
S4 proportional to integral sqrt(-g) [phi R4 - kappa² phi³ F²/4],
and the fixed local ansatz A_y=a(x), phi=phi(x), flat coordinate metric,
the source-free Maxwell equation is d_x(phi³ a')=0.
Thus phi³ a'=Q, hence a'=Q/phi³, F²=2Q²/phi⁶.
The radion equation R4=3 kappa² phi² F²/4 then requires
R4=3 kappa² Q²/(2phi⁴).
The flat background has R4=0, so a nonzero Q cannot solve both equations on it.
This identifies the **necessary gravitational backreaction** and is not yet a
self-consistent nonflat Einstein/radion solution.
Exact symbolic script: scripts/check_kk_maxwell_first_integral_radion_source.py.

## Braid: close the conditional algebraic semidirect group step
DASHI/Foundations/C3O2SignedWindingCompositionExact.agda extends the signed
winding/parity transport with an additive associativity witness and a
source-written composition-associativity proof. There is no assumed specific
physical correspondence between spatial x-reflection and internal KK fibre
inversion; a geometric O(2) connection with checked transition functions
remains a separate obligation.

## Highest-priority analytic residuals
1. Solve Einstein + Maxwell + scalar simultaneously in a genuinely curved base;
   verify 5D Einstein equations, asymptotics and source requirements.
2. Derive full KK curvature tensor for arbitrary g4, A, phi from geometric data.
3. Construct smooth continuous framed strands with theta lift and pants gluing.
4. Prove C3/braid/O2 action commutes with an identified physical connection.
5. Connect YM/colour and modular moonshine only through independent same-object
   fields and gauge/stress/observable witnesses.

## Acceptance (not exact-head verified)
python3 scripts/check_kk_maxwell_first_integral_radion_source.py
agda -i . -i /path/to/agda-stdlib DASHI/Foundations/C3O2SignedWindingCompositionExact.agda

Source commits have been made, but exact-head Agda kernel and CI receipts have
not been observed. Do not mistake a flat-background inconsistency for a
no-go theorem against all nonzero KK electromagnetic backgrounds.
