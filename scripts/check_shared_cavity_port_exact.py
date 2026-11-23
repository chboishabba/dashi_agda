"""Abstract shared receiver observations and nested boundary bookkeeping."""
import sympy as s


def run():
    checks = []
    # A single observed cavity mode cannot distinguish two coherent source inputs.
    C = s.Matrix([[1, 1]])
    checks.append(C.nullspace() == [s.Matrix([-1, 1])])
    checks.append(C*s.Matrix([1, 0]) == C*s.Matrix([0, 1]))
    checks.append(C*s.Matrix([1, -1]) == s.zeros(1, 1))
    # Power-normalized contraction, with a retained dark input direction.
    T = C/s.sqrt(2)
    Q = s.eye(2)-T.H*T
    checks.append(Q*Q == Q)
    checks.append(Q.nullspace() == [s.Matrix([1, 1])])
    checks.append(Q.eigenvals() == {0: 1, 1: 1})
    # Nested energy boundary: internal crossing cancels with opposite signs.
    solar, storm, pump, crossing, loss1, loss2, load, du1, du2 = s.symbols('solar storm pump crossing loss1 loss2 load du1 du2', real=True)
    upstream = solar+storm-crossing-loss1-du1
    downstream = crossing+pump-load-loss2-du2
    checks.append(s.expand(upstream+downstream-(solar+storm+pump-load-loss1-loss2-du1-du2)) == 0)
    # Relabeling an internal transfer as an external input introduces a spurious term.
    checks.append(s.expand(upstream+downstream+crossing-(solar+storm+pump-load-loss1-loss2-du1-du2)) == crossing)
    assert all(checks), checks
    print(f'{len(checks)}/{len(checks)} exact checks PASS; SymPy {s.__version__}')

if __name__ == '__main__':
    run()
