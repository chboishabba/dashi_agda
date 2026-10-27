from dataclasses import dataclass
from math import sqrt

G = 6.67430e-11


@dataclass(frozen=True)
class TorsionBenchmark:
    mass_kg: float = 7.6e-6
    separation_m: float = 0.654e-3
    two_sigma_uncertainty_N: float = 50e-18

    @property
    def newton_force_N(self) -> float:
        return G * self.mass_kg**2 / self.separation_m**2

    @property
    def two_sigma_fractional_transfer(self) -> float:
        return self.two_sigma_uncertainty_N / self.newton_force_N


@dataclass(frozen=True)
class AtomInterferometerBenchmark:
    acceleration_nm_s2: float = 33.3
    stat_nm_s2: float = 5.6
    syst_nm_s2: float = 2.7

    @property
    def one_sigma_nm_s2(self) -> float:
        return sqrt(self.stat_nm_s2**2 + self.syst_nm_s2**2)

    @property
    def one_sigma_fractional_transfer(self) -> float:
        return self.one_sigma_nm_s2 / self.acceleration_nm_s2

    @property
    def two_sigma_fractional_transfer(self) -> float:
        return 2 * self.one_sigma_fractional_transfer


@dataclass(frozen=True)
class OptomechanicalBenchmark:
    unit_snr_full_gravity_hours_upper: float = 15.0

    def required_hours(self, epsilon_history: float, target_snr: float = 1.0) -> float:
        if epsilon_history <= 0:
            raise ValueError("epsilon_history must be positive")
        if target_snr <= 0:
            raise ValueError("target_snr must be positive")
        return self.unit_snr_full_gravity_hours_upper * (target_snr / epsilon_history) ** 2


def history_only_signal(reference_signal: float, epsilon_history: float) -> float:
    return reference_signal * epsilon_history


def required_fractional_precision_improvement(
    current_one_sigma_fraction: float,
    epsilon_history: float,
    target_snr: float = 5.0,
) -> float:
    if current_one_sigma_fraction <= 0:
        raise ValueError("current_one_sigma_fraction must be positive")
    if epsilon_history <= 0:
        raise ValueError("epsilon_history must be positive")
    if target_snr <= 0:
        raise ValueError("target_snr must be positive")
    return target_snr * current_one_sigma_fraction / epsilon_history


def white_noise_time_multiplier(precision_improvement: float) -> float:
    if precision_improvement <= 0:
        raise ValueError("precision_improvement must be positive")
    return precision_improvement**2


def main() -> None:
    torsion = TorsionBenchmark()
    atom = AtomInterferometerBenchmark()
    opto = OptomechanicalBenchmark()

    print(f"torsion_newton_force_aN={torsion.newton_force_N / 1e-18:.6f}")
    print(f"torsion_2sigma_fractional_transfer={torsion.two_sigma_fractional_transfer:.9f}")
    print(f"atom_1sigma_fractional_transfer={atom.one_sigma_fractional_transfer:.9f}")
    print(f"atom_2sigma_fractional_transfer={atom.two_sigma_fractional_transfer:.9f}")
    for eps in (0.1, 0.01, 0.001):
        print(f"torsion_history_signal_aN_eps_{eps:g}={history_only_signal(torsion.newton_force_N / 1e-18, eps):.9f}")
        print(f"opto_upper_hours_eps_{eps:g}_snr1={opto.required_hours(eps, 1):.6f}")
        print(f"opto_upper_hours_eps_{eps:g}_snr5={opto.required_hours(eps, 5):.6f}")
        improvement = required_fractional_precision_improvement(
            atom.one_sigma_fractional_transfer, eps, 5
        )
        print(f"atom_precision_improvement_eps_{eps:g}_snr5={improvement:.9f}")
        print(f"atom_white_time_multiplier_eps_{eps:g}_snr5={white_noise_time_multiplier(improvement):.9f}")


if __name__ == "__main__":
    main()
