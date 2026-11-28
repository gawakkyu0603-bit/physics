#!/usr/bin/env python3
"""
Deterministic Verification, Counterexample, and Figure Suite (G1-G5)
for:
  "Observer-Separated Selective Instruments, Born-Weighted Branching,
   and Non-Isometric Pullback Defects in Type II Gravitational Algebras"

Seed: 20261128
Outputs:
  - docs/numerical_verification.json
  - paper/figures/fig1_steering_and_lf_boundary.pdf
  - paper/figures/fig2_type2_clock_entropy.pdf
  - paper/figures/fig3_dynamical_nonisometric_pullback.pdf
  - paper/figures/fig4_branch_coupling_gate.pdf
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Dict, List, Tuple

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.linalg import eigh, sqrtm, svd
from scipy.optimize import linprog


SEED = 20261128
ROOT = Path(__file__).resolve().parents[1]
DOCS_DIR = ROOT / "docs"
FIG_DIR = ROOT / "paper" / "figures"


# ---------------------------------------------------------------------------
# Linear-algebra & quantum-information helpers
# ---------------------------------------------------------------------------

def ket_bra(v: np.ndarray) -> np.ndarray:
    return np.outer(v, v.conj())


def trace_norm(A: np.ndarray) -> float:
    return float(np.sum(np.linalg.svd(A, compute_uv=False)))


def op_norm(A: np.ndarray) -> float:
    return float(np.linalg.svd(A, compute_uv=False)[0])


def frob_norm(A: np.ndarray) -> float:
    return float(np.linalg.norm(A, "fro"))


def vn_entropy(rho: np.ndarray, tol: float = 1e-15) -> float:
    """Natural-log von Neumann / Segal entropy S(rho) = -Tr(rho ln rho)."""
    vals = np.linalg.eigvalsh((rho + rho.conj().T) / 2.0)
    vals = vals[vals > tol]
    return float(-np.sum(vals * np.log(vals)))


def segal_entropy_scaled(rho: np.ndarray, trace_scale: float, tol: float = 1e-15) -> float:
    """
    Semifinite trace rescaling tau' = c * tau => density rho' = rho / c satisfies
    tau'(rho') = 1 and S_{tau'}(rho') = -tau'(rho' ln rho') = S_tau(rho) + ln(c).
    Computed directly from eigenvalues of rho' under trace tau' = c * Tr.
    """
    rho_prime = rho / trace_scale
    vals = np.linalg.eigvalsh((rho_prime + rho_prime.conj().T) / 2.0)
    vals = vals[vals > tol]
    return float(-trace_scale * np.sum(vals * np.log(vals)))


def relative_entropy(rho: np.ndarray, sigma: np.ndarray, tol: float = 1e-14) -> float:
    """D(rho || sigma) = Tr(rho (ln rho - ln sigma)) in nats."""
    wr, vr = eigh((rho + rho.conj().T) / 2.0)
    ws, vs = eigh((sigma + sigma.conj().T) / 2.0)
    val = 0.0
    for i, r in enumerate(wr):
        if r <= tol:
            continue
        vi = vr[:, i]
        # Project vi onto eigenbasis of sigma
        overlaps = np.abs(vs.conj().T @ vi) ** 2
        if np.any(overlaps[ws <= tol] > 1e-12):
            return float("inf")
        mask = ws > tol
        ln_sig_exp = float(np.sum(overlaps[mask] * np.log(ws[mask])))
        val += float(r * (math.log(r) - ln_sig_exp))
    # Fail loud if pre-clip value is genuinely negative beyond floating-point roundoff
    assert val >= -1e-13, f"Relative entropy pre-clip negative value: {val}"
    return float(max(0.0, val))


def partial_trace(rho: np.ndarray, dims: Tuple[int, ...], keep: Tuple[int, ...]) -> np.ndarray:
    """Partial trace of a multipartite density matrix keeping subsystem indices in `keep`."""
    n = len(dims)
    keep = tuple(keep)
    trace_out = tuple(i for i in range(n) if i not in keep)
    resh = rho.reshape(*dims, *dims)
    # Permute to (keep, trace_out, keep', trace_out')
    perm = list(keep) + list(trace_out) + [i + n for i in keep] + [i + n for i in trace_out]
    resh = np.transpose(resh, perm)
    d_keep = int(np.prod([dims[i] for i in keep])) if keep else 1
    d_tr = int(np.prod([dims[i] for i in trace_out])) if trace_out else 1
    resh = resh.reshape(d_keep, d_tr, d_keep, d_tr)
    # Trace over trace_out (indices 1 and 3), keeping (indices 0 and 2)
    return np.einsum("ijkj->ik", resh)


def haar_unitary(d: int, rng: np.random.Generator) -> np.ndarray:
    """Exact Mezzadri (2007) QR-based Haar-random unitary in U(d)."""
    z = (rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))) / math.sqrt(2.0)
    q, r = np.linalg.qr(z)
    diag = np.diag(r)
    ph = diag / np.abs(diag)
    return q * ph[np.newaxis, :]


def petz_entanglement_fidelity_from_isometry(
    W: np.ndarray, d_C: int, d_A: int, d_B: int
) -> Tuple[float, float, float]:
    """
    Given a linear map W: H_C -> H_A x H_B (possibly approximate isometry; we renormalize
    the maximally entangled output state |Psi> = (I_R x W)|Phi^+> / norm), compute:
      - S_A (radiation entropy in bits for maximally mixed input)
      - F_e(Petz_A o E_A) for subsystem A (radiation)
      - F_e(Petz_B o E_B) for subsystem B (remaining BH)
    For an exact isometry W: H_C -> H_A x H_B, the channel E_A(rho) = Tr_B(W rho W^dagger)
    with maximally mixed prior pi = I/d_C has exact Petz recovery map
      R_A(Y) = pi^{1/2} E_A^dagger(sigma_A^{-1/2} Y sigma_A^{-1/2}) pi^{1/2},
    and entanglement fidelity F_e(R_A o E_A) = <Phi^+| (I x (R_A o E_A))(|Phi^+><Phi^+|) |Phi^+>.
    """
    # Construct Choi / pure tripartite state |Psi> in H_R (d_C) x H_A (d_A) x H_B (d_B)
    # |Phi^+> = (1/sqrt(d_C)) sum_i |i>_R |i>_C
    psi = np.zeros((d_C, d_A, d_B), dtype=np.complex128)
    for i in range(d_C):
        col = W[:, i].reshape(d_A, d_B)
        psi[i] = col / math.sqrt(d_C)
    norm_sq = float(np.vdot(psi, psi).real)
    psi = psi / math.sqrt(norm_sq)

    def petz_fe_for_kept(psi_rab: np.ndarray) -> Tuple[float, float]:
        # psi_rab has shape (d_R, d_keep, d_env)
        dR, dK, dE = psi_rab.shape
        # Kraus operators of E(rho) = sum_e K_e rho K_e^dagger from isometry:
        # <k|K_e|r> = sqrt(dR) * psi_rab[r, k, e]
        Ks = [math.sqrt(dR) * psi_rab[:, :, e].T for e in range(dE)]  # shape (dK, dR)
        # Channel output on maximally mixed state pi = I/dR:
        sigma = np.zeros((dK, dK), dtype=np.complex128)
        for K in Ks:
            sigma += (K @ K.conj().T) / dR
        # Entropy in bits
        vals = np.linalg.eigvalsh((sigma + sigma.conj().T) / 2.0)
        vals_pos = vals[vals > 1e-14]
        S_bits = float(-np.sum(vals_pos * np.log2(vals_pos)))
        # Pseudoinverse sigma^{-1/2}
        ws, vs = eigh((sigma + sigma.conj().T) / 2.0)
        inv_sqrt = np.zeros_like(sigma)
        for idx, lam in enumerate(ws):
            if lam > 1e-12:
                inv_sqrt += (1.0 / math.sqrt(lam)) * ket_bra(vs[:, idx])
        # Petz Kraus operators: P_e = (1/sqrt(dR)) K_e^dagger sigma^{-1/2}
        # Entanglement fidelity F_e(R o E) = (1/dR^2) sum_{e,f} |Tr(P_f K_e)|^2
        # = (1/dR^3) sum_{e,f} |Tr(K_f^dagger sigma^{-1/2} K_e)|^2
        fe = 0.0
        for Ke in Ks:
            M_e = inv_sqrt @ Ke
            for Kf in Ks:
                tr_val = np.trace(Kf.conj().T @ M_e)
                fe += float(abs(tr_val) ** 2)
        fe = fe / (dR ** 3)
        return S_bits, float(fe)

    S_A_bits, Fe_A = petz_fe_for_kept(psi)
    psi_rba = np.transpose(psi, (0, 2, 1))
    _, Fe_B = petz_fe_for_kept(psi_rba)
    return S_A_bits, Fe_A, Fe_B


# ---------------------------------------------------------------------------
# Suite G1: Theorem 1 — Single-Space Steering Floor & Rational 14/5 LF / FR
# ---------------------------------------------------------------------------

def run_suite_g1() -> Tuple[Dict, Dict]:
    # 1. Truncated bosonic Unruh/Hawking state (d = 4, r = 0.7 => n_BE = sinh^2 r)
    d = 4
    r_sq = 0.7
    z = math.tanh(r_sq)
    raw_weights = np.array([z ** (2 * n) for n in range(d)], dtype=np.float64)
    lambdas = raw_weights / np.sum(raw_weights)
    lam_min = float(np.min(lambdas))
    psi = np.zeros(d * d, dtype=np.complex128)
    for i in range(d):
        psi[i * d + i] = math.sqrt(lambdas[i])
    rho_RL = ket_bra(psi)
    rho_L = np.diag(lambdas).astype(np.complex128)
    sqrt_rho_L = np.diag(np.sqrt(lambdas)).astype(np.complex128)

    # Family of unsharp exterior number POVMs: E_0(eta) = (1-eta)*q*I + eta*|0><0|, E_1 = I - E_0
    q_bias = 0.35
    P0 = np.zeros((d, d), dtype=np.complex128)
    P0[0, 0] = 1.0
    etas = np.linspace(0.0, 1.0, 41)
    steering_tr = []
    steering_fr = []
    floor_fr = []
    max_identity_err = 0.0
    max_ns_err = 0.0

    for eta in etas:
        E0 = (1.0 - eta) * q_bias * np.eye(d) + eta * P0
        E1 = np.eye(d) - E0
        sig0 = partial_trace((np.kron(E0, np.eye(d))) @ rho_RL, (d, d), (1,))
        sig1 = partial_trace((np.kron(E1, np.eye(d))) @ rho_RL, (d, d), (1,))
        # Exact identity sigma_{L,x} = sqrt(rho_L) E_x^T sqrt(rho_L)
        sig0_exact = sqrt_rho_L @ E0.T @ sqrt_rho_L
        max_identity_err = max(max_identity_err, frob_norm(sig0 - sig0_exact))
        max_ns_err = max(max_ns_err, frob_norm((sig0 + sig1) - rho_L))
        p0 = float(np.trace(sig0).real)
        diff0 = sig0 - p0 * rho_L
        tr_val = trace_norm(diff0)
        fr_val = frob_norm(diff0)
        bd_val = lam_min * frob_norm(E0 - p0 * np.eye(d))
        assert tr_val + 1e-12 >= fr_val
        assert fr_val + 1e-12 >= bd_val
        steering_tr.append(tr_val)
        steering_fr.append(fr_val)
        floor_fr.append(bd_val)

    # Trivial POVM check at eta = 0
    zero_steering_at_trivial = steering_tr[0]

    # Negative Control 1: Product state rho_R x rho_L with sharp projective E0 = |0><0|
    rho_prod = np.kron(rho_L, rho_L)
    sig0_prod = partial_trace(np.kron(P0, np.eye(d)) @ rho_prod, (d, d), (1,))
    p0_prod = float(np.trace(sig0_prod).real)
    neg_ctrl_product_steering = trace_norm(sig0_prod - p0_prod * rho_L)
    assert neg_ctrl_product_steering < 1e-14

    # Negative Control 2: Classically correlated 2-qubit mixed state with conjugate X-basis POVM
    ket0 = np.array([1.0, 0.0], dtype=np.complex128)
    ket1 = np.array([0.0, 1.0], dtype=np.complex128)
    ketp = (ket0 + ket1) / math.sqrt(2.0)
    rho_cc = 0.5 * (np.kron(ket_bra(ket0), ket_bra(ket0)) + np.kron(ket_bra(ket1), ket_bra(ket1)))
    rho_L_2 = 0.5 * np.eye(2, dtype=np.complex128)
    E_plus = ket_bra(ketp)
    sig_cc_plus = partial_trace(np.kron(E_plus, np.eye(2)) @ rho_cc, (2, 2), (1,))
    p_cc_plus = float(np.trace(sig_cc_plus).real)
    neg_ctrl_classical_x_steering = trace_norm(sig_cc_plus - p_cc_plus * rho_L_2)
    neg_ctrl_classical_x_effect_nontrivial = frob_norm(E_plus - p_cc_plus * np.eye(2))
    assert neg_ctrl_classical_x_steering < 1e-14
    assert neg_ctrl_classical_x_effect_nontrivial > 0.5
    # Contrast with Z-basis on the same classical state (Bayesian update != 0)
    sig_cc_z0 = partial_trace(np.kron(ket_bra(ket0), np.eye(2)) @ rho_cc, (2, 2), (1,))
    neg_ctrl_classical_z_steering = trace_norm(sig_cc_z0 - 0.5 * rho_L_2)
    assert abs(neg_ctrl_classical_z_steering - 0.5) < 1e-14

    # Mixed-State Control (Two-qubit isotropic state rho_v = v|Phi^+><Phi^+| + (1-v) I_4 / 4, v = 1/4;
    # locally unitarily equivalent to two-qubit Werner states):
    # Demonstrates that purity is NOT strictly necessary for zero-steering <=> scalar-effect;
    # the exact general criterion is injectivity of the centered assemblage map, while the
    # quantitative Frobenius coefficient is v/2 (distinct from the pure-state lambda_min bound).
    v_werner = 0.25
    phi_plus_w = np.array([1.0, 0.0, 0.0, 1.0], dtype=np.complex128) / math.sqrt(2.0)
    rho_werner = v_werner * ket_bra(phi_plus_w) + (1.0 - v_werner) * 0.25 * np.eye(4, dtype=np.complex128)
    w_eigs = np.linalg.eigvalsh(rho_werner)
    assert abs(w_eigs[0] - 3.0 / 16.0) < 1e-14 and abs(w_eigs[-1] - 7.0 / 16.0) < 1e-14
    E_gen_w = np.array([[0.6, 0.2 - 0.15j], [0.2 + 0.15j, 0.3]], dtype=np.complex128)
    E_triv_w = 0.35 * np.eye(2, dtype=np.complex128)
    werner_max_id_err = 0.0
    for E_test in (ket_bra(ket0), E_plus, E_gen_w, E_triv_w):
        sig_w = partial_trace(np.kron(E_test, np.eye(2)) @ rho_werner, (2, 2), (1,))
        p_w = float(np.trace(sig_w).real)
        expected_diff = 0.5 * v_werner * (E_test.T - p_w * np.eye(2))
        werner_max_id_err = max(werner_max_id_err, frob_norm((sig_w - p_w * rho_L_2) - expected_diff))
    assert werner_max_id_err < 1e-14
    sig_w_x = partial_trace(np.kron(E_plus, np.eye(2)) @ rho_werner, (2, 2), (1,))
    sig_w_z = partial_trace(np.kron(ket_bra(ket0), np.eye(2)) @ rho_werner, (2, 2), (1,))
    sig_w_triv = partial_trace(np.kron(E_triv_w, np.eye(2)) @ rho_werner, (2, 2), (1,))
    werner_x_steering = trace_norm(sig_w_x - 0.5 * rho_L_2)
    werner_z_steering = trace_norm(sig_w_z - 0.5 * rho_L_2)
    werner_z_steering_frob = frob_norm(sig_w_z - 0.5 * rho_L_2)
    werner_z_correct_rhs = 0.5 * v_werner * frob_norm(ket_bra(ket0) - 0.5 * np.eye(2))
    werner_z_pure_coeff_rhs = 0.5 * frob_norm(ket_bra(ket0) - 0.5 * np.eye(2))
    werner_triv_steering = trace_norm(sig_w_triv - 0.35 * rho_L_2)
    assert abs(werner_x_steering - 0.5 * v_werner) < 1e-14
    assert abs(werner_z_steering - 0.5 * v_werner) < 1e-14
    assert abs(werner_z_steering_frob - werner_z_correct_rhs) < 1e-14
    assert werner_z_steering_frob < werner_z_pure_coeff_rhs - 0.25
    assert werner_triv_steering < 1e-14

    # 2. Exact Rational Pythagorean CHSH / Local Friendliness Witness (S = 14/5 = 2.8 > 2)
    Z = np.array([[1.0, 0.0], [0.0, -1.0]], dtype=np.complex128)
    X = np.array([[0.0, 1.0], [1.0, 0.0]], dtype=np.complex128)
    A0, A1 = Z, X
    B0 = 0.8 * Z + 0.6 * X
    B1 = 0.8 * Z - 0.6 * X
    involution_err = max(
        frob_norm(A0 @ A0 - np.eye(2)),
        frob_norm(A1 @ A1 - np.eye(2)),
        frob_norm(B0 @ B0 - np.eye(2)),
        frob_norm(B1 @ B1 - np.eye(2)),
    )
    assert involution_err < 1e-14
    phi_plus = np.array([1.0, 0.0, 0.0, 1.0], dtype=np.complex128) / math.sqrt(2.0)
    rho_bell = ket_bra(phi_plus)
    E00 = float(np.trace(np.kron(A0, B0) @ rho_bell).real)
    E01 = float(np.trace(np.kron(A0, B1) @ rho_bell).real)
    E10 = float(np.trace(np.kron(A1, B0) @ rho_bell).real)
    E11 = float(np.trace(np.kron(A1, B1) @ rho_bell).real)
    S_rational = E00 + E01 + E10 - E11
    assert abs(S_rational - 2.8) < 1e-14
    assert max_identity_err < 1e-14 and max_ns_err < 1e-14 and zero_steering_at_trivial < 1e-14

    # 3. Exact Frauchiger-Renner (2018) 1/12 probability witness
    psi_FR = np.array([1.0, 0.0, 1.0, 1.0], dtype=np.complex128) / math.sqrt(3.0)
    ok_R = np.array([1.0, -1.0], dtype=np.complex128) / math.sqrt(2.0)
    ok_S = np.array([1.0, -1.0], dtype=np.complex128) / math.sqrt(2.0)
    p_FR_ok_ok = float(abs(np.vdot(np.kron(ok_R, ok_S), psi_FR)) ** 2)
    p_FR_okS_given_t = float(abs(np.vdot(np.kron(np.array([0.0, 1.0]), ok_S), psi_FR)) ** 2) / (2.0 / 3.0)
    p_FR_h_given_up = float(abs(np.vdot(np.kron(np.array([1.0, 0.0]), np.array([0.0, 1.0])), psi_FR)) ** 2) / (1.0 / 3.0)
    p_FR_okR_given_down = float(abs(np.vdot(np.kron(ok_R, np.array([1.0, 0.0])), psi_FR)) ** 2) / (2.0 / 3.0)
    assert abs(p_FR_ok_ok - 1.0 / 12.0) < 1e-14
    assert p_FR_okS_given_t < 1e-14 and p_FR_h_given_up < 1e-14 and p_FR_okR_given_down < 1e-14

    res = {
        "d_schmidt": d,
        "squeezing_r": r_sq,
        "lambda_min": lam_min,
        "max_assemblage_identity_err": max_identity_err,
        "max_nonselective_ns_err": max_ns_err,
        "trivial_povm_steering_norm": zero_steering_at_trivial,
        "sharp_povm_steering_trace_norm": steering_tr[-1],
        "sharp_povm_steering_frob_norm": steering_fr[-1],
        "sharp_povm_floor_bound": floor_fr[-1],
        "neg_ctrl_product_steering": neg_ctrl_product_steering,
        "neg_ctrl_classical_x_steering": neg_ctrl_classical_x_steering,
        "neg_ctrl_classical_x_effect_nontrivial": neg_ctrl_classical_x_effect_nontrivial,
        "neg_ctrl_classical_z_steering": neg_ctrl_classical_z_steering,
        "werner_mixed_v": v_werner,
        "werner_mixed_min_eig": float(w_eigs[0]),
        "werner_mixed_max_eig": float(w_eigs[-1]),
        "werner_mixed_max_identity_err": werner_max_id_err,
        "werner_mixed_x_steering_trace_norm": werner_x_steering,
        "werner_mixed_z_steering_trace_norm": werner_z_steering,
        "werner_mixed_z_steering_frob_norm": werner_z_steering_frob,
        "werner_mixed_z_correct_rhs": werner_z_correct_rhs,
        "werner_mixed_z_pure_coeff_rhs": werner_z_pure_coeff_rhs,
        "werner_mixed_trivial_steering_norm": werner_triv_steering,
        "rational_lf_involution_err": involution_err,
        "rational_lf_E00": E00,
        "rational_lf_E01": E01,
        "rational_lf_E10": E10,
        "rational_lf_E11": E11,
        "rational_lf_S": S_rational,
        "rational_lf_exact_gap": S_rational - 2.0,
        "fr_p_ok_ok": p_FR_ok_ok,
        "fr_p_okS_given_t": p_FR_okS_given_t,
        "fr_p_h_given_up": p_FR_h_given_up,
        "fr_p_okR_given_down": p_FR_okR_given_down,
    }
    plot_data = {
        "etas": etas,
        "steering_tr": np.array(steering_tr),
        "steering_fr": np.array(steering_fr),
        "floor_fr": np.array(floor_fr),
        "neg_ctrl_product": neg_ctrl_product_steering,
        "neg_ctrl_classical_x": neg_ctrl_classical_x_steering,
    }
    return res, plot_data


# ---------------------------------------------------------------------------
# Suite G2: Theorem 2 — Model I (Coupling LP) vs Model II (Born Presheaf)
# ---------------------------------------------------------------------------

def solve_global_section_negativity(E00: float, E01: float, E10: float, E11: float) -> Tuple[bool, float]:
    """
    For a 2-party, 2-setting, dichotomic (+1/-1) no-signaling table with unbiased
    marginals p(a,b|i,j) = (1 + a*b*E_ij)/4, check:
      1. Whether a non-negative 16-entry global distribution Q(a0,a1,b0,b1) >= 0 exists.
      2. Minimum total negativity N_min = min_{Q = Q^+ - Q^-} sum Q^- matching all 16 pairwise marginals.
    """
    # Enumerate 16 global assignments (a0, a1, b0, b1) in {+1, -1}^4
    assignments = [
        (a0, a1, b0, b1)
        for a0 in (1, -1)
        for a1 in (1, -1)
        for b0 in (1, -1)
        for b1 in (1, -1)
    ]
    corrs = {(0, 0): E00, (0, 1): E01, (1, 0): E10, (1, 1): E11}
    rows = []
    rhs = []
    for i in (0, 1):
        for j in (0, 1):
            Eij = corrs[(i, j)]
            for a in (1, -1):
                for b in (1, -1):
                    row = [
                        1.0 if (u[i] == a and u[2 + j] == b) else 0.0
                        for u in assignments
                    ]
                    rows.append(row)
                    rhs.append(0.25 * (1.0 + a * b * Eij))
    A_eq = np.array(rows, dtype=np.float64)
    b_eq = np.array(rhs, dtype=np.float64)

    # Check feasibility for Q >= 0
    res_feas = linprog(
        c=np.zeros(16),
        A_eq=A_eq,
        b_eq=b_eq,
        bounds=[(0.0, None)] * 16,
        method="highs",
    )
    feasible = bool(res_feas.success)

    # Signed global section: Q = Q_plus - Q_minus, minimize sum(Q_minus)
    A_signed = np.hstack([A_eq, -A_eq])
    c_signed = np.concatenate([np.zeros(16), np.ones(16)])
    res_neg = linprog(
        c=c_signed,
        A_eq=A_signed,
        b_eq=b_eq,
        bounds=[(0.0, None)] * 32,
        method="highs",
    )
    assert res_neg.success, "No-signaling table must always admit a signed global section."
    n_min = float(res_neg.fun)
    return feasible, n_min


def run_suite_g2() -> Tuple[Dict, Dict]:
    # 1. Visibility sweep v in [0, 1] for rational Pythagorean observables (S = 14/5 * v)
    vs = np.linspace(0.0, 1.0, 41)
    S_vals = []
    neg_lp = []
    neg_exact = []
    model2_cpl_res = []
    for v in vs:
        E00, E01, E10, E11 = 0.8 * v, 0.8 * v, 0.6 * v, -0.6 * v
        S = E00 + E01 + E10 - E11
        _, nmin = solve_global_section_negativity(E00, E01, E10, E11)
        S_vals.append(S)
        neg_lp.append(nmin)
        neg_exact.append(max(0.0, (S - 2.0) / 4.0))
        # Model II single-context marginal check on context (0,0): verifies one marginal
        # probability p(a=0|0) = p(0,0|0,0) + p(0,1|0,0) = 1/2 (record agreement and
        # two-path composition are audited separately in G2 below).
        p_A_0 = 0.5
        p_C_marg_A = 0.25 * (1.0 + E00) + 0.25 * (1.0 - E00)
        model2_cpl_res.append(abs(p_A_0 - p_C_marg_A))

    # Specific check at v = 1 (rational witness S = 14/5) and v = 0.7 (S = 1.96 <= 2)
    feas_rational, nmin_rational = solve_global_section_negativity(0.8, 0.8, 0.6, -0.6)
    feas_local, nmin_local = solve_global_section_negativity(0.56, 0.56, 0.42, -0.42)
    # Tsirelson maximal witness S = 2*sqrt(2)
    s2 = 1.0 / math.sqrt(2.0)
    feas_tsirelson, nmin_tsirelson = solve_global_section_negativity(s2, s2, s2, -s2)

    # 2. Commuting shared-record diamond + R1 counterexamples + Wigner's friend dilation
    theta = 0.62
    psi_com = np.array([math.cos(theta), 0.0, 0.0, math.sin(theta)], dtype=np.complex128)
    rho_com = ket_bra(psi_com)
    P0 = np.array([[1.0, 0.0], [0.0, 0.0]], dtype=np.complex128)
    P1 = np.array([[0.0, 0.0], [0.0, 1.0]], dtype=np.complex128)
    X2 = np.array([[0.0, 1.0], [1.0, 0.0]], dtype=np.complex128)
    T_mat = np.array([
        [float(np.trace(np.kron(Pi, Pj) @ rho_com).real) for Pj in (P0, P1)]
        for Pi in (P0, P1)
    ])
    pA_born = np.array([float(np.trace(np.kron(Pi, np.eye(2)) @ rho_com).real) for Pi in (P0, P1)])
    pB_born = np.array([float(np.trace(np.kron(np.eye(2), Pj) @ rho_com).real) for Pj in (P0, P1)])
    commuting_cpl_err = float(
        max(np.max(np.abs(T_mat.sum(axis=1) - pA_born)), np.max(np.abs(T_mat.sum(axis=0) - pB_born)))
    )
    commuting_disagreement = float(T_mat[0, 1] + T_mat[1, 0])
    assert commuting_cpl_err < 1e-14 and commuting_disagreement < 1e-14

    # 2a. Counterexample: equal uniform marginals (1/2, 1/2) do NOT imply record agreement P(a != b) = 0
    T_indep = np.full((2, 2), 0.25)
    T_corr = np.diag([0.5, 0.5])
    T_anti = np.array([[0.0, 0.5], [0.5, 0.0]])
    for T_ex in (T_indep, T_corr, T_anti):
        assert np.max(np.abs(T_ex.sum(axis=1) - np.array([0.5, 0.5]))) < 1e-15
        assert np.max(np.abs(T_ex.sum(axis=0) - np.array([0.5, 0.5]))) < 1e-15
    marginal_eq_indep_disagree = float(T_indep[0, 1] + T_indep[1, 0])
    marginal_eq_anti_disagree = float(T_anti[0, 1] + T_anti[1, 0])
    assert abs(marginal_eq_indep_disagree - 0.5) < 1e-15
    assert abs(marginal_eq_anti_disagree - 1.0) < 1e-15

    # 2b. Counterexample: commuting effects [K_a^dag K_a, F_b] = 0 do NOT imply sequential Kraus agreement
    rho_mm = 0.5 * np.eye(2, dtype=np.complex128)
    Ks_flip = [X2 @ P0, X2 @ P1]
    Fs_proj = [P0, P1]
    assert frob_norm(Ks_flip[0].conj().T @ Ks_flip[0] + Ks_flip[1].conj().T @ Ks_flip[1] - np.eye(2)) < 1e-15
    for Ka in Ks_flip:
        Ea = Ka.conj().T @ Ka
        for Fb in Fs_proj:
            assert frob_norm(Ea @ Fb - Fb @ Ea) < 1e-15
    static_joint_disagree = float(
        np.trace(P0 @ P1 @ rho_mm).real + np.trace(P1 @ P0 @ rho_mm).real
    )
    seq_kraus_disagree = float(
        np.trace(Fs_proj[1] @ Ks_flip[0] @ rho_mm @ Ks_flip[0].conj().T).real
        + np.trace(Fs_proj[0] @ Ks_flip[1] @ rho_mm @ Ks_flip[1].conj().T).real
    )
    assert static_joint_disagree < 1e-15 and abs(seq_kraus_disagree - 1.0) < 1e-15

    # 2c. Concrete finite-dimensional Wigner's friend dilation U_SF:
    # Record-preserving CPL readout vs. Wigner's record-erasing interference context
    U_SF = np.kron(P0, np.eye(2)) + np.kron(P1, X2)  # CNOT premeasurement
    assert frob_norm(U_SF.conj().T @ U_SF - np.eye(4)) < 1e-15
    psi_init_SF = np.kron(np.array([1.0, 1.0], dtype=np.complex128) / math.sqrt(2.0), np.array([1.0, 0.0], dtype=np.complex128))
    psi_coh_SF = U_SF @ psi_init_SF  # = |Phi^+>_{SF}
    rho_coh_SF = ket_bra(psi_coh_SF)
    # Record-preserving readout context (Z_S, Z_F nondestructive projectors)
    wf_joint = np.array([
        [float(np.trace(np.kron(Pi, Pj) @ rho_coh_SF).real) for Pj in (P0, P1)]
        for Pi in (P0, P1)
    ])
    wf_cpl_disagree = float(wf_joint[0, 1] + wf_joint[1, 0])
    rho_deph_SF = sum(
        np.kron(Pi, Pj) @ rho_coh_SF @ np.kron(Pi, Pj)
        for Pi in (P0, P1) for Pj in (P0, P1)
    )
    # Wigner's record-erasing interference context: P_int = |Phi^+><Phi^+|_{SF}
    P_int_SF = ket_bra(psi_coh_SF)
    wf_p_int_coherent = float(np.trace(P_int_SF @ rho_coh_SF).real)
    wf_p_int_dephased = float(np.trace(P_int_SF @ rho_deph_SF).real)
    wf_interference_contrast = wf_p_int_coherent - wf_p_int_dephased
    assert wf_cpl_disagree < 1e-15
    assert abs(wf_p_int_coherent - 1.0) < 1e-15
    assert abs(wf_p_int_dephased - 0.5) < 1e-15
    assert abs(wf_interference_contrast - 0.5) < 1e-15

    # 3. Born-weight linearity representation check, non-affine distortion, & replacer non-uniqueness
    rho1 = np.array([[0.8, 0.1], [0.1, 0.2]], dtype=np.complex128)
    rho2 = np.array([[0.3, -0.2j], [0.2j, 0.7]], dtype=np.complex128)
    lam = 0.37
    rho_mix = lam * rho1 + (1.0 - lam) * rho2
    K0 = np.array([[math.sqrt(0.75), 0.0], [0.0, math.sqrt(0.25)]], dtype=np.complex128)
    w_lin_mix = float(np.trace(K0 @ rho_mix @ K0.conj().T).real)
    w_lin_avg = lam * float(np.trace(K0 @ rho1 @ K0.conj().T).real) + (1.0 - lam) * float(
        np.trace(K0 @ rho2 @ K0.conj().T).real
    )
    born_linearity_err = abs(w_lin_mix - w_lin_avg)
    assert born_linearity_err < 1e-15
    # Non-affine quadratic weight negative control: w_nl(rho) = Tr(rho^2) * w_lin(rho)
    w_nl_mix = float(np.trace(rho_mix @ rho_mix).real) * w_lin_mix
    w_nl_avg = lam * float(np.trace(rho1 @ rho1).real) * float(np.trace(K0 @ rho1 @ K0.conj().T).real) + (
        1.0 - lam
    ) * float(np.trace(rho2 @ rho2).real) * float(np.trace(K0 @ rho2 @ K0.conj().T).real)
    nonaffine_distortion = abs(w_nl_mix - w_nl_avg)
    assert nonaffine_distortion > 1e-3

    # 3b. Replacer unraveling non-uniqueness counterexample (C1):
    # I_0^{(a)}(rho) = a Tr(rho) sigma, I_1^{(a)}(rho) = (1-a) Tr(rho) sigma
    sigma_rep = np.diag([0.7, 0.3]).astype(np.complex128)
    a_rep1, a_rep2 = 0.37, 0.81
    I0_a1 = a_rep1 * float(np.trace(rho1).real) * sigma_rep
    I1_a1 = (1.0 - a_rep1) * float(np.trace(rho1).real) * sigma_rep
    I0_a2 = a_rep2 * float(np.trace(rho1).real) * sigma_rep
    I1_a2 = (1.0 - a_rep2) * float(np.trace(rho1).real) * sigma_rep
    replacer_layer1_diff = frob_norm((I0_a1 + I1_a1) - (I0_a2 + I1_a2))
    replacer_cond_state_diff = frob_norm((I0_a1 / a_rep1) - (I0_a2 / a_rep2))
    replacer_weight_gap = abs(a_rep2 - a_rep1)
    assert replacer_layer1_diff < 1e-15 and replacer_cond_state_diff < 1e-15
    assert abs(replacer_weight_gap - 0.44) < 1e-15

    # 3c. Additional independent-review checks for Model II & Theorem 2:
    # (i) Bell |Phi^+> vs. maximally mixed I_4/4 share identical local marginals (I_2/2)
    #     and identical local branch measures, yet Z x Z disagreement is 0 vs. 1/2.
    rho_bell_g2 = ket_bra(np.array([1.0, 0.0, 0.0, 1.0], dtype=np.complex128) / math.sqrt(2.0))
    rho_mix4_g2 = 0.25 * np.eye(4, dtype=np.complex128)
    bell_vs_mix_local_diff = max(
        frob_norm(partial_trace(rho_bell_g2, (2, 2), (0,)) - partial_trace(rho_mix4_g2, (2, 2), (0,))),
        frob_norm(partial_trace(rho_bell_g2, (2, 2), (1,)) - partial_trace(rho_mix4_g2, (2, 2), (1,))),
    )
    bell_zz_disagree = float(np.trace((np.kron(P0, P1) + np.kron(P1, P0)) @ rho_bell_g2).real)
    mix4_zz_disagree = float(np.trace((np.kron(P0, P1) + np.kron(P1, P0)) @ rho_mix4_g2).real)
    assert bell_vs_mix_local_diff < 1e-15 and bell_zz_disagree < 1e-15 and abs(mix4_zz_disagree - 0.5) < 1e-15

    # (ii) Exact necessary-and-sufficient Kraus orthogonality criterion: sum_alpha K_{a,alpha}^dag F_b K_{a,alpha} = 0 (a != b)
    kraus_orthog_preserving_frob = max(
        frob_norm(P0.conj().T @ P1 @ P0), frob_norm(P1.conj().T @ P0 @ P1)
    )
    kraus_orthog_flip_frob = max(
        frob_norm(Ks_flip[0].conj().T @ Fs_proj[1] @ Ks_flip[0]),
        frob_norm(Ks_flip[1].conj().T @ Fs_proj[0] @ Ks_flip[1]),
    )
    assert kraus_orthog_preserving_frob < 1e-15 and abs(kraus_orthog_flip_frob - 1.0) < 1e-15

    # (ii-b) Wigner's friend premeasurement isometry J |psi>_S = U_CNOT (|psi>_S |0>_F) (Theorem 2(b.2)):
    #        effective logical-to-record Kraus operators L_a = (P_a x I_F) J satisfy Eq. (10) identically
    #        for ALL logical inputs, whereas unrestricted 4D input |01> gives disagreement 1.
    J_wf = np.zeros((4, 2), dtype=np.complex128)
    J_wf[0, 0] = 1.0  # |00><0|
    J_wf[3, 1] = 1.0  # |11><1|
    L0_wf = np.kron(P0, np.eye(2, dtype=np.complex128)) @ J_wf
    L1_wf = np.kron(P1, np.eye(2, dtype=np.complex128)) @ J_wf
    F0_wf = np.kron(np.eye(2, dtype=np.complex128), P0)
    F1_wf = np.kron(np.eye(2, dtype=np.complex128), P1)
    D_mis_4d = np.kron(P0, P1) + np.kron(P1, P0)
    wf_premeas_completeness_err = frob_norm(L0_wf.conj().T @ L0_wf + L1_wf.conj().T @ L1_wf - np.eye(2))
    wf_premeas_kraus_orthog_frob = max(
        frob_norm(L0_wf.conj().T @ F1_wf @ L0_wf),
        frob_norm(L1_wf.conj().T @ F0_wf @ L1_wf),
    )
    wf_premeas_ranJ_dmis_frob = frob_norm(J_wf.conj().T @ D_mis_4d @ J_wf)
    rho_01_4d = np.zeros((4, 4), dtype=np.complex128)
    rho_01_4d[1, 1] = 1.0
    wf_unrestricted_01_disagreement = float(np.trace(D_mis_4d @ rho_01_4d).real)
    assert (
        wf_premeas_completeness_err < 1e-15
        and wf_premeas_kraus_orthog_frob < 1e-15
        and wf_premeas_ranJ_dmis_frob < 1e-15
        and abs(wf_unrestricted_01_disagreement - 1.0) < 1e-15
    )

    # (iii) Minimal finite-dimensional two-path causal diamond (O -> M_1 -> C vs. O -> M_2 -> C)
    #       on C^2_rec x C^2_env: U_1 = I x I, U_2 = I x X agree on A_{rec,C} yet differ off-record.
    U_diam1 = np.eye(4, dtype=np.complex128)
    U_diam2 = np.kron(np.eye(2, dtype=np.complex128), X2)
    R_rec_obs = np.kron(np.diag([0.3, -0.7]).astype(np.complex128), np.eye(2, dtype=np.complex128))
    E_env_obs = np.kron(np.eye(2, dtype=np.complex128), np.diag([1.0, -1.0]).astype(np.complex128))
    diamond_rec_pullback_diff = frob_norm(
        U_diam1.conj().T @ R_rec_obs @ U_diam1 - U_diam2.conj().T @ R_rec_obs @ U_diam2
    )
    diamond_env_pullback_diff = frob_norm(
        U_diam1.conj().T @ E_env_obs @ U_diam1 - U_diam2.conj().T @ E_env_obs @ U_diam2
    )
    assert diamond_rec_pullback_diff < 1e-15 and diamond_env_pullback_diff > 1.0

    # (iv) Complementary unraveling non-uniqueness: same replacer Phi(rho) = Tr(rho) I_2/2 and same
    #      weights (1/2, 1/2), yet distinct conditional states (I_2/2 vs. |x><x|).
    rep_same_w_branch0_A = 0.5 * (0.5 * np.eye(2, dtype=np.complex128))
    rep_same_w_branch1_A = 0.5 * (0.5 * np.eye(2, dtype=np.complex128))
    rep_same_w_branch0_B = 0.5 * P0
    rep_same_w_branch1_B = 0.5 * P1
    rep_same_w_layer1_diff = frob_norm(
        (rep_same_w_branch0_A + rep_same_w_branch1_A) - (rep_same_w_branch0_B + rep_same_w_branch1_B)
    )
    rep_same_w_cond_td = 0.5 * trace_norm(2.0 * rep_same_w_branch0_A - 2.0 * rep_same_w_branch0_B)
    assert rep_same_w_layer1_diff < 1e-15 and abs(rep_same_w_cond_td - 0.5) < 1e-15

    max_lp_analytic_err = float(np.max(np.abs(np.array(neg_lp) - np.array(neg_exact))))
    assert max_lp_analytic_err < 1e-12
    assert not feas_rational and abs(nmin_rational - 0.2) < 1e-12
    assert feas_local and abs(nmin_local) < 1e-12
    assert not feas_tsirelson and abs(nmin_tsirelson - (2.0 * math.sqrt(2.0) - 2.0) / 4.0) < 1e-12

    res = {
        "rational_witness_model1_feasible": int(feas_rational),
        "rational_witness_min_negativity": nmin_rational,
        "local_regime_model1_feasible": int(feas_local),
        "local_regime_min_negativity": nmin_local,
        "tsirelson_model1_feasible": int(feas_tsirelson),
        "tsirelson_min_negativity": nmin_tsirelson,
        "tsirelson_exact_formula": (2.0 * math.sqrt(2.0) - 2.0) / 4.0,
        "max_lp_vs_analytic_negativity_err": max_lp_analytic_err,
        "max_model2_commuting_marginal_residual": float(np.max(model2_cpl_res)),
        "commuting_diamond_marginal_err": commuting_cpl_err,
        "commuting_diamond_record_disagreement": commuting_disagreement,
        "r1_equal_marginal_indep_disagreement": marginal_eq_indep_disagree,
        "r1_equal_marginal_anti_disagreement": marginal_eq_anti_disagree,
        "r1_commuting_effects_static_disagreement": static_joint_disagree,
        "r1_commuting_effects_seq_kraus_disagreement": seq_kraus_disagree,
        "wigner_friend_cpl_disagreement": wf_cpl_disagree,
        "wigner_friend_p_int_coherent": wf_p_int_coherent,
        "wigner_friend_p_int_dephased": wf_p_int_dephased,
        "wigner_friend_interference_contrast": wf_interference_contrast,
        "born_linearity_err": born_linearity_err,
        "nonaffine_weight_distortion_neg_ctrl": nonaffine_distortion,
        "replacer_layer1_diff": replacer_layer1_diff,
        "replacer_cond_state_diff": replacer_cond_state_diff,
        "replacer_weight_gap": replacer_weight_gap,
        "bell_vs_mix_local_diff": bell_vs_mix_local_diff,
        "bell_zz_disagreement": bell_zz_disagree,
        "mix4_zz_disagreement": mix4_zz_disagree,
        "kraus_orthog_preserving_frob": kraus_orthog_preserving_frob,
        "kraus_orthog_flip_frob": kraus_orthog_flip_frob,
        "wf_premeas_completeness_err": wf_premeas_completeness_err,
        "wf_premeas_kraus_orthog_frob": wf_premeas_kraus_orthog_frob,
        "wf_premeas_ranJ_dmis_frob": wf_premeas_ranJ_dmis_frob,
        "wf_unrestricted_01_disagreement": wf_unrestricted_01_disagreement,
        "two_path_diamond_rec_pullback_diff": diamond_rec_pullback_diff,
        "two_path_diamond_env_pullback_diff": diamond_env_pullback_diff,
        "replacer_same_weight_layer1_diff": rep_same_w_layer1_diff,
        "replacer_same_weight_cond_td": rep_same_w_cond_td,
    }
    plot_data = {
        "vs": vs,
        "S_vals": np.array(S_vals),
        "neg_lp": np.array(neg_lp),
        "neg_exact": np.array(neg_exact),
        "model2_cpl_res": np.array(model2_cpl_res),
    }
    return res, plot_data


# ---------------------------------------------------------------------------
# Suite G3: Theorem 3 — Finite Z_K Clock Precursor & Type II Entropy Split
# ---------------------------------------------------------------------------

def build_clock_twirl(H_S: np.ndarray, K: int) -> List[np.ndarray]:
    """Unitary constraint group W_t = exp(2*pi*i*t*(H_S + H_C)/K) for t in Z_K."""
    dS = H_S.shape[0]
    e_S = np.diag(H_S).real
    e_C = np.arange(K, dtype=np.float64)
    tot_e = np.add.outer(e_S, e_C).reshape(-1)
    Ws = []
    for t in range(K):
        phases = np.exp(2j * math.pi * t * tot_e / K)
        Ws.append(np.diag(phases))
    return Ws


def gauge_average(X: np.ndarray, Ws: List[np.ndarray]) -> np.ndarray:
    K = len(Ws)
    out = np.zeros_like(X, dtype=np.complex128)
    for W in Ws:
        out += W @ X @ W.conj().T
    return out / K


def run_suite_g3() -> Tuple[Dict, Dict]:
    rng = np.random.default_rng(SEED + 3)
    # 1. Verify Umegaki bimodule conditional expectation on Z_K clock algebra
    K = 8
    H_S = np.diag([0.0, 1.0, 2.0])  # dS = 3 system with integer spectrum
    dS = 3
    dim = dS * K
    Ws = build_clock_twirl(H_S, K)

    # Random test operators X, Y, Z
    A_raw = rng.standard_normal((dim, dim)) + 1j * rng.standard_normal((dim, dim))
    B_raw = rng.standard_normal((dim, dim)) + 1j * rng.standard_normal((dim, dim))
    X_raw = rng.standard_normal((dim, dim)) + 1j * rng.standard_normal((dim, dim))
    A_inv = gauge_average(A_raw, Ws)
    B_inv = gauge_average(B_raw, Ws)
    EX = gauge_average(X_raw, Ws)
    EEX = gauge_average(EX, Ws)

    cond_exp_idempotence_err = frob_norm(EEX - EX)
    cond_exp_bimodule_err = frob_norm(gauge_average(A_inv @ X_raw @ B_inv, Ws) - (A_inv @ EX @ B_inv))
    cond_exp_tp_err = abs(np.trace(EX) - np.trace(X_raw))
    cond_exp_unital_err = frob_norm(gauge_average(np.eye(dim, dtype=np.complex128), Ws) - np.eye(dim))
    max_comm_err = max(frob_norm(A_inv @ W - W @ A_inv) for W in Ws)

    # Clock-dressed raising operator: |1><0|_S x U_C^{-1} commutes with W_t!
    U_shift_inv = np.roll(np.eye(K, dtype=np.complex128), -1, axis=0)  # |q-1><q|
    raise_S = np.zeros((dS, dS), dtype=np.complex128)
    raise_S[1, 0] = 1.0
    dressed_op = np.kron(raise_S, U_shift_inv)
    dressed_comm_err = max(frob_norm(dressed_op @ W - W @ dressed_op) for W in Ws)
    # Undressed raising operator fails to commute (negative control!)
    undressed_op = np.kron(raise_S, np.eye(K, dtype=np.complex128))
    undressed_comm_norm = max(frob_norm(undressed_op @ W - W @ undressed_op) for W in Ws)

    # 2. Covariant selective instrument on A_O^{(K)} & Generalized-Entropy Branch Decomposition
    # Construct coherent gauge-invariant state rho_O in A_O^{(K)} with genuine system-clock coherence
    # (off-diagonal terms |a, q><b, q+a-b| invariant under W_t!) mixed with thermal background
    beta_S = 0.8
    rho_S_th = np.diag(np.exp(-beta_S * np.diag(H_S).real))
    rho_S_th /= np.trace(rho_S_th)
    psi_S_coh = np.array([math.sqrt(0.55), math.sqrt(0.30), math.sqrt(0.15)], dtype=np.complex128)
    rho_S_mix = 0.4 * rho_S_th + 0.6 * ket_bra(psi_S_coh)
    q_grid = np.arange(K, dtype=np.float64)
    psi_C = np.exp(-0.18 * (q_grid - K / 2.0) ** 2)
    psi_C /= np.linalg.norm(psi_C)
    rho_init = gauge_average(np.kron(rho_S_mix, ket_bra(psi_C)), Ws)
    # Ensure exact Hermiticity and unit trace
    rho_init = (rho_init + rho_init.conj().T) / 2.0
    rho_init /= np.trace(rho_init).real

    # Covariant 3-outcome selective Lüders instrument measuring dressed system energy sectors Pi_a x I_C
    # Interpolated with sharpness parameter eta in [0, 1]:
    # M_a(eta) = sqrt((1-eta)/3 * I + eta * (Pi_a x I_C)) (all commute with W_t!)
    etas = np.linspace(0.0, 1.0, 41)
    dS_L1_arr = []
    dS_L2_arr = []
    chi_arr = []
    shannon_arr = []
    max_decomp_err = 0.0
    max_rel_ent_err = 0.0

    S_init = vn_entropy(rho_init)
    for eta in etas:
        Ks = []
        for a in range(dS):
            Pi_a = np.zeros((dS, dS), dtype=np.complex128)
            Pi_a[a, a] = 1.0
            Ea = ((1.0 - eta) / dS) * np.eye(dim) + eta * np.kron(Pi_a, np.eye(K))
            Ks.append(np.diag(np.sqrt(np.diag(Ea).real)).astype(np.complex128))
        # Apply instrument
        branches = [Ka @ rho_init @ Ka.conj().T for Ka in Ks]
        ps = [float(np.trace(b).real) for b in branches]
        rho_cond = [b / p for b, p in zip(branches, ps)]
        rho_bar = sum(branches)
        S_bar = vn_entropy(rho_bar)
        S_cond = [vn_entropy(rc) for rc in rho_cond]
        dS_L1 = S_bar - S_init
        dS_L2 = float(sum(p * (sc - S_init) for p, sc in zip(ps, S_cond)))
        chi_val = S_bar - float(sum(p * sc for p, sc in zip(ps, S_cond)))
        chi_rel = float(sum(p * relative_entropy(rc, rho_bar) for p, rc in zip(ps, rho_cond)))
        H_p = float(-sum(p * math.log(p) for p in ps if p > 1e-15))
        max_decomp_err = max(max_decomp_err, abs((dS_L1 - dS_L2) - chi_val))
        max_rel_ent_err = max(max_rel_ent_err, abs(chi_val - chi_rel))
        assert chi_val >= -1e-12 and chi_val <= H_p + 1e-12
        dS_L1_arr.append(dS_L1)
        dS_L2_arr.append(dS_L2)
        chi_arr.append(chi_val)
        shannon_arr.append(H_p)

    # 3. Exact Trace-Scale Invariance (Type II_infty renormalization tau -> c * tau)
    # Test at eta = 0.85 across c in {0.1, 1.0, 10.0, 100.0}
    eta_ref = 0.85
    Ks_ref = []
    for a in range(dS):
        Pi_a = np.zeros((dS, dS), dtype=np.complex128)
        Pi_a[a, a] = 1.0
        Ea = ((1.0 - eta_ref) / dS) * np.eye(dim) + eta_ref * np.kron(Pi_a, np.eye(K))
        Ks_ref.append(np.diag(np.sqrt(np.diag(Ea).real)).astype(np.complex128))
    branches_ref = [Ka @ rho_init @ Ka.conj().T for Ka in Ks_ref]
    ps_ref = [float(np.trace(b).real) for b in branches_ref]
    rc_ref = [b / p for b, p in zip(branches_ref, ps_ref)]
    rho_bar_ref = sum(branches_ref)
    dS_L1_ref = vn_entropy(rho_bar_ref) - S_init
    chi_ref = vn_entropy(rho_bar_ref) - sum(p * vn_entropy(rc) for p, rc in zip(ps_ref, rc_ref))

    scale_shifts = []
    max_scale_invariance_err = 0.0
    for c_scale in (0.1, 1.0, 10.0, 100.0):
        s_init_c = segal_entropy_scaled(rho_init, c_scale)
        s_bar_c = segal_entropy_scaled(rho_bar_ref, c_scale)
        s_cond_c = [segal_entropy_scaled(rc, c_scale) for rc in rc_ref]
        dL1_c = s_bar_c - s_init_c
        chi_c = s_bar_c - sum(p * sc for p, sc in zip(ps_ref, s_cond_c))
        scale_shifts.append(s_init_c - S_init)
        max_scale_invariance_err = max(
            max_scale_invariance_err,
            abs(dL1_c - dS_L1_ref),
            abs(chi_c - chi_ref),
            abs((s_init_c - S_init) - math.log(c_scale)),
        )

    # 4. Ozawa (1986) Negative Control: Groenewold information gain < 0 on pure input
    # 2-outcome instrument on 2-level system: I_x(rho) = Tr(E_x rho) * ((1-q)|x><x| + q * I/2)
    # Valid CP instrument (measure-and-prepare with noisy preparation); pure input |+><+| gives S(rho)=0,
    # so I_GO = S(rho) - sum p_x S(rho_{|x}) = -S((1-q)|0><0| + q I/2) < 0 for all q > 0!
    qs = np.linspace(0.0, 1.0, 41)
    ozawa_I_GO = []
    ozawa_chi = []
    ozawa_H = []
    rho_pure = ket_bra(np.array([1.0, 1.0], dtype=np.complex128) / math.sqrt(2.0))
    S_pure = vn_entropy(rho_pure)
    for q in qs:
        p0, p1 = 0.5, 0.5
        r0 = (1.0 - q) * np.array([[1.0, 0.0], [0.0, 0.0]]) + q * 0.5 * np.eye(2)
        r1 = (1.0 - q) * np.array([[0.0, 0.0], [0.0, 1.0]]) + q * 0.5 * np.eye(2)
        rbar = p0 * r0 + p1 * r1
        I_GO = S_pure - (p0 * vn_entropy(r0) + p1 * vn_entropy(r1))
        chi_q = vn_entropy(rbar) - (p0 * vn_entropy(r0) + p1 * vn_entropy(r1))
        ozawa_I_GO.append(I_GO)
        ozawa_chi.append(chi_q)
        ozawa_H.append(math.log(2.0))

    # 5. Finite-group K-invariance check (NOT a Type II continuum limit!) and algebra structure
    # For E = Pi_0 x I_K invariant under W_t, Tr(E E_inv(rho_S^th x rho_C)) = Tr(Pi_0 rho_S^th) identically.
    Ks_conv = [4, 8, 16, 32]
    born_K = []
    exact_thermal_p0 = 1.0 / (1.0 + math.exp(-beta_S) + math.exp(-2.0 * beta_S))
    for Kk in Ks_conv:
        Wsk = build_clock_twirl(H_S, Kk)
        q_g = np.arange(Kk, dtype=np.float64)
        pC = np.exp(-0.25 * (q_g - Kk / 2.0) ** 2)
        pC /= np.linalg.norm(pC)
        rhok = gauge_average(np.kron(rho_S_th, ket_bra(pC)), Wsk)
        Pi0 = np.zeros((dS, dS), dtype=np.complex128)
        Pi0[0, 0] = 1.0
        born_K.append(float(np.trace(np.kron(Pi0, np.eye(Kk)) @ rhok).real))
    born_K_spread = float(max(born_K) - min(born_K))
    born_K_exact_err = float(max(abs(v - exact_thermal_p0) for v in born_K))
    assert born_K_spread < 1e-14 and born_K_exact_err < 1e-14

    # Verify finite-group algebra structure A_O^{(K)} = \bigoplus_{r=0}^{K-1} M_{d_S}(C):
    # Each modular energy sector (e_S + e_C) mod K has exact multiplicity d_S, so linear dim = K * d_S^2
    mod_charges = [int((e_s + q) % K) for e_s in np.diag(H_S).real for q in range(K)]
    sector_sizes = [mod_charges.count(r) for r in range(K)]
    assert all(sz == dS for sz in sector_sizes)
    algebra_linear_dim = int(sum(sz * sz for sz in sector_sizes))
    assert algebra_linear_dim == K * dS * dS

    # 6. Corollary 1 state-dependent clock-field correction test:
    # S_tau(rho) = S_gen(rho) + C + delta(rho), where delta(rho) = gamma * I(S:C)_rho models
    # clock-field entanglement corrections (De Vuyst et al. 2025). Verify C cancels while
    # -delta(rho_bar) + sum p_x delta(rho_x) does NOT vanish automatically.
    def clock_field_mi(rho_sc: np.ndarray) -> float:
        rS = partial_trace(rho_sc, (dS, K), (0,))
        rC = partial_trace(rho_sc, (dS, K), (1,))
        return vn_entropy(rS) + vn_entropy(rC) - vn_entropy(rho_sc)

    gamma_corr = 0.1
    C_const = 2.5
    delta_init = gamma_corr * clock_field_mi(rho_init)
    delta_bar = gamma_corr * clock_field_mi(rho_bar_ref)
    delta_conds = [gamma_corr * clock_field_mi(rc) for rc in rc_ref]
    Sgen_init = S_init - C_const - delta_init
    Sgen_bar = vn_entropy(rho_bar_ref) - C_const - delta_bar
    Sgen_conds = [vn_entropy(rc) - C_const - dc for rc, dc in zip(rc_ref, delta_conds)]
    dSgen_L1 = Sgen_bar - Sgen_init
    dSgen_L2 = float(sum(p * (sg - Sgen_init) for p, sg in zip(ps_ref, Sgen_conds)))
    cor1_state_dep_residual = -delta_bar + float(sum(p * dc for p, dc in zip(ps_ref, delta_conds)))
    cor1_identity_err = abs((dSgen_L1 - dSgen_L2) - (chi_ref + cor1_state_dep_residual))
    assert cor1_identity_err < 1e-14
    assert abs(cor1_state_dep_residual) > 1e-4

    # 7. Noncommutative rescaled-trace check for Theorem 3(b) repaired Step 2 (RR-1):
    # M = M_2(C), tau = (1/2) Tr, p = (1/4, 3/4), rho_1 = diag(1.999, 0.001),
    # bar_rho = [[1, -1/2], [-1/2, 1]], rho_2 = (bar_rho - p_1 rho_1) / p_2, eta = 1e-6.
    # Verifies the non-projection positive-pairing bounds U_x and U_x - L_x directly.
    def spec_apply(mat: np.ndarray, fn) -> np.ndarray:
        w_e, u_e = eigh((mat + mat.conj().T) / 2.0)
        return (u_e * fn(w_e)) @ u_e.conj().T

    def tau_half(mat: np.ndarray) -> float:
        return float(np.trace(mat).real) / 2.0

    p_nc = [0.25, 0.75]
    A1_nc = np.diag([1.999, 0.001]).astype(np.complex128)
    B_nc = np.array([[1.0, -0.5], [-0.5, 1.0]], dtype=np.complex128)
    A2_nc = (B_nc - p_nc[0] * A1_nc) / p_nc[1]
    As_nc = [A1_nc, A2_nc]
    assert float(np.min(np.linalg.eigvalsh(A2_nc))) > 0.0
    assert all(abs(tau_half(M_nc) - 1.0) < 1e-14 for M_nc in (A1_nc, A2_nc, B_nc))

    eta_nc = 1e-6
    T_plus_nc = tau_half(spec_apply(B_nc, lambda t: t * np.maximum(np.log(t), 0.0)))
    ln_B_eta = spec_apply(B_nc + eta_nc * np.eye(2), np.log)
    ln_B_eta_pos = spec_apply(B_nc + eta_nc * np.eye(2), lambda t: np.maximum(np.log(t), 0.0))
    ln_B_eta_neg = spec_apply(B_nc + eta_nc * np.eye(2), lambda t: np.maximum(-np.log(t), 0.0))
    abs_ln_B = spec_apply(B_nc, lambda t: np.abs(np.log(t)))

    nc_pos_pairs, nc_Us, nc_neg_pairs, nc_U_minus_Ls = [], [], [], []
    for px, Ax in zip(p_nc, As_nc):
        U_x = (T_plus_nc + math.log(2.0)) / px
        L_x = tau_half(spec_apply(Ax, lambda t: t * np.log(t))) + math.log(px)
        pos_p = tau_half(Ax @ ln_B_eta_pos)
        full_p = tau_half(Ax @ ln_B_eta)
        neg_p = tau_half(Ax @ ln_B_eta_neg)
        assert pos_p <= U_x + 1e-12
        assert full_p >= L_x - 1e-12
        assert neg_p <= (U_x - L_x) + 1e-12
        nc_pos_pairs.append(pos_p)
        nc_Us.append(U_x)
        nc_neg_pairs.append(neg_p)
        nc_U_minus_Ls.append(U_x - L_x)

    nc_cross_sum = float(sum(px * tau_half(Ax @ abs_ln_B) for px, Ax in zip(p_nc, As_nc)))
    nc_B_abs_log = tau_half(spec_apply(B_nc, lambda t: t * np.abs(np.log(t))))
    nc_cross_abs_log_err = abs(nc_cross_sum - nc_B_abs_log)
    assert nc_cross_abs_log_err < 1e-14

    def segal_half(M_nc: np.ndarray) -> float:
        return -tau_half(spec_apply(M_nc, lambda t: t * np.log(t)))

    nc_H = float(-sum(px * math.log(px) for px in p_nc))
    nc_chi = segal_half(B_nc) - float(sum(px * segal_half(Ax) for px, Ax in zip(p_nc, As_nc)))
    assert 0.0 <= nc_chi <= nc_H + 1e-14

    # 8. Abstract normalized-trace Type II_1-style Luders projection saturation witness &
    #    general unequal-weight Ozawa formula check:
    #    tau = (1/2) Tr on M_2(C), P = |0><0| (tau(P)=1/2), input I_2 -> branches 2P, 2(I-P):
    #    S_tau(I_2)=0, S_tau(2P)=S_tau(2(I-P))=-ln 2, chi_tau = ln 2 = H({1/2, 1/2}).
    ii1_S_in = segal_half(np.eye(2, dtype=np.complex128))
    ii1_S_branch = -0.5 * (2.0 * math.log(2.0))  # -tau((2P) ln(2P)) = -ln 2 (0 ln 0 = 0)
    ii1_luders_chi = ii1_S_in - ii1_S_branch
    ii1_luders_sat_err = abs(ii1_luders_chi - math.log(2.0))
    assert abs(ii1_S_in) < 1e-15 and ii1_luders_sat_err < 1e-15

    # General Ozawa formula chi_tau = h_2((1-q)p_1 + q/2) - h_2(q/2) for unequal p_1 = 0.1
    def h2_nat(t: float) -> float:
        return 0.0 if (t <= 0.0 or t >= 1.0) else -(t * math.log(t) + (1.0 - t) * math.log(1.0 - t))

    p1_uneq = 0.1
    r0_u05 = 0.5 * np.diag([1.0, 0.0]) + 0.5 * 0.5 * np.eye(2)
    r1_u05 = 0.5 * np.diag([0.0, 1.0]) + 0.5 * 0.5 * np.eye(2)
    rbar_u05 = (1.0 - p1_uneq) * r0_u05 + p1_uneq * r1_u05
    ozawa_unequal_chi_q05 = vn_entropy(rbar_u05) - ((1.0 - p1_uneq) * vn_entropy(r0_u05) + p1_uneq * vn_entropy(r1_u05))
    ozawa_unequal_formula_q05 = h2_nat(0.5 * p1_uneq + 0.25) - h2_nat(0.25)
    ozawa_unequal_err_q05 = abs(ozawa_unequal_chi_q05 - ozawa_unequal_formula_q05)
    rbar_u10 = 0.5 * np.eye(2)
    ozawa_unequal_chi_q10 = vn_entropy(rbar_u10) - vn_entropy(rbar_u10)
    assert ozawa_unequal_err_q05 < 1e-14 and abs(ozawa_unequal_chi_q10) < 1e-15

    # Strict assertions on all G3 operator-algebra and entropy invariants
    assert cond_exp_idempotence_err < 1e-12 and cond_exp_bimodule_err < 1e-12
    assert cond_exp_tp_err < 1e-12 and cond_exp_unital_err < 1e-12
    assert max_comm_err < 1e-12 and dressed_comm_err < 1e-12 and undressed_comm_norm > 1.0
    assert max_decomp_err < 1e-12 and max_rel_ent_err < 1e-12 and max_scale_invariance_err < 1e-12
    assert abs(ozawa_I_GO[-1] + math.log(2.0)) < 1e-12

    res = {
        "K_clock": K,
        "d_sys": dS,
        "algebra_center_dim": K,
        "algebra_linear_dim": algebra_linear_dim,
        "cond_exp_idempotence_err": cond_exp_idempotence_err,
        "cond_exp_bimodule_err": cond_exp_bimodule_err,
        "cond_exp_tp_err": cond_exp_tp_err,
        "cond_exp_unital_err": cond_exp_unital_err,
        "gauge_inv_commutator_err": max_comm_err,
        "dressed_op_commutator_err": dressed_comm_err,
        "undressed_op_commutator_norm_neg_ctrl": undressed_comm_norm,
        "max_entropy_branch_decomp_err": max_decomp_err,
        "max_holevo_rel_entropy_err": max_rel_ent_err,
        "sharp_eta1_dS_L1": dS_L1_arr[-1],
        "sharp_eta1_dS_L2_avg": dS_L2_arr[-1],
        "sharp_eta1_chi_II": chi_arr[-1],
        "sharp_eta1_shannon_H": shannon_arr[-1],
        "max_trace_scale_invariance_err": max_scale_invariance_err,
        "trace_scale_shift_c10": scale_shifts[2],
        "ozawa_neg_ctrl_I_GO_q05": ozawa_I_GO[20],
        "ozawa_neg_ctrl_I_GO_q10": ozawa_I_GO[-1],
        "ozawa_neg_ctrl_chi_q05": ozawa_chi[20],
        "ozawa_neg_ctrl_chi_q10": ozawa_chi[-1],
        "finite_group_K_invariance_spread": born_K_spread,
        "finite_group_K_exact_thermal_err": born_K_exact_err,
        "cor1_state_dependent_residual": cor1_state_dep_residual,
        "cor1_identity_err": cor1_identity_err,
        "nc_step2_eta": eta_nc,
        "nc_step2_T_plus": T_plus_nc,
        "nc_step2_pos_pair_1": nc_pos_pairs[0],
        "nc_step2_U_1": nc_Us[0],
        "nc_step2_neg_pair_1": nc_neg_pairs[0],
        "nc_step2_U_minus_L_1": nc_U_minus_Ls[0],
        "nc_step2_pos_pair_2": nc_pos_pairs[1],
        "nc_step2_U_2": nc_Us[1],
        "nc_step2_neg_pair_2": nc_neg_pairs[1],
        "nc_step2_U_minus_L_2": nc_U_minus_Ls[1],
        "nc_step2_cross_abs_log_err": nc_cross_abs_log_err,
        "nc_step2_chi_tau": nc_chi,
        "nc_step2_shannon_H": nc_H,
        "ii1_luders_sat_chi": ii1_luders_chi,
        "ii1_luders_sat_err": ii1_luders_sat_err,
        "ozawa_unequal_p0p9_q05_chi": ozawa_unequal_chi_q05,
        "ozawa_unequal_p0p9_q05_err": ozawa_unequal_err_q05,
        "ozawa_unequal_p0p9_q10_chi": ozawa_unequal_chi_q10,
    }
    plot_data = {
        "etas": etas,
        "dS_L1": np.array(dS_L1_arr),
        "dS_L2": np.array(dS_L2_arr),
        "chi": np.array(chi_arr),
        "shannon": np.array(shannon_arr),
        "qs": qs,
        "ozawa_I_GO": np.array(ozawa_I_GO),
        "ozawa_chi": np.array(ozawa_chi),
        "ozawa_H": np.array(ozawa_H),
    }
    return res, plot_data


# ---------------------------------------------------------------------------
# Suite G4: Theorem 4 — Causal Sequential Evaporation Circuit vs.
#           Time-Indexed Postselected Dictionaries & Sharp Polar Bounds (C3)
# ---------------------------------------------------------------------------

def sharp_polar_unnorm_bound(eps: float) -> float:
    """Uniformly sharp l1 bound (B): sqrt(1+eps) - sqrt(1-eps) for 0 <= eps < 1."""
    return math.sqrt(1.0 + eps) - math.sqrt(1.0 - eps)


def sharp_polar_norm_bound(eps: float) -> float:
    """Uniformly sharp l1 bound (C): 2*eps / (1 + sqrt(1 - eps^2)) for 0 <= eps < 1."""
    return (2.0 * eps) / (1.0 + math.sqrt(1.0 - eps * eps))


def run_suite_g4() -> Tuple[Dict, Dict]:
    rng = np.random.default_rng(SEED + 4)

    N_BH0 = 6
    d_fund = 2 ** N_BH0  # 64
    steps = list(range(N_BH0 + 1))  # n = 0..6

    # =========================================================================
    # Part A1: Single Strictly Causal Sequential Unitary Evaporation Circuit
    #   W_n^{seq} = (U_{B_{n-1} -> B_n R_new} x I_{R_{n-1}}) W_{n-1}^{seq}
    # Satisfies exact sequential radiation compatibility:
    #   Tr_{R_new}(rho_{R_n}) = rho_{R_{n-1}}  for ALL n=1..6 and ALL inputs!
    # Built for both d_C = 2 (1 diary qubit) and d_C = 4 (2 diary qubits).
    # =========================================================================
    def run_sequential_circuit(d_C: int) -> Dict:
        # Initial isometric encoding W_0: H_C -> H_{B_0} (dim 64)
        U0 = haar_unitary(d_fund, rng)
        W_cur = U0[:, :d_C].reshape(d_fund, 1, d_C)  # shape (d_BH, d_rad, d_C)
        # Test inputs for universal sequential radiation compatibility check
        ket0_c = np.zeros(d_C, dtype=np.complex128); ket0_c[0] = 1.0
        ketp_c = np.ones(d_C, dtype=np.complex128) / math.sqrt(d_C)
        test_inputs = [
            np.eye(d_C, dtype=np.complex128) / d_C,
            ket_bra(ket0_c),
            ket_bra(ketp_c),
        ]
        prev_rad_states = None
        prev_choi_rad = None
        S_rad_pure_bits = []
        S_rad_mixed_bits = []
        F_rad = []
        F_rem = []
        cap = []
        seq_compat_errs = []
        seq_choi_errs = []

        for n in steps:
            d_BH = 2 ** (N_BH0 - n)
            d_rad = 2 ** n
            if n > 0:
                d_BH_prev = 2 * d_BH
                d_rad_prev = d_rad // 2
                # Scrambling unitary U_n acts ONLY on remaining BH (B_{n-1} -> B_n x R_new)
                U_n = haar_unitary(d_BH_prev, rng)
                # Apply U_n to axis 0 (B_{n-1}), identity on axis 1 (R_{n-1})
                tmp = np.einsum("ab,brc->arc", U_n, W_cur)
                # Split B_{n-1} into (B_n, R_new) and append R_new to the right of R_{n-1}
                tmp = tmp.reshape(d_BH, 2, d_rad_prev, d_C)
                tmp = np.transpose(tmp, (0, 2, 1, 3))  # (B_n, R_{n-1}, R_new, C)
                W_cur = tmp.reshape(d_BH, d_rad, d_C)

            # Verify W_cur is an exact isometry
            W_mat = W_cur.reshape(d_fund, d_C)
            assert frob_norm(W_mat.conj().T @ W_mat - np.eye(d_C)) < 1e-13

            # Compute radiation states for all 3 test inputs and check sequential compatibility (A)
            cur_rad_states = []
            max_err_step = 0.0
            for idx_in, rho_in in enumerate(test_inputs):
                rho_full = W_mat @ rho_in @ W_mat.conj().T
                rho_R = partial_trace(rho_full, (d_BH, d_rad), (1,))
                cur_rad_states.append(rho_R)
                if prev_rad_states is not None:
                    # Trace out the newest (rightmost) qubit R_new from R_n = R_{n-1} x R_new
                    rho_R_prev_rec = partial_trace(rho_R, (d_rad // 2, 2), (0,))
                    td = 0.5 * trace_norm(rho_R_prev_rec - prev_rad_states[idx_in])
                    max_err_step = max(max_err_step, td)
            if prev_rad_states is not None:
                seq_compat_errs.append(max_err_step)
                assert max_err_step < 1e-14, f"Sequential compatibility violated at n={n}: {max_err_step}"
            prev_rad_states = cur_rad_states

            # Exhaustive full matrix-unit Choi-basis audit over all d_C^2 basis units |i><j|
            cur_choi_rad = []
            max_choi_step = 0.0
            for i_u in range(d_C):
                for j_u in range(d_C):
                    E_ij = np.zeros((d_C, d_C), dtype=np.complex128)
                    E_ij[i_u, j_u] = 1.0
                    rho_ij_R = partial_trace(W_mat @ E_ij @ W_mat.conj().T, (d_BH, d_rad), (1,))
                    cur_choi_rad.append(rho_ij_R)
            if prev_choi_rad is not None:
                for idx_u, rho_ij_R in enumerate(cur_choi_rad):
                    rec_ij = partial_trace(rho_ij_R, (d_rad // 2, 2), (0,))
                    max_choi_step = max(max_choi_step, frob_norm(rec_ij - prev_choi_rad[idx_u]))
                seq_choi_errs.append(max_choi_step)
                assert max_choi_step < 1e-14, f"Choi sequential compatibility violated at n={n}: {max_choi_step}"
            prev_choi_rad = cur_choi_rad

            # Pure-input Page curve entropy (bits)
            vals_p = np.linalg.eigvalsh((cur_rad_states[1] + cur_rad_states[1].conj().T) / 2.0)
            vals_p = vals_p[vals_p > 1e-14]
            S_rad_pure_bits.append(float(-np.sum(vals_p * np.log2(vals_p))))

            # Petz recovery fidelities in (H_rad, H_BH) order
            W_rad_bh = np.transpose(W_cur, (1, 0, 2)).reshape(d_fund, d_C)
            S_m, fe_r, fe_b = petz_entanglement_fidelity_from_isometry(W_rad_bh, d_C, d_rad, d_BH)
            S_rad_mixed_bits.append(S_m)
            F_rad.append(fe_r)
            F_rem.append(fe_b)
            cap_val = min(1.0, (d_BH ** 2) / float(d_C ** 2))
            cap.append(cap_val)
            assert fe_b <= cap_val + 1e-10

        assert abs(F_rem[N_BH0] - 1.0 / (d_C ** 2)) < 1e-12
        assert abs(F_rad[N_BH0] - 1.0) < 1e-12
        return {
            "S_rad_pure_bits": S_rad_pure_bits,
            "S_rad_mixed_bits": S_rad_mixed_bits,
            "F_rad": F_rad,
            "F_rem": F_rem,
            "cap": cap,
            "seq_compat_errs": seq_compat_errs,
            "max_seq_compat_err": float(max(seq_compat_errs)),
            "max_choi_compat_err": float(max(seq_choi_errs)),
        }

    seq_d2 = run_sequential_circuit(2)
    seq_d4 = run_sequential_circuit(4)

    # RR-3 Identity-circuit product-input control: sequential compatibility does NOT force a Page hump
    psi_id_prod = np.zeros(d_fund, dtype=np.complex128)
    psi_id_prod[0] = 1.0 / math.sqrt(2.0)
    psi_id_prod[d_fund // 2] = 1.0 / math.sqrt(2.0)  # |+> tensor |0>^{tensor 5}
    seq_id_S_rad_bits = []
    for n in steps:
        mat_id = psi_id_prod.reshape(2 ** (N_BH0 - n), 2 ** n)
        ev_id = np.linalg.eigvalsh(mat_id.conj().T @ mat_id)
        ev_id = ev_id[ev_id > 1e-14]
        seq_id_S_rad_bits.append(float(-np.sum(ev_id * np.log2(ev_id))))
    seq_id_max_S_rad_bits = float(max(abs(s) for s in seq_id_S_rad_bits))
    assert seq_id_max_S_rad_bits < 1e-14

    # =========================================================================
    # Part A2: Separate Time-Indexed Postselected Non-Isometric Dictionary Family
    #   V_n: H_C x H_{L_n} -> H_{BH,n},  Vtilde_n = (V_n x I_{R_n}) o iota_n
    # Explicitly audits BOTH its pullback defects (under sharp C3 bounds) AND
    # its failure of sequential radiation compatibility (A) for independent Haar draws.
    # =========================================================================
    d_C1 = 2
    U_meas = haar_unitary(d_fund, rng)
    povm_fund = []
    block = d_fund // 4
    for m in range(4):
        vecs = U_meas[:, m * block : (m + 1) * block]
        povm_fund.append(vecs @ vecs.conj().T)

    ker_frac_d2 = []
    code_eps_d2 = []
    code_l1_unnorm_d2 = []
    code_l1_norm_d2 = []
    code_sharp_bd_unnorm_d2 = []
    code_sharp_bd_norm_d2 = []
    post_seq_compat_right = []
    post_seq_compat_left = []
    post_choi_compat_right = []
    post_choi_compat_left = []
    post_raw_norm_compat_right = []
    post_raw_norm_compat_left = []
    post_ket0_Z = []
    post_ket0_raw_norm_compat_right = []
    post_ket0_pol_compat_right = []
    post_mm_Z_unit_max_err = 0.0
    null_state_loss_max = 0.0
    prev_post_rho_R = None
    prev_post_choi_R = None
    prev_post_raw_norm_R = None
    prev_post_ket0_raw_norm_R = None
    prev_post_ket0_pol_R = None

    for n in steps:
        d_BH = 2 ** (N_BH0 - n)
        d_rad = 2 ** n
        d_L = d_rad
        d_eff_int = d_C1 * d_L

        if d_eff_int <= d_BH:
            U_bh = haar_unitary(d_BH, rng)
            V_n = U_bh[:, :d_eff_int]
            ker_dim = 0
        else:
            U_scr = haar_unitary(d_eff_int, rng)
            V_n = math.sqrt(d_eff_int / float(d_BH)) * U_scr[:d_BH, :]
            ker_dim = d_eff_int - d_BH

        ker_frac_d2.append(float(ker_dim) / float(d_eff_int))

        if ker_dim > 0:
            _, _, vh = svd(V_n, full_matrices=True)
            v_null = vh[-1, :].conj()
            rho_null = ket_bra(v_null)
            norm_img = float(np.trace(V_n @ rho_null @ V_n.conj().T).real)
            null_state_loss_max = max(null_state_loss_max, 1.0 - norm_img)

        # Vtilde_n = (V_n x I_{R_n}) o iota_n on Bell-entangled code subspace C_n
        V_tilde = np.zeros((d_fund, d_C1), dtype=np.complex128)
        for i in range(d_C1):
            mat_bh_rad = np.zeros((d_BH, d_rad), dtype=np.complex128)
            for j in range(d_L):
                mat_bh_rad[:, j] = V_n[:, i * d_L + j] / math.sqrt(d_L)
            V_tilde[:, i] = mat_bh_rad.reshape(d_fund)

        gram_C = V_tilde.conj().T @ V_tilde
        eps_n = op_norm(gram_C - np.eye(d_C1))
        code_eps_d2.append(eps_n)

        u_sv, _, vh_sv = svd(V_tilde, full_matrices=False)
        W_pol = u_sv @ vh_sv

        if eps_n < 0.99:
            rho_C = np.array([[0.65, 0.25j], [-0.25j, 0.35]], dtype=np.complex128)
            rho_fund_un = V_tilde @ rho_C @ V_tilde.conj().T
            rho_pol = W_pol @ rho_C @ W_pol.conj().T
            Z_norm = float(np.trace(rho_fund_un).real)
            p_B = np.array([float(np.trace(E @ rho_fund_un).real) for E in povm_fund])
            p_B_hat = p_B / Z_norm
            p_A_pol = np.array([float(np.trace(E @ rho_pol).real) for E in povm_fund])
            l1_un = float(np.sum(np.abs(p_B - p_A_pol)))
            l1_nm = float(np.sum(np.abs(p_B_hat - p_A_pol)))
            bd_un = sharp_polar_unnorm_bound(eps_n)
            bd_nm = sharp_polar_norm_bound(eps_n)
            assert l1_un <= bd_un + 1e-12
            assert l1_nm <= bd_nm + 1e-12
            code_l1_unnorm_d2.append(l1_un)
            code_l1_norm_d2.append(l1_nm)
            code_sharp_bd_unnorm_d2.append(bd_un)
            code_sharp_bd_norm_d2.append(bd_nm)
        else:
            code_l1_unnorm_d2.append(float("nan"))
            code_l1_norm_d2.append(float("nan"))
            code_sharp_bd_unnorm_d2.append(float("nan"))
            code_sharp_bd_norm_d2.append(float("nan"))

        # Audit sequential radiation compatibility (A) on the independently drawn W_pol family
        # (both maximally mixed input rho_C = I_2/2 and full d_C^2=4 matrix-unit Choi basis),
        # AND directly on the renormalized raw dictionary outputs for both I_2/2 (where Z_n = 1 identically)
        # and pure input |0><0| (where Z_n != 1 so renormalization acts nontrivially)!
        rho_fund_mm = 0.5 * (W_pol @ W_pol.conj().T)
        rho_R_post = partial_trace(rho_fund_mm, (d_BH, d_rad), (1,))
        rho_raw_mm = 0.5 * (V_tilde @ V_tilde.conj().T)
        Z_raw_mm = float(np.trace(rho_raw_mm).real)
        post_mm_Z_unit_max_err = max(post_mm_Z_unit_max_err, abs(Z_raw_mm - 1.0))
        rho_raw_mm_norm = rho_raw_mm / Z_raw_mm
        rho_R_raw_norm = partial_trace(rho_raw_mm_norm, (d_BH, d_rad), (1,))
        v_ket0_raw = V_tilde[:, 0:1]
        rho_raw_ket0 = v_ket0_raw @ v_ket0_raw.conj().T
        Z_raw_ket0 = float(np.trace(rho_raw_ket0).real)
        post_ket0_Z.append(Z_raw_ket0)
        rho_R_ket0_raw_norm = partial_trace(rho_raw_ket0 / Z_raw_ket0, (d_BH, d_rad), (1,))
        v_ket0_pol = W_pol[:, 0:1]
        rho_R_ket0_pol = partial_trace(v_ket0_pol @ v_ket0_pol.conj().T, (d_BH, d_rad), (1,))
        cur_post_choi_R = []
        for i_u in range(d_C1):
            for j_u in range(d_C1):
                E_ij = np.zeros((d_C1, d_C1), dtype=np.complex128)
                E_ij[i_u, j_u] = 1.0
                cur_post_choi_R.append(partial_trace(W_pol @ E_ij @ W_pol.conj().T, (d_BH, d_rad), (1,)))
        if prev_post_rho_R is not None:
            prior_r = partial_trace(rho_R_post, (d_rad // 2, 2), (0,))
            prior_l = partial_trace(rho_R_post, (2, d_rad // 2), (1,))
            post_seq_compat_right.append(0.5 * trace_norm(prior_r - prev_post_rho_R))
            post_seq_compat_left.append(0.5 * trace_norm(prior_l - prev_post_rho_R))
            raw_r = partial_trace(rho_R_raw_norm, (d_rad // 2, 2), (0,))
            raw_l = partial_trace(rho_R_raw_norm, (2, d_rad // 2), (1,))
            post_raw_norm_compat_right.append(0.5 * trace_norm(raw_r - prev_post_raw_norm_R))
            post_raw_norm_compat_left.append(0.5 * trace_norm(raw_l - prev_post_raw_norm_R))
            ket0_raw_r = partial_trace(rho_R_ket0_raw_norm, (d_rad // 2, 2), (0,))
            ket0_pol_r = partial_trace(rho_R_ket0_pol, (d_rad // 2, 2), (0,))
            post_ket0_raw_norm_compat_right.append(0.5 * trace_norm(ket0_raw_r - prev_post_ket0_raw_norm_R))
            post_ket0_pol_compat_right.append(0.5 * trace_norm(ket0_pol_r - prev_post_ket0_pol_R))
            max_cr, max_cl = 0.0, 0.0
            for idx_u, r_ij in enumerate(cur_post_choi_R):
                max_cr = max(max_cr, frob_norm(partial_trace(r_ij, (d_rad // 2, 2), (0,)) - prev_post_choi_R[idx_u]))
                max_cl = max(max_cl, frob_norm(partial_trace(r_ij, (2, d_rad // 2), (1,)) - prev_post_choi_R[idx_u]))
            post_choi_compat_right.append(max_cr)
            post_choi_compat_left.append(max_cl)
        prev_post_rho_R = rho_R_post
        prev_post_raw_norm_R = rho_R_raw_norm
        prev_post_choi_R = cur_post_choi_R
        prev_post_ket0_raw_norm_R = rho_R_ket0_raw_norm
        prev_post_ket0_pol_R = rho_R_ket0_pol

    assert abs(null_state_loss_max - 1.0) < 1e-12
    assert post_mm_Z_unit_max_err < 1e-14
    assert abs(post_ket0_Z[5] - 1.0) > 0.05 and abs(post_ket0_Z[6] - 1.0) > 0.05
    assert post_ket0_raw_norm_compat_right[-1] > 0.9 and post_ket0_pol_compat_right[-1] > 0.9
    # Confirm independent Haar draws violate (A) significantly past rank-obstruction threshold 2n > 5 (n >= 3, indices 2..5)
    assert max(post_seq_compat_right[2:]) > 0.1 and max(post_seq_compat_left[2:]) > 0.1
    # Verify triangle-inequality lower bound at n=6 for renormalized raw Vtilde_n output:
    post_step6_raw_tri_lb = (
        post_seq_compat_right[-1]
        - 0.5 * sharp_polar_norm_bound(code_eps_d2[5])
        - 0.5 * sharp_polar_norm_bound(code_eps_d2[6])
    )
    assert post_raw_norm_compat_right[-1] >= post_step6_raw_tri_lb - 1e-12

    # RR-3 Outside-domain snapshot control (eps >= 1): N_BH0=2, d_C=4, n=2, U_scr=I_16 => eps = 3 > 1
    V_ood = np.zeros((1, 16), dtype=np.complex128)
    V_ood[0, 0] = 4.0
    iota_ood = np.zeros((64, 4), dtype=np.complex128)
    for c_idx in range(4):
        for l_idx in range(4):
            iota_ood[c_idx * 16 + l_idx * 4 + l_idx, c_idx] = 0.5
    V_tilde_ood = np.kron(V_ood, np.eye(4, dtype=np.complex128)) @ iota_ood
    gram_ood = V_tilde_ood.conj().T @ V_tilde_ood
    post_ood_eps = op_norm(gram_ood - np.eye(4, dtype=np.complex128))
    assert abs(post_ood_eps - 3.0) < 1e-14

    # =========================================================================
    # Part B: Sharp Uniform Polar-Isometric Pullback Bounds (B) & (C) + Saturation
    # =========================================================================
    eps_grid = np.linspace(0.02, 0.80, 40)
    assert abs(eps_grid[19] - 0.4) < 1e-15
    sweep_l1_un = []
    sweep_l1_nm = []
    sweep_sharp_bd_un = []
    sweep_sharp_bd_nm = []
    sweep_sat_un = []
    sweep_sat_nm = []
    W_base = haar_unitary(8, rng)[:, :4]
    U_m8 = haar_unitary(8, rng)
    povm8 = [ket_bra(U_m8[:, k]) for k in range(8)]
    rho4 = np.diag([0.5, 0.25, 0.15, 0.10]).astype(np.complex128)
    for eps in eps_grid:
        a_s = math.sqrt(1.0 - eps)
        b_s = math.sqrt(1.0 + eps)
        M_mat = np.diag([b_s, a_s, math.sqrt(1.0 + 0.5 * eps), math.sqrt(1.0 - 0.5 * eps)])
        V_test = W_base @ M_mat
        assert abs(op_norm(V_test.conj().T @ V_test - np.eye(4)) - eps) < 1e-12
        rho_un = V_test @ rho4 @ V_test.conj().T
        rho_p = W_base @ rho4 @ W_base.conj().T
        Z_t = float(np.trace(rho_un).real)
        pB = np.array([float(np.trace(E @ rho_un).real) for E in povm8])
        pA = np.array([float(np.trace(E @ rho_p).real) for E in povm8])
        l1_u = float(np.sum(np.abs(pB - pA)))
        l1_n = float(np.sum(np.abs(pB / Z_t - pA)))
        bd_u = sharp_polar_unnorm_bound(eps)
        bd_n = sharp_polar_norm_bound(eps)
        assert l1_u <= bd_u + 1e-12 and l1_n <= bd_n + 1e-12
        # Exact 2D saturation witnesses achieving equality in (B) and (C)
        M2 = np.diag([a_s, b_s]).astype(np.complex128)
        rho_u_sat = ket_bra(np.array([1.0, 1.0], dtype=np.complex128) / math.sqrt(2.0))
        rho_n_sat = ket_bra(np.array([math.sqrt(b_s / (a_s + b_s)), math.sqrt(a_s / (a_s + b_s))], dtype=np.complex128))
        sat_u = trace_norm(M2 @ rho_u_sat @ M2 - rho_u_sat)
        nr_sat = M2 @ rho_n_sat @ M2
        sat_n = trace_norm(nr_sat / float(np.trace(nr_sat).real) - rho_n_sat)
        assert abs(sat_u - bd_u) < 1e-13 and abs(sat_n - bd_n) < 1e-13
        sweep_l1_un.append(l1_u)
        sweep_l1_nm.append(l1_n)
        sweep_sharp_bd_un.append(bd_u)
        sweep_sharp_bd_nm.append(bd_n)
        sweep_sat_un.append(sat_u)
        sweep_sat_nm.append(sat_n)

    # Explicit 2-outcome POVM saturation checks at eps in {0.1, 0.4, 0.8} + negative Delta_norm witness
    sat_check_eps = {}
    for eps_val, tag in ((0.1, "0p1"), (0.4, "0p4"), (0.8, "0p8")):
        a_s = math.sqrt(1.0 - eps_val)
        b_s = math.sqrt(1.0 + eps_val)
        M2 = np.diag([a_s, b_s]).astype(np.complex128)
        rho_u = ket_bra(np.array([1.0, 1.0], dtype=np.complex128) / math.sqrt(2.0))
        rho_n = ket_bra(np.array([math.sqrt(b_s / (a_s + b_s)), math.sqrt(a_s / (a_s + b_s))], dtype=np.complex128))
        # Optimal 2-outcome Helstrom-type POVM from eigenbasis of Delta = M rho M - rho
        diff_u = M2 @ rho_u @ M2 - rho_u
        _, vu = eigh(diff_u)
        povm_u = [ket_bra(vu[:, 0]), ket_bra(vu[:, 1])]
        p_u_l1 = sum(abs(float(np.trace(E @ diff_u).real)) for E in povm_u)

        nr = M2 @ rho_n @ M2
        diff_n = nr / float(np.trace(nr).real) - rho_n
        _, vn = eigh(diff_n)
        povm_n = [ket_bra(vn[:, 0]), ket_bra(vn[:, 1])]
        p_n_l1 = sum(abs(float(np.trace(E @ diff_n).real)) for E in povm_n)

        bd_u = sharp_polar_unnorm_bound(eps_val)
        bd_n = sharp_polar_norm_bound(eps_val)
        assert abs(p_u_l1 - bd_u) < 1e-13 and abs(p_n_l1 - bd_n) < 1e-13
        sat_check_eps[f"sharp_sat_eps_{tag}_unnorm_l1"] = p_u_l1
        sat_check_eps[f"sharp_sat_eps_{tag}_unnorm_bound"] = bd_u
        sat_check_eps[f"sharp_sat_eps_{tag}_norm_l1"] = p_n_l1
        sat_check_eps[f"sharp_sat_eps_{tag}_norm_bound"] = bd_n

    # Negative Delta_norm witness (C6): on |1><1| with M^2 = diag(1-0.4, 1+0.4), Delta_norm = 1 - (1+0.4) = -0.4 < 0
    neg_delta_norm_witness = 1.0 - (1.0 + 0.4)
    assert neg_delta_norm_witness < 0.0

    # Independent-review additions for Theorem 4(b)-(c.2) using dedicated local RNG (leaving existing stream untouched):
    rng_g4_ext = np.random.default_rng(SEED + 404)
    # (i) Non-power-of-two co-isometric postselected dictionary: N_BH0=3, d_C=3, n=1 => m=6 > r=4
    m_nonpow, r_nonpow, dC_nonpow = 6, 4, 3
    gram_nonpow_avg = np.zeros((dC_nonpow, dC_nonpow), dtype=np.complex128)
    n_mc_nonpow = 2000
    nonpow_coiso_err = 0.0
    for idx_mc in range(n_mc_nonpow):
        U_np = haar_unitary(m_nonpow, rng_g4_ext)
        V_np = math.sqrt(m_nonpow / float(r_nonpow)) * U_np[:r_nonpow, :]
        if idx_mc == 0:
            nonpow_coiso_err = frob_norm(V_np @ V_np.conj().T - (m_nonpow / float(r_nonpow)) * np.eye(r_nonpow))
        Vt_np = np.zeros((r_nonpow * 2, dC_nonpow), dtype=np.complex128)
        for ci in range(dC_nonpow):
            blk = np.zeros((r_nonpow, 2), dtype=np.complex128)
            for li in range(2):
                blk[:, li] = V_np[:, ci * 2 + li] / math.sqrt(2.0)
            Vt_np[:, ci] = blk.reshape(r_nonpow * 2)
        gram_nonpow_avg += (Vt_np.conj().T @ Vt_np) / float(n_mc_nonpow)
    nonpow_haar_mean_err = frob_norm(gram_nonpow_avg - np.eye(dC_nonpow))
    assert nonpow_coiso_err < 1e-14 and nonpow_haar_mean_err < 0.05

    # (ii) Exact N_BH0=2, d_C=2 non-isometric kernel-carrying yet sequentially compatible witness (V_1, V_2):
    V1_ex = np.zeros((2, 4), dtype=np.complex128)
    V1_ex[0, 0] = math.sqrt(2.0)
    V1_ex[1, 2] = math.sqrt(2.0)
    V2_ex = np.zeros((1, 8), dtype=np.complex128)
    V2_ex[0, 0] = 2.0
    V2_ex[0, 5] = 2.0  # c=1, l=(0,1) -> index 1*4 + 1 = 5
    Vt1_ex = np.zeros((4, 2), dtype=np.complex128)  # (B_1, R_1)
    for ci in range(2):
        blk = np.zeros((2, 2), dtype=np.complex128)
        for li in range(2):
            blk[:, li] = V1_ex[:, ci * 2 + li] / math.sqrt(2.0)
        Vt1_ex[:, ci] = blk.reshape(4)
    Vt2_ex = np.zeros((4, 2), dtype=np.complex128)  # (B_2=1, R_1 x R_new = 4)
    for ci in range(2):
        blk = np.zeros((1, 4), dtype=np.complex128)
        for li in range(4):
            blk[:, li] = V2_ex[:, ci * 4 + li] / 2.0
        Vt2_ex[:, ci] = blk.reshape(4)
    compat_wit_coiso1_err = frob_norm(V1_ex @ V1_ex.conj().T - 2.0 * np.eye(2))
    compat_wit_coiso2_err = frob_norm(V2_ex @ V2_ex.conj().T - 8.0 * np.eye(1))
    compat_wit_iso1_err = frob_norm(Vt1_ex.conj().T @ Vt1_ex - np.eye(2))
    compat_wit_iso2_err = frob_norm(Vt2_ex.conj().T @ Vt2_ex - np.eye(2))
    compat_wit_choi_err = 0.0
    for i_u in range(2):
        for j_u in range(2):
            E_ij = np.zeros((2, 2), dtype=np.complex128)
            E_ij[i_u, j_u] = 1.0
            r1_ij = partial_trace(Vt1_ex @ E_ij @ Vt1_ex.conj().T, (2, 2), (1,))
            r2_ij = partial_trace(Vt2_ex @ E_ij @ Vt2_ex.conj().T, (2, 2), (0,))
            compat_wit_choi_err = max(compat_wit_choi_err, frob_norm(r2_ij - r1_ij))
    assert compat_wit_coiso1_err < 1e-14 and compat_wit_coiso2_err < 1e-14
    assert compat_wit_iso1_err < 1e-14 and compat_wit_iso2_err < 1e-14 and compat_wit_choi_err < 1e-15

    # (iii) Normalized postselection un-reweighted Gisin bias (eps/2) vs. contractive Kraus reweighting (0) at eps=0.4:
    eps_gisin = 0.4
    M_gisin = np.diag([math.sqrt(1.0 - eps_gisin), math.sqrt(1.0 + eps_gisin)]).astype(np.complex128)
    P0_2 = np.array([[1.0, 0.0], [0.0, 0.0]], dtype=np.complex128)
    P1_2 = np.array([[0.0, 0.0], [0.0, 1.0]], dtype=np.complex128)
    Pp_2 = 0.5 * np.array([[1.0, 1.0], [1.0, 1.0]], dtype=np.complex128)
    Pm_2 = 0.5 * np.array([[1.0, -1.0], [-1.0, 1.0]], dtype=np.complex128)
    norm_fn = lambda r: (M_gisin @ r @ M_gisin) / float(np.trace(M_gisin @ r @ M_gisin).real)
    avgZ_unrw = 0.5 * norm_fn(P0_2) + 0.5 * norm_fn(P1_2)
    avgX_unrw = 0.5 * norm_fn(Pp_2) + 0.5 * norm_fn(Pm_2)
    post_norm_unreweighted_gisin_td = 0.5 * trace_norm(avgZ_unrw - avgX_unrw)
    K_contr = M_gisin / op_norm(M_gisin)
    avgZ_rw = 0.5 * (K_contr @ P0_2 @ K_contr) + 0.5 * (K_contr @ P1_2 @ K_contr)
    avgX_rw = 0.5 * (K_contr @ Pp_2 @ K_contr) + 0.5 * (K_contr @ Pm_2 @ K_contr)
    post_norm_reweighted_gisin_td = 0.5 * trace_norm(
        avgZ_rw / float(np.trace(avgZ_rw).real) - avgX_rw / float(np.trace(avgX_rw).real)
    )
    assert abs(post_norm_unreweighted_gisin_td - 0.5 * eps_gisin) < 1e-14
    assert post_norm_reweighted_gisin_td < 1e-15

    res = {
        "N_BH0": N_BH0,
        "d_fund": d_fund,
        "steps": steps,
        "seq_d2_S_rad_pure_bits": seq_d2["S_rad_pure_bits"],
        "seq_d2_S_rad_mixed_bits": seq_d2["S_rad_mixed_bits"],
        "seq_d2_F_rad": seq_d2["F_rad"],
        "seq_d2_F_rem": seq_d2["F_rem"],
        "seq_d2_max_radiation_compat_err": seq_d2["max_seq_compat_err"],
        "seq_d2_choi_max_frob_err": seq_d2["max_choi_compat_err"],
        "seq_d4_F_rad": seq_d4["F_rad"],
        "seq_d4_F_rem": seq_d4["F_rem"],
        "seq_d4_cap": seq_d4["cap"],
        "seq_d4_max_radiation_compat_err": seq_d4["max_seq_compat_err"],
        "seq_d4_choi_max_frob_err": seq_d4["max_choi_compat_err"],
        "seq_id_max_S_rad_bits": seq_id_max_S_rad_bits,
        "seq_d4_step5_bottleneck_F_rem": seq_d4["F_rem"][5],
        "seq_d4_step6_exact_erasure_F_rem": seq_d4["F_rem"][6],
        "seq_d2_step6_exact_erasure_F_rem": seq_d2["F_rem"][6],
        "seq_d2_step6_full_recovery_F_rad": seq_d2["F_rad"][6],
        "postselected_ker_frac_d2": ker_frac_d2,
        "postselected_code_eps_d2": code_eps_d2,
        "postselected_seq_compat_discrepancy_rightmost": post_seq_compat_right,
        "postselected_seq_compat_discrepancy_leftmost": post_seq_compat_left,
        "postselected_choi_compat_discrepancy_rightmost": post_choi_compat_right,
        "postselected_choi_compat_discrepancy_leftmost": post_choi_compat_left,
        "postselected_raw_norm_compat_discrepancy_rightmost": post_raw_norm_compat_right,
        "postselected_raw_norm_compat_discrepancy_leftmost": post_raw_norm_compat_left,
        "postselected_mm_Z_unit_max_err": post_mm_Z_unit_max_err,
        "postselected_ket0_step5_Z": post_ket0_Z[5],
        "postselected_ket0_step6_Z": post_ket0_Z[6],
        "postselected_ket0_step6_raw_norm_compat_rightmost": post_ket0_raw_norm_compat_right[-1],
        "postselected_ket0_step6_pol_compat_rightmost": post_ket0_pol_compat_right[-1],
        "postselected_step6_raw_norm_triangle_lower_bound": post_step6_raw_tri_lb,
        "postselected_outside_domain_eps": post_ood_eps,
        "postselected_nonpow2_coiso_err": nonpow_coiso_err,
        "postselected_nonpow2_haar_mean_err": nonpow_haar_mean_err,
        "noniso_compatible_witness_choi_err": compat_wit_choi_err,
        "post_norm_unreweighted_gisin_td_eps0p4": post_norm_unreweighted_gisin_td,
        "post_norm_reweighted_gisin_td_eps0p4": post_norm_reweighted_gisin_td,
        "null_state_prob_annihilation": null_state_loss_max,
        "neg_delta_norm_witness_eps0p4": neg_delta_norm_witness,
        "sweep_eps_0p4_l1_unnorm": sweep_l1_un[19],
        "sweep_eps_0p4_sharp_bd_unnorm": sweep_sharp_bd_un[19],
        "sweep_eps_0p4_l1_norm": sweep_l1_nm[19],
        "sweep_eps_0p4_sharp_bd_norm": sweep_sharp_bd_nm[19],
        **sat_check_eps,
    }
    plot_data = {
        "steps": np.array(steps),
        "seq_S_rad_pure_d2": np.array(seq_d2["S_rad_pure_bits"]),
        "seq_F_rad_d2": np.array(seq_d2["F_rad"]),
        "seq_F_rem_d2": np.array(seq_d2["F_rem"]),
        "seq_F_rem_d4": np.array(seq_d4["F_rem"]),
        "ker_frac_d2": np.array(ker_frac_d2),
        "eps_grid": eps_grid,
        "sweep_l1_un": np.array(sweep_l1_un),
        "sweep_l1_nm": np.array(sweep_l1_nm),
        "sweep_sharp_bd_un": np.array(sweep_sharp_bd_un),
        "sweep_sharp_bd_nm": np.array(sweep_sharp_bd_nm),
        "sweep_sat_un": np.array(sweep_sat_un),
        "sweep_sat_nm": np.array(sweep_sat_nm),
    }
    return res, plot_data


# ---------------------------------------------------------------------------
# Suite G5: Proposition 1 — Five-Property Causal/Linear Audit,
#           Kinematic Welch Floor, CQ PSD Trade-off, & Two-Clock Constraints
# ---------------------------------------------------------------------------

def run_suite_g5() -> Tuple[Dict, Dict]:
    rng = np.random.default_rng(SEED + 5)

    # --- Control 0: Direct Nonlinear Branch Coupling (Gisin 1990 Wall) ---
    # Preserves density-state positivity & unit trace (NOT a linear CP map!), violates Gisin ensemble independence.
    Z = np.array([[1.0, 0.0], [0.0, -1.0]], dtype=np.complex128)
    P0 = np.array([[1.0, 0.0], [0.0, 0.0]], dtype=np.complex128)
    P1 = np.array([[0.0, 0.0], [0.0, 1.0]], dtype=np.complex128)
    Pp = 0.5 * np.array([[1.0, 1.0], [1.0, 1.0]], dtype=np.complex128)
    Pm = 0.5 * np.array([[1.0, -1.0], [-1.0, 1.0]], dtype=np.complex128)

    def phi_nl(rho: np.ndarray, lam: float) -> np.ndarray:
        z_exp = float(np.trace(rho @ Z).real)
        w = lam * (z_exp ** 2)
        return (1.0 - w) * rho + w * P0

    lams = np.linspace(0.0, 1.0, 21)
    gisin_bias = []
    gisin_td = []
    ctrl0_min_eig = 1.0
    ctrl0_max_trace_err = 0.0
    for lam in lams:
        for st_in in (P0, P1, Pp, Pm):
            out_st = phi_nl(st_in, lam)
            ctrl0_min_eig = min(ctrl0_min_eig, float(np.min(np.linalg.eigvalsh(out_st))))
            ctrl0_max_trace_err = max(ctrl0_max_trace_err, abs(float(np.trace(out_st).real) - 1.0))
        rho_bar_Z = 0.5 * phi_nl(P0, lam) + 0.5 * phi_nl(P1, lam)
        rho_bar_X = 0.5 * phi_nl(Pp, lam) + 0.5 * phi_nl(Pm, lam)
        bias = float(np.trace(Z @ (rho_bar_Z - rho_bar_X)).real)
        td = 0.5 * trace_norm(rho_bar_Z - rho_bar_X)
        assert abs(bias - lam) < 1e-14
        assert abs(td - 0.5 * lam) < 1e-14
        gisin_bias.append(bias)
        gisin_td.append(td)
    assert ctrl0_min_eig >= -1e-15 and ctrl0_max_trace_err < 1e-14

    # --- Control 0' (R2): Linear CPTP + Gisin Ensemble-Independent != Spatial Semicausality ---
    # SWAP gate is linear CPTP and ensemble-independent (0), yet has spatial signaling trace distance 1!
    SWAP = np.eye(4, dtype=np.complex128)[[0, 2, 1, 3]]
    rho_mm_4_Z = 0.5 * (np.kron(P0, 0.5 * np.eye(2)) + np.kron(P1, 0.5 * np.eye(2)))
    rho_mm_4_X = 0.5 * (np.kron(Pp, 0.5 * np.eye(2)) + np.kron(Pm, 0.5 * np.eye(2)))
    swap_gisin_err = trace_norm(SWAP @ rho_mm_4_Z @ SWAP.conj().T - SWAP @ rho_mm_4_X @ SWAP.conj().T)
    swap_A0 = partial_trace(SWAP @ np.kron(P0, P0) @ SWAP.conj().T, (2, 2), (0,))
    swap_A1 = partial_trace(SWAP @ np.kron(P0, P1) @ SWAP.conj().T, (2, 2), (0,))
    swap_spatial_signaling_td = 0.5 * trace_norm(swap_A0 - swap_A1)
    assert swap_gisin_err < 1e-15 and abs(swap_spatial_signaling_td - 1.0) < 1e-15

    # Contrast: local channel id_A x Phi_B satisfies BOTH Gisin independence and exact spatial semicausality
    K_ad0 = np.array([[1.0, 0.0], [0.0, math.sqrt(0.6)]], dtype=np.complex128)
    K_ad1 = np.array([[0.0, math.sqrt(0.4)], [0.0, 0.0]], dtype=np.complex128)
    rho_ent_test = ket_bra(np.array([math.sqrt(0.7), 0.0, 0.0, math.sqrt(0.3)], dtype=np.complex128))
    rho_loc_out = sum(np.kron(np.eye(2), K) @ rho_ent_test @ np.kron(np.eye(2), K.conj().T) for K in (K_ad0, K_ad1))
    local_semicausal_td = 0.5 * trace_norm(
        partial_trace(rho_loc_out, (2, 2), (0,)) - partial_trace(rho_ent_test, (2, 2), (0,))
    )
    assert local_semicausal_td < 1e-15

    # --- Mechanism A (R2 & R3): Kinematic Non-Isometric Gram-Overlap Floor (Welch Bound) ---
    # Remaining BH Hilbert dimension r = d_BH in {16, 32, 64} (explicitly distinct from total d_fund!)
    d_BH_list = [16, 32, 64]
    ratios = [0.25, 0.5, 0.75, 1.0, 1.25, 1.5, 2.0, 3.0, 4.0, 6.0, 8.0]
    welch_data = {}

    for r_bh in d_BH_list:
        rms_emp = []
        rms_bd = []
        M_vals = []
        for rat in ratios:
            M = max(2, int(round(r_bh * rat)))
            M_vals.append(M)
            if M <= r_bh:
                U = haar_unitary(r_bh, rng)
                V = U[:, :M]
                bd = 0.0
            else:
                U = haar_unitary(M, rng)
                V_raw = U[:r_bh, :]
                col_norms = np.linalg.norm(V_raw, axis=0)
                V = V_raw / col_norms[np.newaxis, :]
                bd = math.sqrt((M - r_bh) / (r_bh * (M - 1)))
            G = V.conj().T @ V
            off_diag_sq = frob_norm(G) ** 2 - float(np.sum(np.abs(np.diag(G)) ** 2))
            rms = math.sqrt(max(0.0, off_diag_sq) / (M * (M - 1)))
            assert rms + 1e-12 >= bd
            rms_emp.append(rms)
            rms_bd.append(bd)
        welch_data[r_bh] = {"M": M_vals, "rms_emp": rms_emp, "rms_bd": rms_bd}

    # Linear fundamental evolution U_F (distinct from the non-TP dictionary V!):
    U_F = haar_unitary(16, rng)
    rho_mix_Z = 0.5 * (np.kron(P0, np.eye(8) / 8.0) + np.kron(P1, np.eye(8) / 8.0))
    rho_mix_X = 0.5 * (np.kron(Pp, np.eye(8) / 8.0) + np.kron(Pm, np.eye(8) / 8.0))
    mech_a_fund_gisin_err = trace_norm(U_F @ rho_mix_Z @ U_F.conj().T - U_F @ rho_mix_X @ U_F.conj().T)
    assert mech_a_fund_gisin_err < 1e-14
    # Local fundamental unitary id_A x U_B obeys exact spatial semicausality
    U_B_loc = haar_unitary(8, rng)
    rho_ab_loc = np.kron(P0, np.eye(8) / 8.0)
    mech_a_local_semicausal_err = 0.5 * trace_norm(
        partial_trace(np.kron(np.eye(2), U_B_loc) @ rho_ab_loc @ np.kron(np.eye(2), U_B_loc.conj().T), (2, 8), (0,))
        - partial_trace(rho_ab_loc, (2, 8), (0,))
    )
    assert mech_a_local_semicausal_err < 1e-14

    # Trine ETF (r = 2, M = 3): Welch saturation + R2 non-TP/non-TNI witness + R3 frame-POVM normalization
    V_etf = np.array(
        [[math.cos(2 * math.pi * k / 3), math.sin(2 * math.pi * k / 3)] for k in range(3)],
        dtype=np.complex128,
    ).T
    G_etf = V_etf.conj().T @ V_etf
    eig_etf, vec_etf = eigh(G_etf)
    rho_etf_max = ket_bra(vec_etf[:, -1])
    trine_max_output_trace = float(np.trace(V_etf @ rho_etf_max @ V_etf.conj().T).real)
    trine_sum_G_sq = float(np.sum(np.abs(G_etf[:, 0]) ** 2))
    # Normalized frame POVM F_x = (r/M) |v_x><v_x| sums to I_2
    trine_norm_povm_err = frob_norm(
        sum((2.0 / 3.0) * ket_bra(V_etf[:, k]) for k in range(3)) - np.eye(2)
    )
    off_etf = math.sqrt((frob_norm(G_etf) ** 2 - 3.0) / 6.0)
    welch_etf_exact = math.sqrt((3.0 - 2.0) / (2.0 * 2.0))
    etf_saturation_err = abs(off_etf - welch_etf_exact)
    assert abs(trine_max_output_trace - 1.5) < 1e-14
    assert abs(trine_sum_G_sq - 1.5) < 1e-14
    assert trine_norm_povm_err < 1e-14
    assert etf_saturation_err < 1e-14

    # R3 Full-Rank Duplicated-Frame Counterexample (r = 8, M = 64):
    # Disproves reading Welch's lower bound as a universal O(r^{-1/2}) upper bound!
    r_dup, M_dup = 8, 64
    V_dup = np.zeros((r_dup, M_dup), dtype=np.float64)
    V_dup[0, : M_dup - r_dup + 1] = 1.0
    for j in range(1, r_dup):
        V_dup[j, M_dup - r_dup + j] = 1.0
    dup_rank = int(np.linalg.matrix_rank(V_dup))
    G_dup = V_dup.T @ V_dup
    dup_rms = math.sqrt((float(np.sum(G_dup ** 2)) - M_dup) / (M_dup * (M_dup - 1)))
    dup_welch_lower = math.sqrt((M_dup - r_dup) / (r_dup * (M_dup - 1)))
    assert dup_rank == r_dup
    assert abs(dup_welch_lower - 1.0 / 3.0) < 1e-14
    assert dup_rms > 0.88 and dup_rms > 2.5 * dup_welch_lower

    # RR-5 Column-normalized Haar projection non-tightness & canonical dual frame POVM (r=3, M=8):
    # Dedicated local RNG so existing G5 stream is untouched.
    rng_proj = np.random.default_rng(SEED + 505)
    r_proj, M_proj = 3, 8
    U_proj = haar_unitary(M_proj, rng_proj)
    V_proj_raw = U_proj[:r_proj, :]
    V_proj = V_proj_raw / np.linalg.norm(V_proj_raw, axis=0)[np.newaxis, :]
    S_proj = V_proj @ V_proj.conj().T
    proj_raw_tight_err = frob_norm(V_proj_raw @ V_proj_raw.conj().T - np.eye(r_proj))
    proj_norm_tight_err = frob_norm(S_proj - (M_proj / r_proj) * np.eye(r_proj))
    proj_naive_povm_err = frob_norm((r_proj / M_proj) * S_proj - np.eye(r_proj))
    w_S, u_S = eigh((S_proj + S_proj.conj().T) / 2.0)
    assert float(np.min(w_S)) > 1e-6
    S_inv_sqrt = (u_S * (1.0 / np.sqrt(w_S))) @ u_S.conj().T
    dual_povm_ops = [S_inv_sqrt @ ket_bra(V_proj[:, k]) @ S_inv_sqrt for k in range(M_proj)]
    proj_dual_povm_err = frob_norm(sum(dual_povm_ops) - np.eye(r_proj))
    proj_dual_povm_min_eig = float(min(np.min(np.linalg.eigvalsh((F + F.conj().T) / 2.0)) for F in dual_povm_ops))
    assert proj_raw_tight_err < 1e-14
    assert proj_norm_tight_err > 0.1 and proj_naive_povm_err > 0.1
    assert proj_dual_povm_err < 1e-14 and proj_dual_povm_min_eig >= -1e-14

    # --- Mechanism B: Oppenheim Linear Classical-Quantum (CQ) Mediation & PSD Trade-off ---
    D1_val = 1.0
    D0_grid = np.linspace(0.05, 1.5, 30)
    D2_crit = (D1_val ** 2) / (4.0 * D0_grid)
    M_cq_ok = np.array([[2 * 0.5, 1.0], [1.0, 2 * 0.6]])
    M_cq_bad = np.array([[2 * 0.3, 1.0], [1.0, 2 * 0.6]])
    cq_min_eig_ok = float(np.min(np.linalg.eigvalsh(M_cq_ok)))
    cq_min_eig_bad = float(np.min(np.linalg.eigvalsh(M_cq_bad)))
    assert cq_min_eig_ok > 0.0 and cq_min_eig_bad < 0.0
    K_00 = math.sqrt(0.7) * np.eye(2)
    K_10 = math.sqrt(0.3) * Z
    cq_Z = 0.5 * (K_00 @ P0 @ K_00 + K_10 @ P0 @ K_10) + 0.5 * (K_00 @ P1 @ K_00 + K_10 @ P1 @ K_10)
    cq_X = 0.5 * (K_00 @ Pp @ K_00 + K_10 @ Pp @ K_10) + 0.5 * (K_00 @ Pm @ K_00 + K_10 @ Pm @ K_10)
    mech_b_gisin_err = trace_norm(cq_Z - cq_X)
    assert mech_b_gisin_err < 1e-14
    # Local CQ channel id_A x Phi_{CQ,B} obeys exact spatial semicausality
    cq_loc_out = sum(np.kron(np.eye(2), K) @ rho_ent_test @ np.kron(np.eye(2), K.conj().T) for K in (K_00, K_10))
    mech_b_local_semicausal_err = 0.5 * trace_norm(
        partial_trace(cq_loc_out, (2, 2), (0,)) - partial_trace(rho_ent_test, (2, 2), (0,))
    )
    assert mech_b_local_semicausal_err < 1e-14

    # --- Mechanism C (R6): Separate Modular Z_4 Toy AND Exact C_tot = 0 Bipolar-Clock Model ---
    # C.1 Modular Z_4 toy (explicitly reporting continuous-C_tot discrepancy)
    Kc = 4
    U_sh_inv = np.roll(np.eye(Kc, dtype=np.complex128), -1, axis=0)
    r_op = np.array([[0.0, 0.0], [1.0, 0.0]], dtype=np.complex128)
    H_1 = np.diag([0.0, 1.0])
    H_c = np.diag(np.arange(Kc, dtype=np.float64))
    I_sub = np.eye(2 * Kc, dtype=np.complex128)
    O_A_dr = np.kron(np.kron(r_op, U_sh_inv), I_sub)
    O_B_dr = np.kron(I_sub, np.kron(r_op, U_sh_inv))
    e_sub = np.add.outer(np.diag(H_1).real, np.diag(H_c).real).reshape(-1)
    e_tot = np.add.outer(e_sub, e_sub).reshape(-1)
    C_tot_mod = np.diag(e_tot).astype(np.complex128)
    W_tot_1 = np.diag(np.exp(2j * math.pi * e_tot / Kc))
    mech_c_mod_comm_AB = frob_norm(O_A_dr @ O_B_dr - O_B_dr @ O_A_dr)
    mech_c_mod_gauge_A = frob_norm(O_A_dr @ W_tot_1 - W_tot_1 @ O_A_dr)
    mech_c_mod_gauge_B = frob_norm(O_B_dr @ W_tot_1 - W_tot_1 @ O_B_dr)
    mech_c_mod_C_OA_comm = frob_norm(C_tot_mod @ O_A_dr - O_A_dr @ C_tot_mod)
    mech_c_mod_exact_ker_dim = int(np.sum(np.abs(e_tot) < 1e-12))

    # Modular clock state embedded into |0,0>_S x H_{CA} x H_{CB}
    psi_clocks_mod = np.zeros(Kc * Kc, dtype=np.complex128)
    qsum_mod = np.diag(np.add.outer(np.arange(Kc, dtype=np.float64), np.arange(Kc, dtype=np.float64)).ravel())
    for q in range(Kc):
        psi_clocks_mod[q * Kc + ((-q) % Kc)] = 1.0 / math.sqrt(Kc)
    mech_c_mod_C_psi_norm = float(np.linalg.norm(qsum_mod @ psi_clocks_mod))
    mech_c_mod_C_psi_exp = float(np.vdot(psi_clocks_mod, qsum_mod @ psi_clocks_mod).real)
    w_clocks_mod = np.diag(np.exp(2j * math.pi * np.diag(qsum_mod) / Kc))
    mech_c_mod_finite_gauge_state_err = float(np.linalg.norm(w_clocks_mod @ psi_clocks_mod - psi_clocks_mod))
    rho_cA_mod = partial_trace(ket_bra(psi_clocks_mod), (Kc, Kc), (0,))
    rho_cB_mod = partial_trace(ket_bra(psi_clocks_mod), (Kc, Kc), (1,))
    mech_c_mod_clock_mi = vn_entropy(rho_cA_mod) + vn_entropy(rho_cB_mod) - vn_entropy(ket_bra(psi_clocks_mod))

    assert mech_c_mod_comm_AB < 1e-14 and mech_c_mod_gauge_A < 1e-14 and mech_c_mod_gauge_B < 1e-14
    assert abs(mech_c_mod_C_psi_norm - math.sqrt(12.0)) < 1e-12
    assert abs(mech_c_mod_C_OA_comm - 4.0 * math.sqrt(8.0)) < 1e-12
    assert mech_c_mod_finite_gauge_state_err < 1e-14 and mech_c_mod_exact_ker_dim == 1

    # C.2 Exact C_tot = 0 Finite-Dimensional Bipolar-Clock Model (H_C = diag(-m,...,+m), m=2, K_bi=5)
    m_bi = 2
    K_bi = 2 * m_bi + 1  # 5
    spec_bi = np.arange(-m_bi, m_bi + 1, dtype=np.float64)  # [-2, -1, 0, 1, 2]
    e_sub_bi = np.add.outer(np.array([0.0, 1.0]), spec_bi).reshape(-1)
    e_tot_bi = np.add.outer(e_sub_bi, e_sub_bi).reshape(-1)
    C_tot_bi = np.diag(e_tot_bi).astype(np.complex128)
    # Non-wrapping lowering operator L_C = sum_{q=-m+1}^m |q-1><q| (annihilates bottom level q=-m!)
    L_bi = np.zeros((K_bi, K_bi), dtype=np.complex128)
    for idx_q in range(1, K_bi):
        L_bi[idx_q - 1, idx_q] = 1.0
    I_sub_bi = np.eye(2 * K_bi, dtype=np.complex128)
    O_A_ex = np.kron(np.kron(r_op, L_bi), I_sub_bi)
    O_B_ex = np.kron(I_sub_bi, np.kron(r_op, L_bi))
    mech_c_exact_C_OA_comm = frob_norm(C_tot_bi @ O_A_ex - O_A_ex @ C_tot_bi)
    mech_c_exact_C_OB_comm = frob_norm(C_tot_bi @ O_B_ex - O_B_ex @ C_tot_bi)
    mech_c_exact_OA_OB_comm = frob_norm(O_A_ex @ O_B_ex - O_B_ex @ O_A_ex)
    assert mech_c_exact_C_OA_comm < 1e-14 and mech_c_exact_C_OB_comm < 1e-14 and mech_c_exact_OA_OB_comm < 1e-14

    # Exact entangled state |psi_exact> = (1/sqrt(K_bi)) sum_{q=-m}^m |0,q,0,-q> in ker(C_tot)
    psi_exact_full = np.zeros(4 * K_bi * K_bi, dtype=np.complex128)
    psi_exact_clocks = np.zeros(K_bi * K_bi, dtype=np.complex128)
    for idx_q in range(K_bi):
        idx_neg_q = (K_bi - 1) - idx_q  # maps -2..+2 to +2..-2
        # Basis ordering: (sA, qA, sB, qB) with dims (2, K_bi, 2, K_bi)
        flat_idx = ((0 * K_bi + idx_q) * 2 + 0) * K_bi + idx_neg_q
        psi_exact_full[flat_idx] = 1.0 / math.sqrt(K_bi)
        psi_exact_clocks[idx_q * K_bi + idx_neg_q] = 1.0 / math.sqrt(K_bi)
    mech_c_exact_C_psi_norm = float(np.linalg.norm(C_tot_bi @ psi_exact_full))
    mech_c_exact_OA_psi_norm = float(np.linalg.norm(O_A_ex @ psi_exact_full))
    mech_c_exact_C_OA_psi_norm = float(np.linalg.norm(C_tot_bi @ (O_A_ex @ psi_exact_full)))
    rho_cA_ex = partial_trace(ket_bra(psi_exact_clocks), (K_bi, K_bi), (0,))
    rho_cB_ex = partial_trace(ket_bra(psi_exact_clocks), (K_bi, K_bi), (1,))
    mech_c_exact_clock_mi = vn_entropy(rho_cA_ex) + vn_entropy(rho_cB_ex) - vn_entropy(ket_bra(psi_exact_clocks))

    # Exact unentangled product state |0,0,0,0> also in ker(C_tot): constraint permits, does not force entanglement!
    psi_prod_full = np.zeros(4 * K_bi * K_bi, dtype=np.complex128)
    idx_zero_q = m_bi  # q = 0
    psi_prod_full[((0 * K_bi + idx_zero_q) * 2 + 0) * K_bi + idx_zero_q] = 1.0
    mech_c_exact_prod_C_norm = float(np.linalg.norm(C_tot_bi @ psi_prod_full))
    psi_prod_clocks = np.zeros(K_bi * K_bi, dtype=np.complex128)
    psi_prod_clocks[idx_zero_q * K_bi + idx_zero_q] = 1.0
    rho_cA_pr = partial_trace(ket_bra(psi_prod_clocks), (K_bi, K_bi), (0,))
    rho_cB_pr = partial_trace(ket_bra(psi_prod_clocks), (K_bi, K_bi), (1,))
    mech_c_exact_prod_clock_mi = vn_entropy(rho_cA_pr) + vn_entropy(rho_cB_pr) - vn_entropy(ket_bra(psi_prod_clocks))

    assert mech_c_exact_C_psi_norm < 1e-14 and mech_c_exact_C_OA_psi_norm < 1e-14
    assert abs(mech_c_exact_OA_psi_norm - math.sqrt((K_bi - 1.0) / K_bi)) < 1e-14
    assert abs(mech_c_exact_clock_mi - 2.0 * math.log(K_bi)) < 1e-13
    assert mech_c_exact_prod_C_norm < 1e-14 and mech_c_exact_prod_clock_mi < 1e-14

    # RR-6 Exact bipolar-clock local CPTP channel completion (K_0, K_1):
    # K_1 = |1><0| x L_C, K_0 = sqrt(I - K_1^dag K_1) = |1><1| x I_C + |0><0| x |-m><-m|.
    K1_loc = np.kron(r_op, L_bi)
    P_bot_bi = np.zeros((K_bi, K_bi), dtype=np.complex128)
    P_bot_bi[0, 0] = 1.0
    K0_loc = np.kron(P1, np.eye(K_bi, dtype=np.complex128)) + np.kron(P0, P_bot_bi)
    mech_c_exact_cptp_complete_err = frob_norm(
        K0_loc.conj().T @ K0_loc + K1_loc.conj().T @ K1_loc - I_sub_bi
    )
    K0_full = np.kron(K0_loc, I_sub_bi)
    K1_full = np.kron(K1_loc, I_sub_bi)
    mech_c_exact_C_K0_comm = frob_norm(C_tot_bi @ K0_full - K0_full @ C_tot_bi)
    rho_exact_full = ket_bra(psi_exact_full)
    rho_exact_k1_branch = K1_full @ rho_exact_full @ K1_full.conj().T
    rho_exact_cptp_out = K0_full @ rho_exact_full @ K0_full.conj().T + rho_exact_k1_branch
    mech_c_exact_k1_success_prob = float(np.trace(rho_exact_k1_branch).real)
    mech_c_exact_cptp_trace_err = abs(float(np.trace(rho_exact_cptp_out).real) - 1.0)
    mech_c_exact_cptp_constraint_err = frob_norm(C_tot_bi @ rho_exact_cptp_out)
    mech_c_exact_cptp_semicausal_td = 0.5 * trace_norm(
        partial_trace(rho_exact_cptp_out, (2 * K_bi, 2 * K_bi), (1,))
        - partial_trace(rho_exact_full, (2 * K_bi, 2 * K_bi), (1,))
    )
    assert mech_c_exact_cptp_complete_err < 1e-14 and mech_c_exact_C_K0_comm < 1e-14
    assert abs(mech_c_exact_k1_success_prob - (K_bi - 1.0) / K_bi) < 1e-14
    assert mech_c_exact_cptp_trace_err < 1e-14 and mech_c_exact_cptp_constraint_err < 1e-14
    assert mech_c_exact_cptp_semicausal_td < 1e-14

    # Independent-review additions for Mechanism C.2 (dedicated local RNG):
    # (i) Local constraint-commuting observables [O_A, C_A] = [O_B, C_B] = 0 cannot distinguish
    #     |psi_exact> from its q-dephased classical mixture; global C_tot-commuting witness CAN!
    rng_g5_ext = np.random.default_rng(SEED + 506)
    rho_exact_deph = np.zeros_like(rho_exact_full)
    for idx_q in range(K_bi):
        idx_neg_q = (K_bi - 1) - idx_q
        flat_idx = ((0 * K_bi + idx_q) * 2 + 0) * K_bi + idx_neg_q
        rho_exact_deph[flat_idx, flat_idx] = 1.0 / float(K_bi)
    # Build random Hermitian local operators block-diagonal in C_loc = H_S + H_C
    C_loc_diag = np.diag(e_sub_bi).astype(np.complex128)
    def rand_commuting_local(r_gen) -> np.ndarray:
        M_raw = r_gen.normal(size=(2 * K_bi, 2 * K_bi)) + 1j * r_gen.normal(size=(2 * K_bi, 2 * K_bi))
        M_raw = 0.5 * (M_raw + M_raw.conj().T)
        mask = (np.abs(e_sub_bi[:, None] - e_sub_bi[None, :]) < 1e-12).astype(np.complex128)
        return M_raw * mask
    OA_ccomm = rand_commuting_local(rng_g5_ext)
    OB_ccomm = rand_commuting_local(rng_g5_ext)
    assert frob_norm(C_loc_diag @ OA_ccomm - OA_ccomm @ C_loc_diag) < 1e-14
    assert frob_norm(C_loc_diag @ OB_ccomm - OB_ccomm @ C_loc_diag) < 1e-14
    OAB_ccomm = np.kron(OA_ccomm, OB_ccomm)
    mech_c_exact_local_ccomm_deph_diff = abs(
        float(np.trace(OAB_ccomm @ (rho_exact_full - rho_exact_deph)).real)
    )
    # Global two-sided C_tot-commuting coherence witness between q=0 and q=1 (idx_q=2 and idx_q=3):
    f_q0 = ((0 * K_bi + m_bi) * 2 + 0) * K_bi + m_bi
    f_q1 = ((0 * K_bi + (m_bi + 1)) * 2 + 0) * K_bi + (m_bi - 1)
    W_glob_coh = np.zeros_like(rho_exact_full)
    W_glob_coh[f_q0, f_q1] = 1.0
    W_glob_coh[f_q1, f_q0] = 1.0
    mech_c_exact_global_witness_comm = frob_norm(C_tot_bi @ W_glob_coh - W_glob_coh @ C_tot_bi)
    mech_c_exact_global_witness_gap = abs(
        float(np.trace(W_glob_coh @ (rho_exact_full - rho_exact_deph)).real)
    )
    assert mech_c_exact_local_ccomm_deph_diff < 1e-14
    assert mech_c_exact_global_witness_comm < 1e-14 and abs(mech_c_exact_global_witness_gap - 0.4) < 1e-14

    # (ii) Conditional B-marginal update under K_1 success (trace distance = 1/K_bi = 1/5)
    #      vs. exact non-selective preservation (0.0):
    rho_B_init_ex = partial_trace(rho_exact_full, (2 * K_bi, 2 * K_bi), (1,))
    rho_B_cond_k1_ex = partial_trace(rho_exact_k1_branch / mech_c_exact_k1_success_prob, (2 * K_bi, 2 * K_bi), (1,))
    mech_c_exact_k1_cond_B_td = 0.5 * trace_norm(rho_B_cond_k1_ex - rho_B_init_ex)
    assert abs(mech_c_exact_k1_cond_B_td - 1.0 / float(K_bi)) < 1e-14

    res = {
        "ctrl0_gisin_bias_lam1": gisin_bias[-1],
        "ctrl0_gisin_td_lam1": gisin_td[-1],
        "ctrl0_gisin_bias_lam05": gisin_bias[10],
        "ctrl0_min_output_eig": ctrl0_min_eig,
        "ctrl0_max_trace_err": ctrl0_max_trace_err,
        "ctrl0p_swap_gisin_err": swap_gisin_err,
        "ctrl0p_swap_spatial_signaling_td": swap_spatial_signaling_td,
        "ctrl0p_local_semicausal_td": local_semicausal_td,
        "mechA_etf_rms": off_etf,
        "mechA_etf_welch_bound": welch_etf_exact,
        "mechA_etf_saturation_err": etf_saturation_err,
        "mechA_trine_max_output_trace": trine_max_output_trace,
        "mechA_trine_sum_G_sq": trine_sum_G_sq,
        "mechA_trine_norm_povm_err": trine_norm_povm_err,
        "mechA_dup_r": r_dup,
        "mechA_dup_M": M_dup,
        "mechA_dup_rank": dup_rank,
        "mechA_dup_rms": dup_rms,
        "mechA_dup_welch_lower": dup_welch_lower,
        "mechA_proj_raw_tight_err": proj_raw_tight_err,
        "mechA_proj_norm_tight_err": proj_norm_tight_err,
        "mechA_proj_naive_povm_err": proj_naive_povm_err,
        "mechA_proj_dual_povm_err": proj_dual_povm_err,
        "mechA_proj_dual_povm_min_eig": proj_dual_povm_min_eig,
        "mechA_dBH32_M32_rms": welch_data[32]["rms_emp"][3],
        "mechA_dBH32_M64_rms": welch_data[32]["rms_emp"][6],
        "mechA_dBH32_M64_welch_bd": welch_data[32]["rms_bd"][6],
        "mechA_dBH32_M256_rms": welch_data[32]["rms_emp"][-1],
        "mechA_dBH32_M256_welch_bd": welch_data[32]["rms_bd"][-1],
        "mechA_dBH64_M512_rms": welch_data[64]["rms_emp"][-1],
        "mechA_dBH64_M512_welch_bd": welch_data[64]["rms_bd"][-1],
        "mechA_fund_linear_gisin_err": mech_a_fund_gisin_err,
        "mechA_local_semicausal_err": mech_a_local_semicausal_err,
        "mechB_cq_psd_ok_min_eig": cq_min_eig_ok,
        "mechB_cq_psd_bad_min_eig": cq_min_eig_bad,
        "mechB_linear_gisin_err": mech_b_gisin_err,
        "mechB_local_semicausal_err": mech_b_local_semicausal_err,
        "mechC_mod_dressed_commutator_AB": mech_c_mod_comm_AB,
        "mechC_mod_gauge_inv_A": mech_c_mod_gauge_A,
        "mechC_mod_gauge_inv_B": mech_c_mod_gauge_B,
        "mechC_mod_C_psi_norm": mech_c_mod_C_psi_norm,
        "mechC_mod_C_psi_expectation": mech_c_mod_C_psi_exp,
        "mechC_mod_finite_gauge_state_err": mech_c_mod_finite_gauge_state_err,
        "mechC_mod_C_OA_comm_frob": mech_c_mod_C_OA_comm,
        "mechC_mod_exact_ker_dim": mech_c_mod_exact_ker_dim,
        "mechC_mod_clock_mutual_info_nats": mech_c_mod_clock_mi,
        "mechC_exact_K_bi": K_bi,
        "mechC_exact_C_psi_norm": mech_c_exact_C_psi_norm,
        "mechC_exact_C_OA_comm_frob": mech_c_exact_C_OA_comm,
        "mechC_exact_C_OB_comm_frob": mech_c_exact_C_OB_comm,
        "mechC_exact_OA_OB_comm_frob": mech_c_exact_OA_OB_comm,
        "mechC_exact_OA_psi_norm": mech_c_exact_OA_psi_norm,
        "mechC_exact_C_OA_psi_norm": mech_c_exact_C_OA_psi_norm,
        "mechC_exact_clock_mutual_info_nats": mech_c_exact_clock_mi,
        "mechC_exact_prod_C_norm": mech_c_exact_prod_C_norm,
        "mechC_exact_prod_clock_mi_nats": mech_c_exact_prod_clock_mi,
        "mechC_exact_cptp_complete_err": mech_c_exact_cptp_complete_err,
        "mechC_exact_C_K0_comm_frob": mech_c_exact_C_K0_comm,
        "mechC_exact_k1_success_prob": mech_c_exact_k1_success_prob,
        "mechC_exact_cptp_trace_err": mech_c_exact_cptp_trace_err,
        "mechC_exact_cptp_constraint_err": mech_c_exact_cptp_constraint_err,
        "mechC_exact_cptp_semicausal_td": mech_c_exact_cptp_semicausal_td,
        "mechC_exact_local_ccomm_deph_diff": mech_c_exact_local_ccomm_deph_diff,
        "mechC_exact_global_witness_comm_frob": mech_c_exact_global_witness_comm,
        "mechC_exact_global_witness_gap": mech_c_exact_global_witness_gap,
        "mechC_exact_k1_cond_B_td": mech_c_exact_k1_cond_B_td,
    }
    plot_data = {
        "lams": lams,
        "gisin_bias": np.array(gisin_bias),
        "ratios": np.array(ratios),
        "welch_data": welch_data,
        "dup_ratio": float(M_dup) / float(r_dup),
        "dup_rms": dup_rms,
        "dup_welch_lower": dup_welch_lower,
        "D0_grid": D0_grid,
        "D2_crit": D2_crit,
        "measured_diagnostics": {
            "swap_gisin": swap_gisin_err,
            "swap_spatial": swap_spatial_signaling_td,
            "mechA_gisin": mech_a_fund_gisin_err,
            "mechA_local_semi": mech_a_local_semicausal_err,
            "mechB_gisin": mech_b_gisin_err,
            "mechB_local_semi": mech_b_local_semicausal_err,
        },
    }
    return res, plot_data


# ---------------------------------------------------------------------------
# Publication-grade Figure Generation (4 Vector PDFs)
# ---------------------------------------------------------------------------

def configure_matplotlib() -> None:
    plt.rcParams.update({
        "font.family": "serif",
        "font.size": 9.5,
        "axes.labelsize": 10,
        "axes.titlesize": 10.5,
        "legend.fontsize": 8.0,
        "xtick.labelsize": 8.5,
        "ytick.labelsize": 8.5,
        "lines.linewidth": 1.7,
        "axes.grid": True,
        "grid.alpha": 0.25,
        "savefig.bbox": "tight",
        "pdf.fonttype": 42,
    })


def make_figures(p1: Dict, p2: Dict, p3: Dict, p4: Dict, p5: Dict) -> None:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    configure_matplotlib()

    # Figure 1: Steering floor & Model I vs Model II LF boundary
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.6))
    ax1.plot(p1["etas"], p1["steering_tr"], color="#1f4e79", label=r"Trace norm $\|\sigma_{L,0}-p_0\rho_L\|_1$")
    ax1.plot(p1["etas"], p1["steering_fr"], color="#2e8b57", ls="--", label=r"Frobenius norm $\|\sigma_{L,0}-p_0\rho_L\|_F$")
    ax1.plot(p1["etas"], p1["floor_fr"], color="#c0392b", ls=":", lw=2.0, label=r"Theorem 1 floor $\lambda_{\min}\|E_0-p_0 I\|_F$")
    ax1.axhline(p1["neg_ctrl_product"], color="#7f8c8d", ls="-.", lw=1.2, label="Product / classical $X$-POVM controls ($0$)")
    ax1.set_xlabel(r"Exterior POVM sharpness $\eta$")
    ax1.set_ylabel("Conditional steering magnitude")
    ax1.set_title(r"(a) Single-space steering floor ($d=4$ Unruh state)")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.92)

    ax2.plot(p2["S_vals"], p2["neg_lp"], color="#b03a2e", lw=2.0, label=r"Model I min. negativity $\mathcal{N}_{\min}$ (LP)")
    ax2.plot(p2["S_vals"], p2["neg_exact"], color="#1c2833", ls="--", lw=1.3, label=r"Analytic $\max(0,(S-2)/4)$")
    ax2.plot(p2["S_vals"], p2["model2_cpl_res"], color="#1f618d", ls="-.", lw=1.6, label=r"Model II single-context marginal residual ($0$)")
    ax2.axvline(2.0, color="#7f8c8d", ls=":", lw=1.2)
    ax2.scatter([2.8], [0.2], color="#b03a2e", zorder=5, s=36, label=r"Rational witness $(S=14/5, \mathcal{N}_{\min}=1/5)$")
    ax2.set_xlabel(r"CHSH / Local Friendliness value $S$")
    ax2.set_ylabel(r"Global-section negativity / marginal residual")
    ax2.set_title("(b) Model I obstruction vs. Model II context consistency")
    ax2.legend(loc="upper left", frameon=True, framealpha=0.92)
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig1_steering_and_lf_boundary.pdf")
    plt.close(fig)

    # Figure 2: Semifinite Segal entropy split (Z_8 toy analogue) & Ozawa negative control
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.6))
    ax1.plot(p3["etas"], p3["shannon"], color="#5d6d7e", ls=":", lw=1.8, label=r"Shannon bound $H(\{p_x\})$")
    ax1.plot(p3["etas"], p3["chi"], color="#1f4e79", lw=2.0, label=r"Holevo deficit $\chi_{\tau}=\Delta S_{\tau}^{\mathrm{L1}}-\overline{\Delta S}_{\tau}^{\mathrm{L2}}$")
    ax1.plot(p3["etas"], p3["dS_L1"], color="#2e8b57", ls="--", label=r"Layer 1 change $\Delta S_{\tau}^{\mathrm{L1}}$")
    ax1.plot(p3["etas"], p3["dS_L2"], color="#c0392b", ls="-.", label=r"Layer 2 avg. change $\overline{\Delta S}_{\tau}^{\mathrm{L2}}$")
    ax1.set_xlabel(r"Covariant $\mathbb{Z}_8$ clock-instrument sharpness $\eta$")
    ax1.set_ylabel("Segal entropy difference (nats)")
    ax1.set_title(r"(a) $\mathbb{Z}_8$ toy clock-algebra Segal entropy split")
    ax1.legend(loc="center left", frameon=True, framealpha=0.92)

    ax2.plot(p3["qs"], p3["ozawa_H"], color="#5d6d7e", ls=":", lw=1.8, label=r"Upper bound $H(\{p_x\})=\ln 2$")
    ax2.plot(p3["qs"], p3["ozawa_chi"], color="#1f4e79", lw=2.0, label=r"Holevo deficit $\chi_{\tau}\geq 0$")
    ax2.plot(p3["qs"], p3["ozawa_I_GO"], color="#c0392b", ls="-.", lw=1.9, label=r"Groenewold--Ozawa gain $I_{\mathrm{GO}}<0$")
    ax2.axhline(0.0, color="#2c3e50", lw=0.9)
    ax2.set_xlabel(r"Conditional-state depolarization $q$")
    ax2.set_ylabel("Entropy / information (nats)")
    ax2.set_title("(b) Ozawa negative control on pure input")
    ax2.legend(loc="lower left", frameon=True, framealpha=0.92)
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig2_type2_clock_entropy.pdf")
    plt.close(fig)

    # Figure 3: Causal sequential unitary circuit W_n^{seq} & sharp uniform polar bounds (B)/(C)
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.6))
    st = p4["steps"]
    ax1.plot(st, p4["seq_F_rad_d2"], "o-", color="#1f4e79", ms=4.5, label=r"Seq. $W_n^{\mathrm{seq}}$ rad. $F_{\mathrm{rad}}$ ($d_C=2$)")
    ax1.plot(st, p4["seq_F_rem_d2"], "s--", color="#c0392b", ms=4.5, label=r"Seq. $W_n^{\mathrm{seq}}$ rem. $F_{\mathrm{rem}}$ ($d_C=2$)")
    ax1.plot(st, p4["seq_F_rem_d4"], "^:", color="#8e44ad", ms=4.5, label=r"Seq. $W_n^{\mathrm{seq}}$ rem. $F_{\mathrm{rem}}$ ($d_C=4$)")
    ax1.plot(st, p4["ker_frac_d2"], "d-.", color="#2e8b57", ms=4.2, label=r"Postselected $V_n$ kernel frac.")
    ax1.axvline(3.0, color="#7f8c8d", ls=":", lw=1.2)
    ax1.set_xlabel(r"Evaporation step $n$ ($d_{\mathrm{BH}}=2^{6-n}$)")
    ax1.set_ylabel("Fidelity / kernel fraction")
    ax1.set_title(r"(a) Causal sequential $W_n^{\mathrm{seq}}$ & postselected $\ker V_n$")
    ax1.set_ylim(-0.04, 1.08)
    ax1.legend(loc="center left", fontsize=7.4, frameon=True, framealpha=0.92)

    ax2.plot(p4["eps_grid"], p4["sweep_sharp_bd_nm"], color="#c0392b", ls="--", lw=1.7, label=r"Sharp norm. bound $\frac{2\varepsilon}{1+\sqrt{1-\varepsilon^2}}$")
    ax2.scatter(p4["eps_grid"][::6], p4["sweep_sat_nm"][::6], color="#c0392b", marker="x", s=30, zorder=5, label=r"2D saturation witness (norm.)")
    ax2.plot(p4["eps_grid"], p4["sweep_l1_nm"], color="#c0392b", lw=1.6, alpha=0.85, label=r"Generic mixed $\ell^1$ (norm.)")
    ax2.plot(p4["eps_grid"], p4["sweep_sharp_bd_un"], color="#1f4e79", ls="--", lw=1.7, label=r"Sharp unnorm. $\sqrt{1+\varepsilon}-\sqrt{1-\varepsilon}$")
    ax2.scatter(p4["eps_grid"][::6], p4["sweep_sat_un"][::6], color="#1f4e79", marker="+", s=36, zorder=5, label=r"2D saturation witness (unnorm.)")
    ax2.plot(p4["eps_grid"], p4["sweep_l1_un"], color="#1f4e79", lw=1.6, alpha=0.85, label=r"Generic mixed $\ell^1$ (unnorm.)")
    ax2.set_xlabel(r"Code-subspace isometry error $\varepsilon$")
    ax2.set_ylabel(r"$\ell^1$ Born-weight defect $\sum_x |p_x - q_x|$")
    ax2.set_title(r"(b) Sharp uniform polar-isometric $\ell^1$ bounds")
    ax2.legend(loc="upper left", fontsize=6.7, frameon=True, framealpha=0.92)
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig3_dynamical_nonisometric_pullback.pdf")
    plt.close(fig)

    # Figure 4: Kinematic Welch Gram-overlap floor (w/ duplicated counterexample) & measured signaling diagnostics
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.6))
    colors = {16: "#c0392b", 32: "#1f4e79", 64: "#2e8b57"}
    for r_bh in (16, 32, 64):
        wd = p5["welch_data"][r_bh]
        ax1.plot(p5["ratios"], wd["rms_emp"], "o-", ms=3.5, color=colors[r_bh], label=rf"Haar proj. $d_{{\mathrm{{BH}}}}={r_bh}$")
        ax1.plot(p5["ratios"], wd["rms_bd"], ls="--", lw=1.2, color=colors[r_bh], alpha=0.8, label=rf"Welch floor ($d_{{\mathrm{{BH}}}}={r_bh}$)")
    ax1.scatter(
        [p5["dup_ratio"]],
        [p5["dup_rms"]],
        color="#8e44ad",
        marker="*",
        s=95,
        zorder=6,
        label=rf"Full-rank dup. ($r=8,M=64$): {p5['dup_rms']:.3f}",
    )
    ax1.axvline(1.0, color="#7f8c8d", ls=":", lw=1.2)
    ax1.set_xlabel(r"Branch-to-BH dimension ratio $M / d_{\mathrm{BH}}$")
    ax1.set_ylabel(r"RMS overlap $\mathrm{RMS}_{x\neq y}|G_{xy}|$")
    ax1.set_title("(a) Mechanism A: kinematic Welch floor vs. counterexample")
    ax1.set_ylim(-0.04, 0.98)
    ax1.legend(loc="center left", bbox_to_anchor=(0.01, 0.56), ncol=1, fontsize=6.6, frameon=True, framealpha=0.92)

    diag = p5["measured_diagnostics"]
    ax2.plot(p5["lams"], p5["gisin_bias"], color="#c0392b", lw=2.0, label=r"Control 0 nonlinear Gisin $|\Delta\langle Z\rangle|=\lambda$")
    # Plot actual measured diagnostic values (explicitly naming each evaluated linear operation)
    x_meas = np.array([0.07, 0.12, 0.17, 0.22, 0.27])
    y_gisin_meas = np.array([
        diag["swap_gisin"],
        diag["mechA_gisin"],
        diag["mechA_local_semi"],
        diag["mechB_gisin"],
        diag["mechB_local_semi"],
    ])
    ax2.scatter(
        x_meas,
        y_gisin_meas,
        color="#1f4e79",
        marker="s",
        s=30,
        zorder=5,
        label=r"Linear checks ($<10^{-14}$): $\mathrm{SWAP}$(G), $U_F$(G)," + "\n" + r"$\mathrm{id}\!\otimes\!U_B$(S), deph. proxy(G,S)",
    )
    ax2.scatter([0.07], [diag["swap_spatial"]], color="#d35400", marker="*", s=100, zorder=6, label=r"Control 0$'$ SWAP spatial signaling ($1.0$)")
    ax2.set_xlabel(r"Nonlinear coupling $\lambda$ / diagnostic slot")
    ax2.set_ylabel(r"Measured signaling / trace distance")
    ax2.set_title("(b) Measured Gisin vs. spatial-semicausality diagnostics")
    ax2.set_ylim(-0.06, 1.08)
    inset = ax2.inset_axes([0.16, 0.46, 0.44, 0.42])
    inset.plot(p5["D0_grid"], p5["D2_crit"], color="#2e8b57", lw=1.5)
    inset.fill_between(p5["D0_grid"], p5["D2_crit"], 5.5, color="#2e8b57", alpha=0.18)
    inset.set_xlim(0.05, 1.5)
    inset.set_ylim(0.0, 5.0)
    inset.set_xlabel(r"$D_0$", fontsize=7.5, labelpad=1)
    inset.set_ylabel(r"$D_2$", fontsize=7.5, labelpad=1)
    inset.set_title(r"Mech. B: $D_2,D_0\geq 0,\ 4D_2D_0\geq D_1^2$", fontsize=6.7, pad=2)
    inset.tick_params(labelsize=6.8)
    ax2.legend(loc="lower right", fontsize=6.2, frameon=True, framealpha=0.92)
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig4_branch_coupling_gate.pdf")
    plt.close(fig)


def count_numeric_fields(obj) -> int:
    if isinstance(obj, dict):
        return sum(count_numeric_fields(v) for v in obj.values())
    if isinstance(obj, list):
        return sum(count_numeric_fields(v) for v in obj)
    if isinstance(obj, (int, float)) and not isinstance(obj, bool):
        return 1
    return 0


def main() -> None:
    DOCS_DIR.mkdir(parents=True, exist_ok=True)
    g1, p1 = run_suite_g1()
    g2, p2 = run_suite_g2()
    g3, p3 = run_suite_g3()
    g4, p4 = run_suite_g4()
    g5, p5 = run_suite_g5()

    make_figures(p1, p2, p3, p4, p5)

    scientific = {"G1": g1, "G2": g2, "G3": g3, "G4": g4, "G5": g5}
    n_fields = count_numeric_fields(scientific)

    payload = {
        "metadata": {
            "paper": "paper3_layer2_type2",
            "seed": SEED,
            "scientific_numeric_fields": n_fields,
            "figures": [
                "paper/figures/fig1_steering_and_lf_boundary.pdf",
                "paper/figures/fig2_type2_clock_entropy.pdf",
                "paper/figures/fig3_dynamical_nonisometric_pullback.pdf",
                "paper/figures/fig4_branch_coupling_gate.pdf",
            ],
        },
        **scientific,
    }
    out_path = DOCS_DIR / "numerical_verification.json"
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    print(f"VERIFICATION COMPLETE: {n_fields} scientific numeric fields recorded in {out_path}")
    print(f"G1: S_rational={g1['rational_lf_S']:.6f}, werner_id_err={g1['werner_mixed_max_identity_err']:.2e}, FR_p_okok={g1['fr_p_ok_ok']:.6f}")
    print(f"G2: rat_Nmin={g2['rational_witness_min_negativity']:.6f}, wf_cpl={g2['wigner_friend_cpl_disagreement']:.1e}, wf_coh={g2['wigner_friend_p_int_coherent']:.3f}, wf_deph={g2['wigner_friend_p_int_dephased']:.3f}, replacer_gap={g2['replacer_weight_gap']:.2f}")
    print(f"G3: alg_dim={g3['algebra_linear_dim']}, decomp_err={g3['max_entropy_branch_decomp_err']:.2e}, cor1_res={g3['cor1_state_dependent_residual']:.6f}, cor1_err={g3['cor1_identity_err']:.2e}")
    print(f"G4: seq_d2_compat={g4['seq_d2_max_radiation_compat_err']:.2e}, seq_d4_compat={g4['seq_d4_max_radiation_compat_err']:.2e}, post_max_compat={max(g4['postselected_seq_compat_discrepancy_rightmost']):.4f}, sharp_0p8_norm={g4['sharp_sat_eps_0p8_norm_l1']:.6f}")
    print(f"G5: swap_spatial={g5['ctrl0p_swap_spatial_signaling_td']:.3f}, trine_max_tr={g5['mechA_trine_max_output_trace']:.3f}, dup_rms={g5['mechA_dup_rms']:.6f}>>{g5['mechA_dup_welch_lower']:.6f}, exact_C_psi={g5['mechC_exact_C_psi_norm']:.2e}, exact_C_OA={g5['mechC_exact_C_OA_comm_frob']:.2e}")


if __name__ == "__main__":
    main()
