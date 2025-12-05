# ============================================================
# Residual Computer - 理论起源与工程验证集成版 (V12 - 代码清理版)
# ============================================================

import numpy as np
import struct
from collections import Counter
from math import isfinite
import math

# ------------------------------------------------------------
# 0. 物理与架构参数
# ------------------------------------------------------------

M_ENERGY_GAP = 5.0
TARGET_WORD_ACC_ALPHA1 = 0.52965
WORD_BITS = 32
GATE_DEPTH_PER_BIT = 8
SIGMA_BASELINE = 0.05  # 静态基线噪声 σ₀
T_BASE_FLOAT32 = 0.037
E_BASE_FLOAT32 = 1e-6


# ============================================================
# 理论起源模块 (M=5.0)
# ============================================================
PARAMS_XOR = {'lambda': 20.0, 'kappa': -30.0, 'tau': 15.0}  
PARAMS_AND = {'lambda': 10.0, 'kappa': 20.0, 'tau': 15.0}   
PARAMS_OR  = {'lambda': 15.0, 'kappa': 0.0, 'tau': 7.5}     

def energy_function(a: int, b: int, lambda_val: float, kappa: float) -> float:
    return abs(lambda_val * (a + b) + kappa * a * b)

def boolean_gate_from_energy(a: int, b: int, params: dict) -> int:
    E = energy_function(a, b, params['lambda'], params['kappa'])
    return 1 if E > params['tau'] else 0

def compute_energy_margin(params: dict) -> float:
    test_cases = [(0,0), (0,1), (1,0), (1,1)]
    min_margin = float('inf')
    for a, b in test_cases:
        E = energy_function(a, b, params['lambda'], params['kappa'])
        margin = abs(E - params['tau'])
        min_margin = min(min_margin, margin)
    return min_margin

def run_theory_verification():
    print("="*60)
    print("【理论验证】1. 能量最小化与布尔逻辑起源 (目标 M=5.0)")
    print("="*60)
    
    gates_to_verify = {'XOR': PARAMS_XOR, 'AND': PARAMS_AND, 'OR': PARAMS_OR}
    system_min_margin = float('inf')
    
    for name, params in gates_to_verify.items():
        print(f"\n--- 验证门: {name} ---")
        correct = True
        margin = compute_energy_margin(params)
        system_min_margin = min(system_min_margin, margin)
        
        expected_output = {'XOR': [0, 1, 1, 0], 'AND': [0, 0, 0, 1], 'OR': [0, 1, 1, 1]}
        test_cases = [(0,0), (0,1), (1,0), (1,1)]
        for i, (a, b) in enumerate(test_cases):
            result = boolean_gate_from_energy(a, b, params)
            expected = expected_output[name][i]
            E = energy_function(a, b, params['lambda'], params['kappa'])
            E_vs_tau = "E > τ" if E > params['tau'] else "E < τ"
            print(f"  Input ({a}, {b}): E={E:.2f} (τ={params['tau']:.2f}, {E_vs_tau}) -> Result: {result} (Expected: {expected})")
            if result != expected:
                correct = False
        
        status = "✅ 成功" if correct and margin >= M_ENERGY_GAP else "❌ 失败"
        print(f"  验证状态: {status}，实际裕度 M = {margin:.3f}")

    print(f"\n系统最小能量裕度 M (min of all gates): {system_min_margin:.3f} (目标 M={M_ENERGY_GAP:.1f})")


# ============================================================
# 2. 标定逻辑：反解 SIGMA_DYNAMIC_FACTOR (不变)
# ============================================================

p_eff_target = 1.0 - TARGET_WORD_ACC_ALPHA1 ** (1.0 / WORD_BITS)
p_gate_target = 1.0 - (1.0 - p_eff_target) ** (1.0 / GATE_DEPTH_PER_BIT)
sigma_total_required = M_ENERGY_GAP / math.sqrt(8.0 * math.log(2.0 / p_gate_target))
SIGMA_DYNAMIC_FACTOR = sigma_total_required - SIGMA_BASELINE


# ============================================================
# 3. ULP, float32 互转工具 (不变)
# ============================================================

def float32_to_bits(x: np.float32) -> np.ndarray:
    b = struct.pack('>f', float(x))
    i = struct.unpack('>I', b)[0]
    return np.array([(i >> (31 - k)) & 1 for k in range(32)], dtype=np.uint8)

def bits_to_float32(bits: np.ndarray) -> np.float32:
    bits = bits.astype(np.uint8)
    val = 0
    for k in range(32):
        val = (val << 1) | int(bits[k])
    b = struct.pack('>I', val)
    x = struct.unpack('>f', b)[0]
    return np.float32(x)

def float32_to_int_repr(x: np.float32) -> int:
    b = struct.pack('>f', float(x))
    i = struct.unpack('>I', b)[0]
    if i & 0x80000000:
        return ~i & 0xFFFFFFFF
    else:
        return i | 0x80000000

def ulp_distance(a: np.float32, b: np.float32) -> int:
    ia = float32_to_int_repr(a)
    ib = float32_to_int_repr(b)
    return abs(ia - ib)


# ============================================================
# 4. 残差噪声模型：缓存与边界修正 (V9 优化)
# ============================================================
_P_ERR_CACHE = {} # 全局缓存

def sigma_from_alpha(alpha: float) -> float:
    return float(SIGMA_BASELINE + alpha * SIGMA_DYNAMIC_FACTOR)

def p_error_from_sigma(sigma: float, M: float = M_ENERGY_GAP) -> float:
    """V9修正：σ=0边界和下溢检查"""
    if sigma <= 0.0:
        return 0.0 
        
    log_ratio = - (M ** 2) / (8.0 * sigma ** 2)
    
    if log_ratio < -700.0:
        return 0.0
    
    p = 2.0 * math.pow(math.e, log_ratio)
    p = float(min(max(p, 0.0), 0.5))
    return p

def p_error_from_alpha(alpha: float) -> float:
    """V9优化：缓存 p_error_from_sigma"""
    if alpha in _P_ERR_CACHE:
        return _P_ERR_CACHE[alpha]
        
    result = p_error_from_sigma(sigma_from_alpha(alpha))
    _P_ERR_CACHE[alpha] = result
    return result

def rc_noisy_bits(bits: np.ndarray, alpha: float, depth: int = GATE_DEPTH_PER_BIT) -> np.ndarray:
    p_gate = p_error_from_alpha(alpha)
    
    # V9优化：快速路径
    if p_gate < 1e-15: 
        return bits.copy().astype(np.uint8)

    p_eff = 1.0 - math.pow(1.0 - p_gate, depth)

    noisy = bits.copy().astype(np.uint8)
    flip_mask = np.random.rand(len(noisy)) < p_eff
    noisy[flip_mask] ^= 1
    return noisy


# ============================================================
# 5-6. 浮点加法核心 (修正 V11)
# ============================================================

def ideal_fadd(a: np.float32, b: np.float32) -> np.float32:
    return np.float32(a + b)

def rc_float_add_bits(a: np.float32, b: np.float32, alpha: float, gate_depth_per_bit: int = GATE_DEPTH_PER_BIT) -> np.ndarray:
    ideal = ideal_fadd(a, b)
    bits = float32_to_bits(ideal)
    noisy_bits = rc_noisy_bits(bits, alpha=alpha, depth=gate_depth_per_bit)
    return noisy_bits

def rc_float_add(a: np.float32, b: np.float32, alpha: float, gate_depth_per_bit: int = GATE_DEPTH_PER_BIT) -> np.float32:
    # 修正：调用 rc_float_add_bits 来获取噪声比特串
    noisy_bits = rc_float_add_bits(a, b, alpha, gate_depth_per_bit) 
    rc_out = bits_to_float32(noisy_bits)
    return rc_out

def majority_bits(b1: np.ndarray, b2: np.ndarray, b3: np.ndarray) -> np.ndarray:
    s = b1.astype(np.int16) + b2.astype(np.int16) + b3.astype(np.int16)
    return (s >= 2).astype(np.uint8)

def tmr_rc_float_add(a: np.float32, b: np.float32, alpha: float, gate_depth_per_bit: int = GATE_DEPTH_PER_BIT) -> np.float32:
    bits1 = rc_float_add_bits(a, b, alpha, gate_depth_per_bit)
    bits2 = rc_float_add_bits(a, b, alpha, gate_depth_per_bit)
    bits3 = rc_float_add_bits(a, b, alpha, gate_depth_per_bit)

    maj_bits = majority_bits(bits1, bits2, bits3)
    rc_out = bits_to_float32(maj_bits)
    return rc_out


# ============================================================
# 7. 单路 RC 浮点加法鲁棒性基准 (修正 V12)
# ============================================================

def run_rc_fadd_benchmark(
    num_samples: int = 20000,
    alpha_list = (0.0, 0.6, 0.7, 0.8, 0.9, 1.0),
    gate_depth_per_bit: int = GATE_DEPTH_PER_BIT,
    value_range = (-1e4, 1e4),
    rel_tol_thresholds = (1e-6, 1e-9),
    max_ulp_record: int = 4, # 保持参数定义
    seed: int = 0
):
    rng = np.random.default_rng(seed)
    results = {}

    for alpha in alpha_list:
        p_err_alpha = p_error_from_alpha(alpha)
        sigma_alpha = sigma_from_alpha(alpha)
        
        print(f"\n=== [Single] 测试 alpha = {alpha:.3f} (σ={sigma_alpha:.3f}, P_err={p_err_alpha:.2e}) ===")
        exact_matches = 0
        valid_count = 0

        # --- 理论正确率计算 ---
        p_gate = p_error_from_alpha(alpha)
        p_total_correct_theory = math.pow(1.0 - p_gate, GATE_DEPTH_PER_BIT * WORD_BITS)
        
        if alpha == 0.0:
            print(f"  理论基线字正确率: {p_total_correct_theory:.6f} (32 bit)")
        # --- 理论正确率计算结束 ---


        ulp_hist = Counter()
        rel_tol_counts = {thr: 0 for thr in rel_tol_thresholds}
        
        for _ in range(num_samples):
            a = np.float32(rng.uniform(*value_range))
            b = np.float32(rng.uniform(*value_range))

            ref = ideal_fadd(a, b)
            rc  = rc_float_add(a, b, alpha=alpha, gate_depth_per_bit=gate_depth_per_bit)

            if not (isfinite(ref) and isfinite(rc)):
                continue

            valid_count += 1
            if float32_to_bits(ref).tolist() == float32_to_bits(rc).tolist():
                exact_matches += 1

            ulp = ulp_distance(ref, rc)
            ulp_hist[min(ulp, max_ulp_record)] += 1 # 使用参数 max_ulp_record

            if ref != 0.0:
                rel_err = abs((float(rc) - float(ref)) / float(ref))
            else:
                rel_err = abs(float(rc) - float(ref))

            for thr in rel_tol_thresholds:
                if rel_err <= thr:
                    rel_tol_counts[thr] += 1

        if valid_count == 0:
            print("  (无有效样本)")
            continue

        exact_rate = exact_matches / valid_count
        print(f"  有效样本数: {valid_count}")
        print(f"  [Single] bitwise 完全正确比例: {exact_rate:.6f}")

        total_ulp_samples = sum(ulp_hist.values())
        print(f"  [Single] ULP 误差分布 (0..{max_ulp_record}+):") # 使用参数 max_ulp_record
        for e in range(max_ulp_record): # 使用参数 max_ulp_record
            c = ulp_hist[e]
            print(f"    ULP = {e}: {c} ({c / total_ulp_samples:.4f})")
        c_catastrophic = ulp_hist[max_ulp_record] # 使用参数 max_ulp_record
        print(f"    ULP >= {max_ulp_record}: {c_catastrophic} ({c_catastrophic / total_ulp_samples:.4f})")

        for thr in rel_tol_thresholds:
            ratio = rel_tol_counts[thr] / valid_count
            print(f"  [Single] |rel_err| <= {thr:g} 的比例: {ratio:.6f}")

        results[alpha] = {
            "valid_count": valid_count,
            "exact_rate": exact_rate,
            "ulp_hist": dict(ulp_hist),
            "rel_tol_counts": rel_tol_counts,
        }

    return results

def run_tmr_rc_fadd_benchmark(
    num_samples: int = 20000,
    alpha_list = (1.0,),
    gate_depth_per_bit: int = GATE_DEPTH_PER_BIT,
    value_range = (-1e4, 1e4),
    rel_tol_thresholds = (1e-6, 1e-9),
    max_ulp_record: int = 4, # 保持参数定义
    seed: int = 0
):
    rng = np.random.default_rng(seed)
    results = {}

    for alpha in alpha_list:
        p_err_alpha = p_error_from_alpha(alpha)
        sigma_alpha = sigma_from_alpha(alpha)
        p_gate = p_error_from_alpha(alpha)
        
        # --- TMR 理论正确率计算 ---
        p_tmr_gate = 3 * p_gate**2 - 2 * p_gate**3
        p_tmr_correct_link = math.pow(1.0 - p_tmr_gate, GATE_DEPTH_PER_BIT)
        p_tmr_total_correct_theory = math.pow(p_tmr_correct_link, WORD_BITS)

        print(f"\n=== [TMR] 测试 alpha = {alpha:.3f} (σ={sigma_alpha:.3f}, P_err={p_err_alpha:.2e}) ===")
        print(f"  理论TMR字正确率: {p_tmr_total_correct_theory:.6f} (32 bit)")
        # --- TMR 理论正确率计算结束 ---
        
        exact_matches = 0
        valid_count = 0

        ulp_hist = Counter()
        rel_tol_counts = {thr: 0 for thr in rel_tol_thresholds}

        for _ in range(num_samples):
            a = np.float32(rng.uniform(*value_range))
            b = np.float32(rng.uniform(*value_range))

            ref = ideal_fadd(a, b)
            rc  = tmr_rc_float_add(a, b, alpha=alpha, gate_depth_per_bit=gate_depth_per_bit)

            if not (isfinite(ref) and isfinite(rc)):
                continue

            valid_count += 1
            if float32_to_bits(ref).tolist() == float32_to_bits(rc).tolist():
                exact_matches += 1

            ulp = ulp_distance(ref, rc)
            ulp_hist[min(ulp, max_ulp_record)] += 1 # 使用参数 max_ulp_record

            if ref != 0.0:
                rel_err = abs((float(rc) - float(ref)) / float(ref))
            else:
                rel_err = abs(float(rc) - float(ref))

            for thr in rel_tol_thresholds:
                if rel_err <= thr:
                    rel_tol_counts[thr] += 1

        if valid_count == 0:
            print("  (无有效样本)")
            continue

        exact_rate = exact_matches / valid_count
        print(f"  有效样本数: {valid_count}")
        print(f"  [TMR] bitwise 完全正确比例: {exact_rate:.6f}")

        total_ulp_samples = sum(ulp_hist.values())
        print(f"  [TMR] ULP 误差分布 (0..{max_ulp_record}+):") # 使用参数 max_ulp_record
        for e in range(max_ulp_record): # 使用参数 max_ulp_record
            c = ulp_hist[e]
            print(f"    ULP = {e}: {c} ({c / total_ulp_samples:.4f})")
        c = ulp_hist[max_ulp_record] # 使用参数 max_ulp_record
        print(f"    ULP >= {max_ulp_record}: {c} ({c / total_ulp_samples:.4f})")

        for thr in rel_tol_thresholds:
            ratio = rel_tol_counts[thr] / valid_count
            print(f"  [TMR] |rel_err| <= {thr:g} 的比例: {ratio:.6f}")

        results[alpha] = {
            "valid_count": valid_count,
            "exact_rate": exact_rate,
            "ulp_hist": dict(ulp_hist),
            "rel_tol_counts": rel_tol_counts,
        }

    return results


# ============================================================
# 9. TMR 延迟 & 能耗成本估算 (修正 V10)
# ============================================================

def print_tmr_cost_estimate():
    T_single = T_BASE_FLOAT32
    E_single = E_BASE_FLOAT32

    T_tmr_serial = 3 * T_single
    E_tmr_serial = 3 * E_single
    T_tmr_parallel = T_single
    E_tmr_parallel = 3 * E_single

    print("\n=== TMR 成本估算 (占位) ===")
    print(f"单路:    T = {T_single:.3e} s / op, E = {E_single:.3e} J / op")
    print(f"TMR 串行: T ≈ {T_tmr_serial:.3e} s / op, E ≈ {E_tmr_serial:.3e} J / op") 
    print(f"TMR 并行: T ≈ {T_tmr_parallel:.3e} s / op, E ≈ {E_tmr_parallel:.3e} J / op") 

    ops_per_j_single = 1.0 / E_single
    ops_per_j_tmr_serial = 1.0 / E_tmr_serial
    ops_per_j_tmr_parallel = 1.0 / E_tmr_parallel

    print(f"\nOps/J (单路):     {ops_per_j_single:.3e}")
    print(f"Ops/J (TMR 串行): {ops_per_j_tmr_serial:.3e}")
    print(f"Ops/J (TMR 并行): {ops_per_j_tmr_parallel:.3e}")


# ============================================================
# 10. main: 执行 (修正 V12)
# ============================================================

if __name__ == "__main__":
    run_theory_verification()
    
    print("-" * 60)
    print(f"模型参数: M={M_ENERGY_GAP}, D={GATE_DEPTH_PER_BIT}, σ₀={SIGMA_BASELINE}")
    print(f"标定值: σ(α=1.0) total = {sigma_total_required:.3f}, P_gate(α=1.0) = {p_gate_target:.2e}")
    print("-" * 60)

    # 修正 V12：明确传递 max_ulp_record 参数
    results_single = run_rc_fadd_benchmark(
        num_samples=20000,
        alpha_list=[0.0, 0.6, 0.7, 0.8, 0.9, 1.0],
        gate_depth_per_bit=GATE_DEPTH_PER_BIT,
        value_range=(-1e4, 1e4),
        rel_tol_thresholds=(1e-6, 1e-9),
        max_ulp_record=4, # 明确传递
        seed=42
    )

    # 修正 V12：明确传递 max_ulp_record 参数
    results_tmr = run_tmr_rc_fadd_benchmark(
        num_samples=20000,
        alpha_list=[1.0],
        gate_depth_per_bit=GATE_DEPTH_PER_BIT,
        value_range=(-1e4, 1e4),
        rel_tol_thresholds=(1e-6, 1e-9),
        max_ulp_record=4, # 明确传递
        seed=43
    )

    print_tmr_cost_estimate()