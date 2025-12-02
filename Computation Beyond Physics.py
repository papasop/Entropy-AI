import numpy as np

# --- 结构 Full-Adder 仿真 ---
# 里程碑 4: 可扩展性 (N-bit Ripple-Carry Adder)

# === 1. 结构逻辑门参数 (简化残差模型) ===
GATE_PARAMS = {
    # XOR: E(0,0)=0, E(0,1)=E(1,0)=5, E(1,1)=0 → 阈值 2.0
    "XOR": {"lambda": -1.0, "kappa":  2.0, "threshold":  2.0}, 

    # AND: E(0,0)=0, E(0,1)=E(1,0)=10, E(1,1)=30
    # 要求: 只有 (1,1) 输出 1 → 10 < T < 30
    "AND": {"lambda": -2.0, "kappa": -2.0, "threshold": 20.0},

    # OR: 同样的能量簇，但要求: (0,0)=0，其余为 1 → 0 < T < 10
    # 取 T=5.0，离 0 有 margin=5，抗噪性更好。
    "OR":  {"lambda": -2.0, "kappa": -2.0, "threshold":  5.0}, 
}

# --- 2. 核心结构门 ---

def get_gate_result_from_bits(a, b, mode, noise_std=0.0):
    """
    简化残差模型:
      E_total ~ | λ (a + b) A + κ (a b) A |
    其中 A 是脉冲幅度，噪声加在 E_total 上，然后与阈值比较。
    """
    AMPLITUDE = 5.0
    params = GATE_PARAMS[mode]
    lambd = params['lambda']
    kappa = params['kappa']
    
    E_sum  = lambd * (a + b) * AMPLITUDE
    E_prod = kappa * (a * b) * AMPLITUDE
    E_total = abs(E_sum + E_prod)

    # 加噪声；负值不影响逻辑，因为 threshold>0
    E_noisy = E_total + np.random.normal(0, noise_std)
    
    threshold = params['threshold']
    logic_output = 1 if E_noisy > threshold else 0
    
    return logic_output, E_noisy

# --- 3. Half-Adder / Full-Adder 逻辑 ---

def structure_half_adder_logic(a, b, noise_std=0.0):
    """结构 Half-Adder: Sum = A XOR B, Carry = A AND B"""
    sum_output,   sum_energy   = get_gate_result_from_bits(a, b, "XOR", noise_std)
    carry_output, carry_energy = get_gate_result_from_bits(a, b, "AND", noise_std)
    return sum_output, carry_output, sum_energy, carry_energy

def structure_full_adder_logic(a, b, cin, noise_std=0.0):
    """
    Full-Adder:
      S1 = A XOR B
      C1 = A AND B
      S  = S1 XOR Cin
      C2 = S1 AND Cin
      Cout = C1 OR C2
    """
    # 第一半加器
    S1_out, C1_out, E_s1, E_c1 = structure_half_adder_logic(a, b, noise_std)
    # 第二半加器
    S_out, C2_out, E_sum, E_c2 = structure_half_adder_logic(S1_out, cin, noise_std)
    # OR 组合进位
    Cout_out, E_cout = get_gate_result_from_bits(C1_out, C2_out, "OR", noise_std)
    return S_out, Cout_out, E_s1, E_c1, E_sum, E_c2, E_cout

# --- 4. N-bit 行波进位加法器 (MSB-first bit 序) ---

def structure_ripple_carry_adder(bits_A, bits_B, noise_std=0.0):
    """
    bits_A, bits_B: MSB-first，例如 [0,1,1,1] 表示 0111(2)
    内部从 LSB 开始做 full-adder，向 MSB 传递进位。
    """
    N = len(bits_A)
    if len(bits_B) != N:
        raise ValueError("A 和 B 的位数必须相同")
    
    Sum_bits = []
    Carry_out = 0  # C0 = 0

    # 从最低位 (末尾 index) 开始
    for i in range(N - 1, -1, -1):
        a = bits_A[i]
        b = bits_B[i]
        cin = Carry_out
        
        S_out, Cout_out, *_ = structure_full_adder_logic(a, b, cin, noise_std)
        Carry_out = Cout_out
        Sum_bits.insert(0, S_out)  # 塞到前面，保持 MSB-first

    return Sum_bits, Carry_out

def bits_to_int(bits):
    return int("".join(map(str, bits)), 2)

# --- 5. 验证工具 ---

def verify_gate(mode):
    print(f"\nVerifying {mode} gate (no noise):")
    for a in [0, 1]:
        for b in [0, 1]:
            out, E = get_gate_result_from_bits(a, b, mode, noise_std=0.0)
            print(f"  Input ({a},{b}) -> Energy={E:.1f}, Output={out}")
    print("Done.")

def verify_full_adder():
    print("\nVerifying Full-Adder truth table (no noise):")
    ok = True
    for a in [0, 1]:
        for b in [0, 1]:
            for cin in [0, 1]:
                S, Cout, *_ = structure_full_adder_logic(a, b, cin, noise_std=0.0)
                S_exp   = (a ^ b) ^ cin
                Cout_exp = (a & b) | ((a ^ b) & cin)
                if (S != S_exp) or (Cout != Cout_exp):
                    print(f"  ERROR: ({a},{b},{cin}) -> S={S}(exp={S_exp}), Cout={Cout}(exp={Cout_exp})")
                    ok = False
    if ok:
        print("  Full-Adder truth table fully correct.")
    else:
        print("  Full-Adder verification FAILED.")

def sanity_check_full_space():
    """无噪声下，穷举 4-bit 所有 A,B，验证加法是否完全正确。"""
    print("\nSanity check: 4-bit full space (no noise)")
    ok = True
    for A in range(16):
        for B in range(16):
            A_bits = [int(b) for b in format(A, '04b')]
            B_bits = [int(b) for b in format(B, '04b')]
            S_bits, Cout = structure_ripple_carry_adder(A_bits, B_bits, noise_std=0.0)
            S_val = bits_to_int(S_bits) + (Cout << 4)
            if S_val != A + B:
                print(f"  Mismatch: {A} + {B} -> {S_val} (expected {A+B})")
                ok = False
                break
        if not ok:
            break
    print("  All correct?" , ok)

def noise_sweep_for_7_plus_9():
    """在不同噪声水平下，多次测试 7+9=16 的成功率。"""
    A_int, B_int, N_bits = 7, 9, 4
    A_bits = [int(b) for b in format(A_int, f'0{N_bits}b')]
    B_bits = [int(b) for b in format(B_int, f'0{N_bits}b')]
    print("\nNoise robustness for 7 + 9 = 16:")
    for noise in [0.05, 0.1, 0.15, 0.2]:
        success = 0
        trials = 200
        for _ in range(trials):
            Sum_bits, Cout = structure_ripple_carry_adder(A_bits, B_bits, noise_std=noise)
            Sum_val = bits_to_int(Sum_bits) + (Cout << N_bits)
            if Sum_val == A_int + B_int:
                success += 1
        print(f"  Noise={noise:.2f}: {success}/{trials} success ({success/trials*100:.1f}%)")

# --- 6. 主流程：里程碑 4 测试 ---

if __name__ == "__main__":
    # 6.1 验证单个门
    verify_gate("XOR")
    verify_gate("AND")
    verify_gate("OR")

    # 6.2 验证 Full-Adder 真值表
    verify_full_adder()

    # 6.3 4-bit 全空间 sanity check
    sanity_check_full_space()

    # 6.4 特定例子：4-bit 7 + 9 = 16
    A_int = 7
    B_int = 9
    N_bits = 4
    A_bits = [int(b) for b in format(A_int, f'0{N_bits}b')]
    B_bits = [int(b) for b in format(B_int, f'0{N_bits}b')]

    print("\n" + "="*70)
    print(f"=== 里程碑 4: {N_bits}-bit 行波进位加法器 (RCA) 实验 ===")
    print(f"=== 目标计算: {A_int} + {B_int} = {A_int + B_int} ===")
    print(f"=== 输入比特: A={A_bits} ({A_int}), B={B_bits} ({B_int}) ===")
    print("="*70)

    # 无噪声
    Sum_bits_clean, Cout_clean = structure_ripple_carry_adder(A_bits, B_bits, noise_std=0.0)
    Sum_int_clean = bits_to_int(Sum_bits_clean) + (Cout_clean << N_bits)
    print(f"\n--- 结果 1: 无噪声 ---")
    print(f"结构输出比特 (Cout | Sum): {Cout_clean} | {Sum_bits_clean}")
    print(f"结构输出整数: {Sum_int_clean}")
    print(f"验证: {Sum_int_clean == (A_int + B_int)}")

    # 高噪声
    noise_std_high = 0.1
    Sum_bits_noisy, Cout_noisy = structure_ripple_carry_adder(A_bits, B_bits, noise_std=noise_std_high)
    Sum_int_noisy = bits_to_int(Sum_bits_noisy) + (Cout_noisy << N_bits)
    print(f"\n--- 结果 2: 高噪声 (Noise_Std={noise_std_high}) ---")
    print(f"结构输出比特 (Cout | Sum): {Cout_noisy} | {Sum_bits_noisy}")
    print(f"结构输出整数: {Sum_int_noisy}")
    print(f"验证: {Sum_int_noisy == (A_int + B_int)}")
    print("-"*70)

    # 6.5 噪声扫描统计
    noise_sweep_for_7_plus_9()

