import numpy as np
import matplotlib.pyplot as plt
from mpmath import mp, mpc

# 设置精度
mp.dps = 50

# 定义 Dirichlet β(s) 函数的近似
def beta_series(s, N=100):
    return mp.nsum(lambda n: (-1)**(n+1) / mp.power((2*n - 1), s), [1, N])

# 生成 β(sigma + it) 的相位轨迹
def compute_beta_phase(sigma, t_range, N=100):
    t = np.linspace(0, t_range, t_range)
    s_array = [mpc(sigma, float(ti)) for ti in t]
    beta_vals = [beta_series(s, N=N) for s in s_array]
    phases = np.unwrap([np.angle(complex(float(b.real), float(b.imag))) for b in beta_vals])
    return t, np.array(phases)

# 编码字符串为结构激发 phi(t)
def encode_string_phi(input_string, spacing=20, amp=0.5, total_len=2000):
    bits = ''.join([format(ord(c), '08b') for c in input_string])
    phi = np.zeros(total_len)
    for i, bit in enumerate(bits):
        if bit == '1':
            start = i * spacing
            if start + spacing <= total_len:
                phi[start:start+spacing] += amp * np.hanning(spacing)
    return phi, bits

# 解码 phi(t) 还原字符串
def decode_phi_to_string(phi, spacing=20, threshold=0.1):
    bits_out = ''
    for i in range(len(phi) // spacing):
        segment = phi[i * spacing : (i+1) * spacing]
        energy = np.sum(segment**2)
        bits_out += '1' if energy > threshold else '0'
    chars = [chr(int(bits_out[i:i+8], 2)) for i in range(0, len(bits_out), 8) if len(bits_out[i:i+8]) == 8]
    return ''.join(chars), bits_out

# 完整流程
def store_and_recover(input_string):
    # 1. 基础波形
    t, phase_base = compute_beta_phase(sigma=0.5, t_range=2000, N=80)
    
    # 2. 编码
    phi_signal, bits_in = encode_string_phi(input_string, spacing=20, total_len=len(t))
    phase_encoded = phase_base + phi_signal
    
    # 3. 恢复
    recovered_str, bits_out = decode_phi_to_string(phase_encoded - phase_base, spacing=20)
    
    return t, phase_base, phase_encoded, phi_signal, bits_in, bits_out, recovered_str

# 执行测试
t, base, encoded, phi, bin_in, bin_out, output_str = store_and_recover("Entropy AI System")

# 可视化
plt.figure(figsize=(12, 5))
plt.plot(t, base, label="β phase")
plt.plot(t, encoded, label="β + φ", alpha=0.7)
plt.plot(t, phi, label="φ (encoded signal)", alpha=0.6)
plt.title("β(s) Phase Signal with Encoded Information")
plt.legend()
plt.xlabel("t")
plt.ylabel("Phase")
plt.grid(True)
plt.show()

# 输出结果
print("原始比特流：", bin_in)
print("恢复比特流：", bin_out)
print("恢复字符串 ：", output_str)
