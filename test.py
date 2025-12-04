# -*- coding: utf-8 -*-
import numpy as np
import math
import random
import matplotlib.pyplot as plt

print("="*80)
print("残差计算机 · 纯内存 CPU · 五大测试一体版（神之 OR 参数）")
print("="*80)

# ============================================================
# 0. 神之参数 + 基本结构
# ============================================================

CANONICAL_GATES = {
    'XOR': {'λ': 5.0,  'κ': -10.0, 'τ': 2.5},
    'AND': {'λ': 1.0,  'κ': 4.0,   'τ': 3.5},
    'OR' : {'λ': 5.0,  'κ': 0.0,   'τ': 2.5},  # 神之 OR
}

WORD_WIDTH = 4   # 数据位宽
PC_WIDTH   = 4   # PC 位宽
OPC_WIDTH  = 3   # opcode 位宽

OP_NOP   = 0
OP_LOADI = 1
OP_ADDI  = 2
OP_JNZ   = 3
OP_HALT  = 4

ACC_IDX = 0
PC_IDX  = 1

def int_to_bits(x, width):
    return [(x >> i) & 1 for i in range(width)]

def bits_to_int(bits, carry=0):
    return carry * (1 << len(bits)) + int(''.join(map(str, bits[::-1])), 2)

def int_to_bits_width(x, width):
    return [(x >> i) & 1 for i in range(width)]

# ============================================================
# 1. 残差场 & 逻辑门 & 加法器 & 控制流
# ============================================================

class ResidualField:
    def __init__(self, sigma=0.0, gates=None):
        self.sigma = sigma
        self.gates = gates if gates is not None else CANONICAL_GATES

    def energy(self, a, b, λ, κ):
        return abs(λ * (a + b) + κ * (a * b))

    def evaluate(self, a, b, gate_name):
        p = self.gates[gate_name]
        E = self.energy(a, b, p['λ'], p['κ'])
        if self.sigma > 0:
            E = max(0.0, E + np.random.normal(0, self.sigma))
        return 1 if E > p['τ'] else 0

    def NOT(self, a):
        return self.evaluate(a, 1, 'XOR')

class ResidualGates:
    def __init__(self, field: ResidualField):
        self.f = field
    def XOR(self, a, b): return self.f.evaluate(a, b, 'XOR')
    def AND(self, a, b): return self.f.evaluate(a, b, 'AND')
    def OR (self, a, b): return self.f.evaluate(a, b, 'OR')
    def NOT(self, a):    return self.f.NOT(a)

class ResidualAdder:
    def __init__(self, gates: ResidualGates):
        self.g = gates

    def full_adder(self, a, b, cin):
        s1 = self.g.XOR(a, b)
        s  = self.g.XOR(s1, cin)
        c1 = self.g.AND(a, b)
        c2 = self.g.AND(s1, cin)
        cout = self.g.OR(c1, c2)
        return s, cout

    def adder_nbit(self, A_bits, B_bits):
        n = len(A_bits)
        result = []
        carry = 0
        for i in range(n):
            s, carry = self.full_adder(A_bits[i], B_bits[i], carry)
            result.append(s)
        return result, carry

class ResidualControl:
    def __init__(self, gates: ResidualGates):
        self.g = gates

    def mux_bit(self, a, b, s):
        ns = self.g.NOT(s)
        p1 = self.g.AND(ns, a)
        p2 = self.g.AND(s,  b)
        return self.g.OR(p1, p2)

    def mux_word(self, A_bits, B_bits, s):
        return [self.mux_bit(a, b, s) for a, b in zip(A_bits, B_bits)]

    def is_zero(self, X_bits):
        acc = 0
        for x in X_bits:
            acc = self.g.OR(acc, x)
        return self.g.NOT(acc)

    def equal_bits(self, A_bits, B_bits):
        acc = 0
        for a, b in zip(A_bits, B_bits):
            diff = self.g.XOR(a, b)
            acc = self.g.OR(acc, diff)
        return self.g.NOT(acc)

    def less_than_unsigned(self, A_bits, B_bits):
        n = len(A_bits)
        eq = 1
        lt = 0
        gt = 0
        for i in range(n - 1, -1, -1):
            a = A_bits[i]
            b = B_bits[i]
            a_lt_b = self.g.AND(self.g.NOT(a), b)
            a_gt_b = self.g.AND(a, self.g.NOT(b))
            new_lt = self.g.OR(lt, self.g.AND(eq, a_lt_b))
            new_gt = self.g.OR(gt, self.g.AND(eq, a_gt_b))
            a_xor_b = self.g.XOR(a, b)
            a_eq_b  = self.g.NOT(a_xor_b)
            new_eq  = self.g.AND(eq, a_eq_b)
            lt, gt, eq = new_lt, new_gt, new_eq
        return lt

    def register_conditional_move(self, reg_bits, new_bits, cond_bit):
        return [self.mux_bit(r, n, cond_bit) for r, n in zip(reg_bits, new_bits)]

    def residual_if_word(self, cond_bit, then_bits, else_bits):
        return self.mux_word(else_bits, then_bits, cond_bit)

# ============================================================
# 2. 纯内存残差 CPU + 理想整数 CPU
# ============================================================

class ResidualCPUMem:
    def __init__(self, program, sigma=0.0, gates=None):
        self.field = ResidualField(sigma=sigma, gates=gates)
        self.gates = ResidualGates(self.field)
        self.adder = ResidualAdder(self.gates)
        self.ctrl  = ResidualControl(self.gates)

        self.program = [
            {
                'opcode_bits': int_to_bits_width(inst['opcode'], OPC_WIDTH),
                'imm_bits'   : int_to_bits(inst['imm'] & 0b1111, WORD_WIDTH)
            }
            for inst in program
        ]

        self.mem = [
            int_to_bits(0, WORD_WIDTH),  # ACC
            int_to_bits(0, PC_WIDTH),    # PC
        ]

        self._op_bits = {
            op: int_to_bits_width(op, OPC_WIDTH)
            for op in [OP_NOP, OP_LOADI, OP_ADDI, OP_JNZ, OP_HALT]
        }

    def _read_word(self, idx):
        return self.mem[idx]

    def _write_word(self, idx, bits):
        if idx >= len(self.mem):
            for _ in range(idx + 1 - len(self.mem)):
                self.mem.append(int_to_bits(0, WORD_WIDTH))
        self.mem[idx] = [int(b) for b in bits]

    def _read_acc(self):
        return self._read_word(ACC_IDX)

    def _write_acc(self, bits):
        self._write_word(ACC_IDX, bits)

    def _read_pc_bits(self):
        return self._read_word(PC_IDX)

    def _write_pc_bits(self, bits):
        self._write_word(PC_IDX, bits)

    def _pc_to_int(self):
        return bits_to_int(self._read_pc_bits(), 0)

    def _acc_to_int(self):
        return bits_to_int(self._read_acc(), 0) & 0b1111

    def _eq_opcode(self, op_bits, opcode_const):
        pattern = self._op_bits[opcode_const]
        return self.ctrl.equal_bits(op_bits, pattern)

    def _pc_inc_bits(self):
        pc_bits = self._read_pc_bits()
        one = int_to_bits(1, PC_WIDTH)
        new_pc_bits, carry = self.adder.adder_nbit(pc_bits, one)
        return new_pc_bits

    def step(self):
        pc_val = self._pc_to_int()
        if pc_val < 0 or pc_val >= len(self.program):
            return True  # 越界视为 HALT

        inst_bits = self.program[pc_val]
        op_bits   = inst_bits['opcode_bits']
        imm_bits  = inst_bits['imm_bits']

        is_NOP   = self._eq_opcode(op_bits, OP_NOP)
        is_LOADI = self._eq_opcode(op_bits, OP_LOADI)
        is_ADDI  = self._eq_opcode(op_bits, OP_ADDI)
        is_JNZ   = self._eq_opcode(op_bits, OP_JNZ)
        is_HALT  = self._eq_opcode(op_bits, OP_HALT)

        pc_inc_bits = self._pc_inc_bits()
        acc_bits    = self._read_acc()
        acc_is_zero = self.ctrl.is_zero(acc_bits)
        acc_is_nz   = self.gates.NOT(acc_is_zero)

        acc_nop = acc_bits
        pc_nop  = pc_inc_bits

        acc_load = imm_bits
        pc_load  = pc_inc_bits

        acc_add_bits, carry_add = self.adder.adder_nbit(acc_bits, imm_bits)
        pc_add = pc_inc_bits

        cond_jump = self.gates.AND(is_JNZ, acc_is_nz)
        pc_jnz = self.ctrl.mux_word(pc_inc_bits, imm_bits, cond_jump)
        acc_jnz = acc_bits

        acc_halt = acc_bits
        pc_halt  = self._read_pc_bits()

        acc_next = acc_nop
        pc_next  = pc_nop

        acc_next = self.ctrl.mux_word(acc_next, acc_load,    is_LOADI)
        pc_next  = self.ctrl.mux_word(pc_next,  pc_load,     is_LOADI)

        acc_next = self.ctrl.mux_word(acc_next, acc_add_bits, is_ADDI)
        pc_next  = self.ctrl.mux_word(pc_next,  pc_add,       is_ADDI)

        acc_next = self.ctrl.mux_word(acc_next, acc_jnz, is_JNZ)
        pc_next  = self.ctrl.mux_word(pc_next,  pc_jnz,  is_JNZ)

        acc_next = self.ctrl.mux_word(acc_next, acc_halt, is_HALT)
        pc_next  = self.ctrl.mux_word(pc_next,  pc_halt,  is_HALT)

        self._write_acc(acc_next)
        self._write_pc_bits(pc_next)

        return (is_HALT == 1)

    def run(self, max_steps=50, verbose=False, return_trace=False):
        step = 0
        trace = []
        if verbose:
            print("\n[CPUMem] 纯内存残差机运行开始 (sigma={:.2f})".format(self.field.sigma))
            print("step | PC | ACC")
            print("-"*20)
        while step < max_steps:
            pc_val  = self._pc_to_int()
            acc_val = self._acc_to_int()
            if verbose:
                print(f"{step:4d} | {pc_val:2d} | {acc_val:2d}")
            if return_trace:
                trace.append((step, pc_val, acc_val))
            halted = self.step()
            if halted:
                if verbose:
                    print("[CPUMem] HALT，停机。")
                break
            step += 1
        if return_trace:
            return self._acc_to_int(), trace
        return self._acc_to_int()

def ideal_cpu_run(program, max_steps=50):
    acc = 0
    pc  = 0
    trace = []
    step = 0
    halted = False
    while step < max_steps:
        if pc < 0 or pc >= len(program):
            break
        trace.append((step, pc, acc))
        inst = program[pc]
        op, imm = inst['opcode'], inst['imm'] & 0b1111
        if op == OP_NOP:
            pc = (pc + 1) & 0b1111
        elif op == OP_LOADI:
            acc = imm
            pc = (pc + 1) & 0b1111
        elif op == OP_ADDI:
            acc = (acc + imm) & 0b1111
            pc = (pc + 1) & 0b1111
        elif op == OP_JNZ:
            if acc != 0:
                pc = imm & 0b1111
            else:
                pc = (pc + 1) & 0b1111
        elif op == OP_HALT:
            halted = True
            break
        else:
            break
        step += 1
    return acc & 0b1111, trace, halted

# 倒计时程序
def countdown_program(start_value):
    return [
        {'opcode': OP_LOADI, 'imm': start_value},
        {'opcode': OP_ADDI , 'imm': 15},  # -1 (mod16)
        {'opcode': OP_JNZ  , 'imm': 1},
        {'opcode': OP_HALT , 'imm': 0},
    ]

# ============================================================
# TEST 1: 4 位加法器穷举正确性
# ============================================================

print("\n[TEST 1] 4 位加法器穷举正确性（σ=0）")
rf = ResidualField(sigma=0.0)
rg = ResidualGates(rf)
adder = ResidualAdder(rg)

all_ok = True
max_err = 0
for A in range(16):
    for B in range(16):
        Ab = int_to_bits(A, WORD_WIDTH)
        Bb = int_to_bits(B, WORD_WIDTH)
        sum_bits, carry = adder.adder_nbit(Ab, Bb)
        res = bits_to_int(sum_bits, carry)
        if res != A + B:
            all_ok = False
            max_err = max(max_err, abs(res - (A+B)))
            print(f"  错误: {A}+{B}, 残差={res}, 真实={A+B}")
if all_ok:
    print("  ✓ 所有 4 位加法 (0..15) × (0..15) 全部正确")
else:
    print("  ✗ 加法器存在错误, max_err =", max_err)

# ============================================================
# TEST 2: 理想 CPU vs 残差 CPU（σ=0）
# ============================================================

print("\n[TEST 2] 理想 CPU vs 残差 CPU 轨迹对比（σ=0）")

def compare_cpu(program):
    ideal_acc, ideal_trace, ideal_halt = ideal_cpu_run(program, max_steps=50)
    cpu = ResidualCPUMem(program, sigma=0.0)
    cpu._write_acc(int_to_bits(0, WORD_WIDTH))
    cpu._write_pc_bits(int_to_bits(0, PC_WIDTH))
    res_acc, res_trace = cpu.run(max_steps=50, verbose=False, return_trace=True)
    ok = True
    min_len = min(len(ideal_trace), len(res_trace))
    for (s1,p1,a1),(s2,p2,a2) in zip(ideal_trace[:min_len], res_trace[:min_len]):
        if (p1!=p2) or (a1!=a2):
            ok = False
            break
    ok = ok and (ideal_acc == res_acc)
    return ok, ideal_trace, res_trace, ideal_acc, res_acc

prog_short = countdown_program(3)
ok_short, it_short, rt_short, ia_short, ra_short = compare_cpu(prog_short)
print("  倒计时程序 start=3: ", "✓ 一致" if ok_short else "✗ 不一致",
      f"(ideal ACC={ia_short}, residual ACC={ra_short})")

prog_long = countdown_program(7)
ok_long, it_long, rt_long, ia_long, ra_long = compare_cpu(prog_long)
print("  倒计时程序 start=7: ", "✓ 一致" if ok_long else "✗ 不一致",
      f"(ideal ACC={ia_long}, residual ACC={ra_long})")

# ============================================================
# TEST 3: 程序成功率 vs σ vs 步数（短/长程序）
# ============================================================

print("\n[TEST 3] 程序级成功率 vs 噪声 σ（短循环 vs 长循环）")

def measure_success_rate(program, sigma, trials=200, max_steps=50):
    success = 0
    for _ in range(trials):
        cpu = ResidualCPUMem(program, sigma=sigma)
        cpu._write_acc(int_to_bits(0, WORD_WIDTH))
        cpu._write_pc_bits(int_to_bits(0, PC_WIDTH))
        final_acc, trace = cpu.run(max_steps=max_steps, verbose=False, return_trace=True)
        # 期望 ACC=0，且最后一条状态 PC=3（HALT 所在）
        if len(trace) == 0:
            continue
        last_step, last_pc, last_acc = trace[-1]
        if final_acc == 0 and last_pc == 3:
            success += 1
    return success / trials

sigmas = np.linspace(0.0, 0.6, 7)
prog_short = countdown_program(3)
prog_long  = countdown_program(7)

print("  σ    | 短程序成功率(start=3) | 长程序成功率(start=7)")
print("  -----------------------------------------------")
short_rates = []
long_rates  = []
for s in sigmas:
    r_short = measure_success_rate(prog_short, s, trials=200)
    r_long  = measure_success_rate(prog_long,  s, trials=200)
    short_rates.append(r_short)
    long_rates.append(r_long)
    print(f"  {s:0.2f} | {r_short*100:8.2f}%             | {r_long*100:8.2f}%")

plt.figure(figsize=(8,4))
plt.plot(sigmas, short_rates, 'o-', label='短程序 start=3')
plt.plot(sigmas, long_rates,  's--', label='长程序 start=7')
plt.xlabel('噪声 σ')
plt.ylabel('成功率')
plt.title('程序成功率 vs σ（短/长循环）')
plt.grid(True, alpha=0.3)
plt.legend()
plt.tight_layout()
plt.show()

# ============================================================
# TEST 4: 神之 OR 周围参数敏感性（σ=0.3）
# ============================================================

print("\n[TEST 4] 神之 OR 周围参数敏感性（σ=0.3，start=3 倒计时）")

def or_variation_success(lambda_or, kappa_or, tau_or, sigma=0.3, trials=200):
    custom_gates = {
        'XOR': CANONICAL_GATES['XOR'],
        'AND': CANONICAL_GATES['AND'],
        'OR' : {'λ': lambda_or, 'κ': kappa_or, 'τ': tau_or},
    }
    program = countdown_program(3)
    success = 0
    for _ in range(trials):
        cpu = ResidualCPUMem(program, sigma=sigma, gates=custom_gates)
        cpu._write_acc(int_to_bits(0, WORD_WIDTH))
        cpu._write_pc_bits(int_to_bits(0, PC_WIDTH))
        final_acc, trace = cpu.run(max_steps=50, verbose=False, return_trace=True)
        if len(trace) == 0:
            continue
        last_step, last_pc, last_acc = trace[-1]
        if final_acc == 0 and last_pc == 3:
            success += 1
    return success / trials

lambda_vals = [4.5, 5.0, 5.5]
kappa_vals  = [-1.0, 0.0, 1.0]
tau_val     = 2.5

print("  行: λ in {4.5,5.0,5.5}, 列: κ in {-1,0,1}, τ=2.5, σ=0.3")
for lam in lambda_vals:
    row_str = []
    for kap in kappa_vals:
        rate = or_variation_success(lam, kap, tau_val, sigma=0.3, trials=100)
        row_str.append(f"{rate*100:6.1f}%")
    print(f"  λ={lam:3.1f} | " + " ".join(row_str))

# ============================================================
# TEST 5: 单门错误率 vs σ（XOR / AND / OR）
# ============================================================

print("\n[TEST 5] 单门错误率 vs σ（在 {0,1}² 上）")

def gate_error_rate(gate_name, sigma, trials=1000):
    rf = ResidualField(sigma=sigma)
    rg = ResidualGates(rf)
    err = 0
    for _ in range(trials):
        a = random.randint(0,1)
        b = random.randint(0,1)
        if gate_name == 'XOR':
            ideal = a ^ b
            out = rg.XOR(a,b)
        elif gate_name == 'AND':
            ideal = a & b
            out = rg.AND(a,b)
        elif gate_name == 'OR':
            ideal = a | b
            out = rg.OR(a,b)
        else:
            continue
        if out != ideal:
            err += 1
    return err / trials

sigmas_gate = [0.0, 0.1, 0.2, 0.3, 0.4, 0.5]
print("  σ    | XOR错误率 | AND错误率 | OR错误率")
print("  ---------------------------------------")
xor_errs, and_errs, or_errs = [], [], []
for s in sigmas_gate:
    ex = gate_error_rate('XOR', s, trials=2000)
    ea = gate_error_rate('AND', s, trials=2000)
    eo = gate_error_rate('OR',  s, trials=2000)
    xor_errs.append(ex); and_errs.append(ea); or_errs.append(eo)
    print(f"  {s:0.1f} | {ex*100:8.3f}% | {ea*100:8.3f}% | {eo*100:8.3f}%")

plt.figure(figsize=(8,4))
plt.plot(sigmas_gate, xor_errs, 'o-', label='XOR 错误率')
plt.plot(sigmas_gate, and_errs, 's--', label='AND 错误率')
plt.plot(sigmas_gate, or_errs,  'd-.', label='OR 错误率')
plt.xlabel('噪声 σ')
plt.ylabel('错误率')
plt.title('单门错误率 vs σ')
plt.grid(True, alpha=0.3)
plt.legend()
plt.tight_layout()
plt.show()

print("\n全部 5 组测试完成。")
print("="*80)

