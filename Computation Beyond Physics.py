# ===============================
# Residual VM / Mini CPU for Colab
# ===============================

from dataclasses import dataclass
from typing import List, Dict, Tuple, Union

# 寄存器数量 & 内存大小
NUM_REGS = 8
MEM_SIZE = 256

@dataclass
class VMState:
    regs: List[int]
    mem: List[int]
    flags: Dict[str, bool]
    pc: int = 0
    steps: int = 0
    halted: bool = False

def make_vm() -> VMState:
    return VMState(
        regs=[0]*NUM_REGS,
        mem=[0]*MEM_SIZE,
        flags={"EQ": False, "LT": False, "GT": False},
        pc=0,
        steps=0,
        halted=False
    )

Instruction = Tuple

def resolve_labels(program: List[Instruction]):
    """把 ('LABEL', 'name') 转成 label -> pc 映射，并返回去掉 LABEL 的指令列表"""
    labels = {}
    real_instructions = []
    for instr in program:
        op = instr[0]
        if op == "LABEL":
            label_name = instr[1]
            labels[label_name] = len(real_instructions)
        else:
            real_instructions.append(instr)
    return real_instructions, labels

def set_flags_cmp(state: VMState, v1: int, v2: int):
    state.flags["EQ"] = (v1 == v2)
    state.flags["LT"] = (v1 <  v2)
    state.flags["GT"] = (v1 >  v2)

def step_vm(state: VMState, program: List[Instruction], labels: Dict[str, int]):
    if state.halted or not (0 <= state.pc < len(program)):
        state.halted = True
        return

    instr = program[state.pc]
    op = instr[0]
    args = instr[1:]
    state.steps += 1

    # --- 数据操作类 ---
    if op == "LOADI":
        r, imm = args
        state.regs[r] = int(imm)
        state.pc += 1

    elif op == "LOAD":
        r, addr = args
        state.regs[r] = state.mem[addr]
        state.pc += 1

    elif op == "STORE":
        r, addr = args
        state.mem[addr] = int(state.regs[r])
        state.pc += 1

    elif op == "MOV":
        rd, rs = args
        state.regs[rd] = int(state.regs[rs])
        state.pc += 1

    elif op == "ADD":
        rd, rs = args
        state.regs[rd] = state.regs[rd] + state.regs[rs]  # 不做 8-bit 截断，直接用 Python int
        state.pc += 1

    elif op == "SUB":
        rd, rs = args
        state.regs[rd] = state.regs[rd] - state.regs[rs]
        state.pc += 1

    elif op == "INC":
        r, = args
        state.regs[r] = state.regs[r] + 1
        state.pc += 1

    elif op == "DEC":
        r, = args
        state.regs[r] = state.regs[r] - 1
        state.pc += 1

    # --- 比较 & 标志 ---
    elif op == "CMP":
        r1, r2 = args
        v1 = state.regs[r1]
        v2 = state.regs[r2]
        set_flags_cmp(state, v1, v2)
        state.pc += 1

    elif op == "CMP_IMM":
        r, imm = args
        v1 = state.regs[r]
        v2 = int(imm)
        set_flags_cmp(state, v1, v2)
        state.pc += 1

    # --- 跳转 ---
    elif op == "JMP":
        label, = args
        state.pc = labels[label]

    elif op == "JE":
        label, = args
        if state.flags["EQ"]:
            state.pc = labels[label]
        else:
            state.pc += 1

    elif op == "JNE":
        label, = args
        if not state.flags["EQ"]:
            state.pc = labels[label]
        else:
            state.pc += 1

    elif op == "JLT":
        label, = args
        if state.flags["LT"]:
            state.pc = labels[label]
        else:
            state.pc += 1

    elif op == "JGT":
        label, = args
        if state.flags["GT"]:
            state.pc = labels[label]
        else:
            state.pc += 1

    elif op == "JLE":
        label, = args
        if state.flags["LT"] or state.flags["EQ"]:
            state.pc = labels[label]
        else:
            state.pc += 1

    elif op == "JGE":
        label, = args
        if state.flags["GT"] or state.flags["EQ"]:
            state.pc = labels[label]
        else:
            state.pc += 1

    # --- 终止 ---
    elif op == "HALT":
        state.halted = True

    else:
        raise ValueError(f"未知指令: {op}")


def run_program(program: List[Instruction], max_steps: int = 10_000) -> VMState:
    real_prog, labels = resolve_labels(program)
    state = make_vm()
    while not state.halted and state.steps < max_steps:
        step_vm(state, real_prog, labels)
    if state.steps >= max_steps:
        print("⚠️ 达到最大步数，可能出现死循环")
    return state

# ===============================
# 程序 1：Sum 1..N
# ===============================

def build_program_sum(N: int) -> List[Instruction]:
    """
    用 R0 累加 1..N，结果写入 mem[0]
    R0: sum
    R1: i
    R2: N
    """
    prog = [
        ("LOADI", 0, 0),      # R0 = 0 (sum)
        ("LOADI", 1, 1),      # R1 = 1 (i)
        ("LOADI", 2, N),      # R2 = N
        ("LABEL", "loop"),
        ("CMP",   1, 2),      # cmp R1, R2
        ("JGT",  "end"),      # if i > N: jump end
        ("ADD",   0, 1),      # sum += i
        ("INC",   1),         # i += 1
        ("JMP",  "loop"),
        ("LABEL", "end"),
        ("STORE", 0, 0),      # mem[0] = sum
        ("HALT",),
    ]
    return prog

# ===============================
# 程序 2：Fib(n) 迭代
# ===============================

def build_program_fib(n: int) -> List[Instruction]:
    """
    迭代计算 Fibonacci：
    R0 = a = fib(i)
    R1 = b = fib(i+1)
    R2 = tmp = a+b
    R3 = counter = n
    R7 = 0 常量
    循环 n 次之后，R1 = fib(n+1)
    最终把 R1 写入 mem[1]
    """
    prog = [
        ("LOADI", 0, 1),      # R0 = 1
        ("LOADI", 1, 1),      # R1 = 1
        ("LOADI", 3, n),      # R3 = n (迭代次数)
        ("LOADI", 7, 0),      # R7 = 0
        ("LABEL", "loop"),
        ("CMP",   3, 7),      # cmp R3, 0
        ("JLE",  "end"),      # if counter <= 0: end
        ("MOV",   2, 0),      # R2 = R0 (a)
        ("ADD",   2, 1),      # R2 = a + b
        ("MOV",   0, 1),      # a = b
        ("MOV",   1, 2),      # b = a+b
        ("DEC",   3),         # counter--
        ("JMP",  "loop"),
        ("LABEL", "end"),
        ("STORE", 1, 1),      # mem[1] = b = fib(n+1)
        ("HALT",),
    ]
    return prog

# ===============================
# 实验：Sum 与 Fib
# ===============================

def print_state_sum(state: VMState, N: int):
    print(f"=== 程序 1：Sum 1..{N} ===")
    print("寄存器状态:", state.regs)
    print(f"内存[0] (sum 1..{N}):", state.mem[0])
    print("执行步数:", state.steps)
    print()

def print_state_fib(state: VMState, n: int):
    print(f"=== 程序 2：Fib(n) 迭代 (n={n}) ===")
    print("寄存器状态:", state.regs)
    print(f"内存[1] (fib({n+1})): {state.mem[1]}")
    print("执行步数:", state.steps)
    print()

# ===============================
# 跑实验
# ===============================

# 1. Sum 1..10
state_sum10 = run_program(build_program_sum(10))
print_state_sum(state_sum10, 10)

# 2. Sum 1..20
state_sum20 = run_program(build_program_sum(20))
print_state_sum(state_sum20, 20)  # 期待 210

# 3. Fib n=10  -> fib(11)=89
state_fib10 = run_program(build_program_fib(10))
print_state_fib(state_fib10, 10)

# 4. Fib n=15  -> fib(16)=987
state_fib15 = run_program(build_program_fib(15))
print_state_fib(state_fib15, 15)


