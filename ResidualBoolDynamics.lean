import Mathlib
noncomputable section
open Real

namespace Residual
set_option autoImplicit false
set_option linter.unusedVariables false

------------------------------------------------------------
-- 0. BoolFn：二元布尔函数空间（Theorem 3 用）
------------------------------------------------------------

/-- 二元布尔函数类型：{0,1}² → {0,1}. -/
def BoolFn := Bool → Bool → Bool

------------------------------------------------------------
-- 1. 连续能量律与 Hessian（Theorem 1）
------------------------------------------------------------

/-- 能量参数：λ, κ. -/
structure Params where
  lam : ℝ
  kap : ℝ
deriving DecidableEq   -- 不派生 Repr，避免 unsafe

/-- 连续能量：E(x,y) = (lam*(x+y) + kap*x*y)^2. -/
def E (p : Params) (x y : ℝ) : ℝ :=
  let g := p.lam*(x + y) + p.kap*x*y
  g*g

/-- ∂E/∂x 的显式代数表达式（不依赖微积分库）。 -/
def dE_dx (p : Params) (x y : ℝ) : ℝ :=
  let g := p.lam*(x + y) + p.kap*x*y
  let L := p.lam + p.kap*y
  2*g*L

/-- ∂E/∂y 的显式代数表达式。 -/
def dE_dy (p : Params) (x y : ℝ) : ℝ :=
  let g := p.lam*(x + y) + p.kap*x*y
  let L := p.lam + p.kap*x
  2*g*L

/-- ∂²E/∂x². -/
def d2E_dx2 (p : Params) (x y : ℝ) : ℝ :=
  let L := p.lam + p.kap*y
  2 * L * L

/-- ∂²E/∂y². -/
def d2E_dy2 (p : Params) (x y : ℝ) : ℝ :=
  let L := p.lam + p.kap*x
  2 * L * L

/-- ∂²E/(∂x∂y). -/
def d2E_dxdy (p : Params) (x y : ℝ) : ℝ :=
  let g  := p.lam*(x + y) + p.kap*x*y
  let Lx := p.lam + p.kap*y
  let Ly := p.lam + p.kap*x
  2 * (Lx * Ly + p.kap*g)

/-- Hessian 矩阵（2×2）。 -/
def Hessian (p : Params) (x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    match i.val, j.val with
    | 0,0 => d2E_dx2  p x y
    | 0,1 => d2E_dxdy p x y
    | 1,0 => d2E_dxdy p x y
    | 1,1 => d2E_dy2  p x y
    | _,_ => 0  -- 理论上不会到这里，仅为模式匹配完备

/-- Theorem 1: 对任意 (x,y)，Hessian 是对称矩阵。 -/
lemma Hessian_symm (p : Params) (x y : ℝ) :
  Matrix.transpose (Hessian p x y) = Hessian p x y := by
  funext i j
  cases' i using Fin.cases with hi hi <;>
  cases' j using Fin.cases with hj hj <;>
  simp [Hessian, Matrix.transpose]

------------------------------------------------------------
-- 2. 离散能量 E_b 上的 XOR 唯一极小性（Theorem 2）
------------------------------------------------------------

/-- 将连续能量 E 限制到布尔点 (0,1)² 上。 -/
def Eb (p : Params) (a b : Bool) : ℝ :=
  E p (if a then 1 else 0) (if b then 1 else 0)

/-- XOR 区域：Lean 需要一个显式的能量排序假设。 -/
def isXORregion (p : Params) : Prop :=
  Eb p true  false = Eb p false true ∧
  Eb p true  false < Eb p false false ∧
  Eb p true  false < Eb p true  true

/-- Theorem 2:
  在 XOR 区域内，(1,0) / (0,1) 的能量是所有布尔点中最小，
  并且 Eb(1,0) = Eb(0,1)（XOR 的两个 “true” 点能量相等且为全局最小）。 -/
theorem XOR_unique_min (p : Params)
  (h : isXORregion p) :
  (∀ a b, Eb p a b ≥ Eb p true false) ∧
  Eb p true false = Eb p false true :=
by
  rcases h with ⟨hSym, hLT00, hLT11⟩

  refine And.intro ?min ?eq

  · intro a b
    -- 穷举四个布尔点
    cases a <;> cases b <;>
    simp [Eb] <;>
    first
      | exact le_of_lt hLT00        -- (0,0) 能量 > (1,0)
      | exact le_of_lt hLT11        -- (1,1) 能量 > (1,0)
      | exact le_of_eq (Eq.symm hSym) -- (0,1) 与 (1,0) 能量相等
      | exact le_of_eq hSym

  · exact hSym

------------------------------------------------------------
-- 3. 离散“局部对齐”动力学的全局收敛（Theorem 3）
------------------------------------------------------------

/-- 单点 mismatch：如果 f(a,b) ≠ target(a,b)，记 1，否则 0。 -/
def mismatch (target f : BoolFn) (a b : Bool) : Nat :=
  if f a b = target a b then 0 else 1

/-- 与 target 在四个布尔输入上的 Hamming 距离（0–4）。 -/
def hammingCost (target f : BoolFn) : Nat :=
  mismatch target f false false +
  mismatch target f false true  +
  mismatch target f true  false +
  mismatch target f true  true

/-- 在输入点 (a0,b0) 上，把 f 的输出对齐到 target，其它点保持不变。 -/
def updateAt (target f : BoolFn) (a0 b0 : Bool) : BoolFn :=
  fun a b =>
    if a = a0 ∧ b = b0 then
      target a b
    else
      f a b

/-- updateAt 在目标点 (a0,b0) 上确实等于 target。 -/
lemma updateAt_at_target (target f : BoolFn) (a0 b0 : Bool) :
  updateAt target f a0 b0 a0 b0 = target a0 b0 := by
  simp [updateAt]

/-- 在非目标点上，updateAt 不改变原函数值。 -/
lemma updateAt_other (target f : BoolFn) (a0 b0 a b : Bool)
  (h : ¬ (a = a0 ∧ b = b0)) :
  updateAt target f a0 b0 a b = f a b := by
  simp [updateAt, h]

/-- 连续对四个布尔输入点依次做局部对齐：
    先修正 (false,false)，再修正 (false,true)，
    然后修正 (true,false)，最后修正 (true,true)。 -/
def fixAll (target f : BoolFn) : BoolFn :=
  updateAt target
    (updateAt target
      (updateAt target
        (updateAt target f false false)
        false true)
      true false)
    true true

/-- Theorem 3 核心：对任意 (a,b)，fixAll target f 的值等于 target a b。 -/
lemma fixAll_eval (target f : BoolFn) :
  fixAll target f = target := by
  funext a b
  -- 穷举四种布尔输入
  cases a <;> cases b <;>
    simp [fixAll, updateAt]

/-- Theorem 3（全局收敛版）：
    对任意目标门 `target` 和任意初始布尔函数 `f`，
    经过 fixAll 的 4 步局部对齐之后，得到的函数必然等于 `target`。 -/
theorem fixAll_converges (target f : BoolFn) :
  fixAll target f = target :=
  fixAll_eval target f

/-- 推论：fixAll 之后在任意点 (a,b) 不再有 mismatch。 -/
lemma mismatch_fixAll_zero (target f : BoolFn) (a b : Bool) :
  mismatch target (fixAll target f) a b = 0 := by
  have h := congrArg (fun g => g a b) (fixAll_eval target f)
  unfold mismatch
  simp [h]

/-- 推论：fixAll 之后 Hamming 代价为 0（和 target 完全一致）。 -/
lemma hammingCost_fixAll_zero (target f : BoolFn) :
  hammingCost target (fixAll target f) = 0 := by
  unfold hammingCost
  have h00 := mismatch_fixAll_zero target f false false
  have h01 := mismatch_fixAll_zero target f false true
  have h10 := mismatch_fixAll_zero target f true  false
  have h11 := mismatch_fixAll_zero target f true  true
  simp [h00, h01, h10, h11]

end Residual

