import Mathlib
noncomputable section
open Real

namespace Residual

set_option autoImplicit false
set_option linter.unusedVariables false
-- 如需安静一点，可以再加：
-- set_option linter.unnecessarySimpa false
-- set_option linter.unnecessarySeqFocus false

/-
############################################################
# Section 0. 纯布尔函数空间与局部对齐动力学（fixAll）
############################################################
-/

/-- 二元布尔函数类型：{0,1}² → {0,1}. -/
def BoolFn := Bool → Bool → Bool

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

/-- 对任意 (a,b)，fixAll target f 的值等于 target a b。 -/
lemma fixAll_eval (target f : BoolFn) :
  fixAll target f = target := by
  funext a b
  -- 穷举四种布尔输入
  cases a <;> cases b <;>
    simp [fixAll, updateAt]

/-- Theorem（全局收敛版）：
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

/-
############################################################
# Section 1. 连续能量律 E 与 Hessian（Theorem 1）
############################################################
-/

/-- 能量参数：λ, κ. -/
structure Params where
  lam : ℝ
  kap : ℝ
deriving DecidableEq   -- 不派生 Repr，避免 unsafe

/-- 连续能量：E(x,y) = (lam*(x+y) + kap*x*y)^2. -/
def E (p : Params) (x y : ℝ) : ℝ :=
  let g := p.lam*(x + y) + p.kap*x*y
  g * g

/-- ∂E/∂x 的显式代数表达式（不依赖微积分库）。 -/
def dE_dx (p : Params) (x y : ℝ) : ℝ :=
  let g := p.lam*(x + y) + p.kap*x*y
  let L := p.lam + p.kap*y
  2 * g * L

/-- ∂E/∂y 的显式代数表达式。 -/
def dE_dy (p : Params) (x y : ℝ) : ℝ :=
  let g := p.lam*(x + y) + p.kap*x*y
  let L := p.lam + p.kap*x
  2 * g * L

/-- ∂²E/∂x² = 2·(λ+κy)². -/
def d2E_dx2 (p : Params) (x y : ℝ) : ℝ :=
  2 * (p.lam + p.kap*y)^2

/-- ∂²E/∂y² = 2·(λ+κx)². -/
def d2E_dy2 (p : Params) (x y : ℝ) : ℝ :=
  2 * (p.lam + p.kap*x)^2

/-- ∂²E/(∂x∂y) : mixed second derivative. -/
def d2E_dxdy (p : Params) (x y : ℝ) : ℝ :=
  let g  := p.lam*(x + y) + p.kap*x*y
  let Lx := p.lam + p.kap*y
  let Ly := p.lam + p.kap*x
  2 * (Lx * Ly + p.kap*g)

/-- Hessian 矩阵（2×2）。 -/
def Hessian (p : Params) (x y : ℝ) :
  Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    match i.val, j.val with
    | 0,0 => d2E_dx2  p x y
    | 0,1 => d2E_dxdy p x y
    | 1,0 => d2E_dxdy p x y
    | 1,1 => d2E_dy2  p x y
    | _,_ => 0  -- 理论上不会到这里，仅为模式匹配完备

/-- THEOREM 1:
    对任意 (λ,κ) 与 (x,y)，Hessian(E) 是对称矩阵。 -/
lemma Hessian_symm (p : Params) (x y : ℝ) :
  Matrix.transpose (Hessian p x y) = Hessian p x y := by
  funext i j
  cases' i using Fin.cases with hi hi <;>
  cases' j using Fin.cases with hj hj <;>
  simp [Hessian, Matrix.transpose]

/-
############################################################
# Section 2. 二阶导的非负 / 正（局部凸性 / 稳定性）
############################################################
-/

/-- ∂²E/∂x² ≥ 0 for all (x,y). -/
lemma d2E_dx2_nonneg (p : Params) (x y : ℝ) :
  0 ≤ d2E_dx2 p x y := by
  unfold d2E_dx2
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  have hL : 0 ≤ (p.lam + p.kap*y)^2 := by
    have := sq_nonneg (p.lam + p.kap*y)
    simpa [pow_two] using this
  exact mul_nonneg h2 hL

/-- ∂²E/∂y² ≥ 0 for all (x,y). -/
lemma d2E_dy2_nonneg (p : Params) (x y : ℝ) :
  0 ≤ d2E_dy2 p x y := by
  unfold d2E_dy2
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  have hL : 0 ≤ (p.lam + p.kap*x)^2 := by
    have := sq_nonneg (p.lam + p.kap*x)
    simpa [pow_two] using this
  exact mul_nonneg h2 hL

/-- If λ+κy ≠ 0, then ∂²E/∂x² > 0. -/
lemma d2E_dx2_pos (p : Params) (x y : ℝ)
  (hL : p.lam + p.kap*y ≠ 0) :
  0 < d2E_dx2 p x y := by
  unfold d2E_dx2
  have h2 : 0 < (2 : ℝ) := by norm_num
  have hL2 : 0 < (p.lam + p.kap*y)^2 := by
    have h : p.lam + p.kap*y ≠ 0 := hL
    simpa [pow_two] using (sq_pos_of_ne_zero h)
  exact mul_pos h2 hL2

/-- If λ+κx ≠ 0, then ∂²E/∂y² > 0. -/
lemma d2E_dy2_pos (p : Params) (x y : ℝ)
  (hL : p.lam + p.kap*x ≠ 0) :
  0 < d2E_dy2 p x y := by
  unfold d2E_dy2
  have h2 : 0 < (2 : ℝ) := by norm_num
  have hL2 : 0 < (p.lam + p.kap*x)^2 := by
    have h : p.lam + p.kap*x ≠ 0 := hL
    simpa [pow_two] using (sq_pos_of_ne_zero h)
  exact mul_pos h2 hL2

/-
############################################################
# Section 3. XOR：离散极小 & 阈值门 & pXOR 轴向凸性
############################################################
-/

/-- 将连续能量 E 限制到布尔点 (0,1)² 上。 -/
def Eb (p : Params) (a b : Bool) : ℝ :=
  E p (if a then 1 else 0) (if b then 1 else 0)

/-- XOR 区域：两个 XOR 角 (1,0) 和 (0,1) 等能量、
    且严格低于另外两个角 (0,0)、(1,1). -/
def isXORregion (p : Params) : Prop :=
  Eb p true  false = Eb p false true ∧
  Eb p true  false < Eb p false false ∧
  Eb p true  false < Eb p true  true

/-- THEOREM 2:
  在 XOR 区域内，(1,0) / (0,1) 的能量是所有布尔点中最小，
  并且 Eb(1,0) = Eb(0,1)（XOR 的两个 “true” 点能量相等且为全局最小）。 -/
theorem XOR_unique_min (p : Params)
  (h : isXORregion p) :
  (∀ a b, Eb p a b ≥ Eb p true false) ∧
  Eb p true false = Eb p false true := by
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

/-- 纯布尔 XOR 真值表。 -/
def XORbool (a b : Bool) : Bool :=
  (a && !b) || (!a && b)

/-- Energy gate with real threshold τ: [Eb(a,b) < τ]. -/
def XORgate (p : Params) (τ : ℝ) (a b : Bool) : Bool :=
  decide (Eb p a b < τ)

/-- 存在 τ，使得 XOR 角有 E < τ < 其他角。 -/
lemma exists_XOR_threshold (p : Params) (h : isXORregion p) :
  ∃ τ,
    Eb p true false < τ ∧
    Eb p false true < τ ∧
    τ < Eb p false false ∧
    τ < Eb p true true := by
  rcases h with ⟨hSym, hLT00, hLT11⟩
  let e : ℝ := Eb p true false
  let m : ℝ := min (Eb p false false) (Eb p true true)
  have h_em : e < m := by
    have h1 : e < Eb p false false := by simpa [e] using hLT00
    have h2 : e < Eb p true true  := by simpa [e] using hLT11
    exact lt_min h1 h2
  obtain ⟨τ, h1, h2⟩ := exists_between h_em
  have τ_lt_00 : τ < Eb p false false :=
    lt_of_lt_of_le h2 (min_le_left _ _)
  have τ_lt_11 : τ < Eb p true true  :=
    lt_of_lt_of_le h2 (min_le_right _ _)
  have hSym' : Eb p false true = Eb p true false := by
    simpa [eq_comm] using hSym
  have ht1 : Eb p false true < τ := by
    simpa [hSym'] using h1
  refine ⟨τ, ?_, ?_, ?_, ?_⟩
  · simpa [e] using h1
  · exact ht1
  · exact τ_lt_00
  · exact τ_lt_11

/-- 真值表一致性：给定这样的 τ，XORgate = XORbool。 -/
lemma XORgate_truth_table (p : Params) {τ : ℝ}
  (h_tf : Eb p true false < τ)
  (h_ft : Eb p false true < τ)
  (h00 : τ < Eb p false false)
  (h11 : τ < Eb p true true) :
  ∀ a b, XORgate p τ a b = XORbool a b := by
  intro a b
  cases a <;> cases b
  · -- (false,false) → 0
    have : ¬ Eb p false false < τ := not_lt_of_ge (le_of_lt h00)
    simp [XORgate, XORbool, this]
  · -- (false,true) → 1
    simp [XORgate, XORbool, h_ft]
  · -- (true,false) → 1
    simp [XORgate, XORbool, h_tf]
  · -- (true,true) → 0
    have : ¬ Eb p true true < τ := not_lt_of_ge (le_of_lt h11)
    simp [XORgate, XORbool, this]

/-- THEOREM 3：
    存在实数 τ，使得物理能量门 `(a,b) ↦ [Eb(a,b) < τ]`
    的真值表等价于 XOR。 -/
theorem XORgate_realizes_XOR (p : Params) (h : isXORregion p) :
  ∃ τ, ∀ a b, XORgate p τ a b = XORbool a b := by
  obtain ⟨τ, h1, h2, h3, h4⟩ := exists_XOR_threshold p h
  refine ⟨τ, ?_⟩
  intro a b
  exact XORgate_truth_table p h1 h2 h3 h4 a b

/-- 论文中用于 XOR 的具体参数。 -/
def pXOR : Params := { lam := 20, kap := -30 }

/-- Bool → ℝ via {false↦0, true↦1}. -/
def b2r (b : Bool) : ℝ := if b then 1 else 0

/-- 对于 pXOR 和任意 Bool b，有 λ+κ·b ≠ 0. -/
lemma lam_plus_kap_b2r_ne_zero (b : Bool) :
  pXOR.lam + pXOR.kap * b2r b ≠ 0 := by
  cases b <;> simp [pXOR, b2r] <;> norm_num

/-- THEOREM 4（轴向严格凸性，XOR 角）：

    对 pXOR = (20,-30) 和每个布尔角 (a,b)，
    两个方向上的二阶导都严格为正。 -/
theorem XOR_axis_strict_convex_at_corners :
  ∀ a b : Bool,
    0 < d2E_dx2 pXOR (b2r a) (b2r b) ∧
    0 < d2E_dy2 pXOR (b2r a) (b2r b) := by
  intro a b
  have hLy : pXOR.lam + pXOR.kap * b2r b ≠ 0 :=
    lam_plus_kap_b2r_ne_zero b
  have hLx : pXOR.lam + pXOR.kap * b2r a ≠ 0 :=
    lam_plus_kap_b2r_ne_zero a
  refine And.intro ?hx ?hy
  · have := d2E_dx2_pos pXOR (b2r a) (b2r b) hLy
    simpa using this
  · have := d2E_dy2_pos pXOR (b2r a) (b2r b) hLx
    simpa using this

/-
############################################################
# Section 4. AND：抽象 AND 区域与唯一极小（Theorem 5 抽象版）
############################################################
-/

/-- AND-region：布尔角 (true,true) 的能量严格小于其他三个角。 -/
def isANDregion (p : Params) : Prop :=
  Eb p true  true  < Eb p false false ∧
  Eb p true  true  < Eb p true  false ∧
  Eb p true  true  < Eb p false true

/-- THEOREM 5 (抽象版 1)：
    在 AND-region 内，(1,1) 的能量是 {0,1}² 上的全局最小。 -/
theorem AND_unique_min (p : Params) (h : isANDregion p) :
  ∀ a b, Eb p true true ≤ Eb p a b := by
  rcases h with ⟨h11_lt_00, h11_lt_10, h11_lt_01⟩
  intro a b
  cases a <;> cases b
  · -- (false,false)
    exact le_of_lt h11_lt_00
  · -- (false,true)
    exact le_of_lt h11_lt_01
  · -- (true,false)
    exact le_of_lt h11_lt_10
  · -- (true,true)
    exact le_rfl

/-- THEOREM 5 (抽象版 2)：
    如果在 AND-region 中某个角 (a,b) 是全局最小点，
    那么必然 a = true 且 b = true（极小点唯一）。 -/
theorem AND_minimizer_is_tt (p : Params) (h : isANDregion p)
  {a b : Bool} (hmin : ∀ c d, Eb p a b ≤ Eb p c d) :
  a = true ∧ b = true := by
  rcases h with ⟨h11_lt_00, h11_lt_10, h11_lt_01⟩
  -- 分四种情况讨论 (a,b)
  cases a <;> cases b
  · -- (false,false) 不可能是全局最小
    exfalso
    -- 从极小性得到：E(0,0) ≤ E(1,1)
    have hle : Eb p false false ≤ Eb p true true := hmin true true
    -- 但 AND-region 中有：E(1,1) < E(0,0)
    have hlt : Eb p true true < Eb p false false := h11_lt_00
    exact not_lt_of_ge hle hlt
  · -- (false,true) 不可能是全局最小
    exfalso
    have hle : Eb p false true ≤ Eb p true true := hmin true true
    have hlt : Eb p true true < Eb p false true := h11_lt_01
    exact not_lt_of_ge hle hlt
  · -- (true,false) 不可能是全局最小
    exfalso
    have hle : Eb p true false ≤ Eb p true true := hmin true true
    have hlt : Eb p true true < Eb p true false := h11_lt_10
    exact not_lt_of_ge hle hlt
  · -- (true,true) 是唯一剩下的情况
    exact And.intro rfl rfl

end Residual
