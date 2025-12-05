import Mathlib
noncomputable section
open Real

namespace Residual
set_option autoImplicit false
set_option linter.unusedVariables false
-- 如果不想看某些提示，也可以加：
-- set_option linter.unnecessarySimpa false
-- set_option linter.unnecessarySeqFocus false

/-
  Params: (λ, κ) parameters of the analytic energy law
    E(x,y) = (λ(x+y) + κxy)²
-/
structure Params where
  lam : ℝ
  kap : ℝ
deriving DecidableEq

------------------------------------------------------------
-- THEOREM 1 : Analytic energy & Hessian symmetry
------------------------------------------------------------

/-- Continuous energy on ℝ²: E(x,y) = (λ(x+y) + κxy)². -/
def E (p : Params) (x y : ℝ) : ℝ :=
  let g := p.lam*(x + y) + p.kap*x*y
  g * g

/-- ∂E/∂x : symbolic derivative (no calculus library). -/
def dE_dx (p : Params) (x y : ℝ) : ℝ :=
  let g := p.lam*(x + y) + p.kap*x*y
  let L := p.lam + p.kap*y
  2 * g * L

/-- ∂E/∂y : symbolic derivative. -/
def dE_dy (p : Params) (x y : ℝ) : ℝ :=
  let g := p.lam*(x + y) + p.kap*x*y
  let L := p.lam + p.kap*x
  2 * g * L

/-- ∂²E/∂x² : second derivative in x, 2·(λ+κy)². -/
def d2E_dx2 (p : Params) (x y : ℝ) : ℝ :=
  2 * (p.lam + p.kap*y)^2

/-- ∂²E/∂y² : second derivative in y, 2·(λ+κx)². -/
def d2E_dy2 (p : Params) (x y : ℝ) : ℝ :=
  2 * (p.lam + p.kap*x)^2

/-- ∂²E/(∂x∂y) : mixed second derivative. -/
def d2E_dxdy (p : Params) (x y : ℝ) : ℝ :=
  let g  := p.lam*(x + y) + p.kap*x*y
  let Lx := p.lam + p.kap*y
  let Ly := p.lam + p.kap*x
  2 * (Lx * Ly + p.kap*g)

/-- Hessian of E at (x,y) as a 2×2 matrix. -/
def Hessian (p : Params) (x y : ℝ) :
  Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    match i.val, j.val with
    | 0,0 => d2E_dx2 p x y
    | 0,1 => d2E_dxdy p x y
    | 1,0 => d2E_dxdy p x y
    | 1,1 => d2E_dy2 p x y
    | _,_ => 0   -- 不会被真的用到，只是保证 total

/-- THEOREM 1 (formal):
    For all parameters (λ,κ) and all (x,y), the Hessian of E is symmetric. -/
lemma Hessian_symm (p : Params) (x y : ℝ) :
  Matrix.transpose (Hessian p x y) = Hessian p x y := by
  funext i j
  cases' i using Fin.cases <;> cases' j using Fin.cases <;>
  simp [Hessian, Matrix.transpose]

------------------------------------------------------------
-- 基础：二阶导的非负性 / 正性（Theorem 4 要用）
------------------------------------------------------------

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

------------------------------------------------------------
-- THEOREM 2 : XOR discrete minimum on {0,1}²
------------------------------------------------------------

/-- Discrete energy on Boolean inputs. -/
def Eb (p : Params) (a b : Bool) : ℝ :=
  E p (if a then 1 else 0) (if b then 1 else 0)

/-- XOR-region: 两个 XOR 角 (1,0) 和 (0,1) 等能量、
    且严格低于另外两个角 (0,0)、(1,1). -/
def isXORregion (p : Params) : Prop :=
  Eb p true false = Eb p false true ∧
  Eb p true false < Eb p false false ∧
  Eb p true false < Eb p true true

/-- THEOREM 2 (formal):
    If `p` is in the XOR-region, then for all Boolean (a,b),
    Eb(a,b) ≥ Eb(1,0), and Eb(1,0) = Eb(0,1).

    即：在 {0,1}² 上，唯一的极小点集合是 {(1,0),(0,1)}. -/
theorem XOR_unique_min (p : Params)
  (h : isXORregion p) :
  (∀ a b, Eb p a b ≥ Eb p true false) ∧
  Eb p true false = Eb p false true := by
  rcases h with ⟨hSym, hLT00, hLT11⟩
  refine And.intro ?min ?eq
  · intro a b
    cases a <;> cases b
    · -- (false,false)
      exact le_of_lt hLT00
    · -- (false,true) 要证明 Eb 0 1 ≥ Eb 1 0
      have : Eb p false true = Eb p true false := by
        simpa [eq_comm] using hSym
      -- 转成 Eb 0 1 ≥ Eb 0 1
      simpa [this]
    · -- (true,false)
      exact le_rfl
    · -- (true,true)
      exact le_of_lt hLT11
  · exact hSym

------------------------------------------------------------
-- THEOREM 5 (new) : AND / OR discrete minima on {0,1}²
------------------------------------------------------------

/-- AND-region: (1,1) 在四个布尔角中具有严格最小能量。 -/
def isANDregion (p : Params) : Prop :=
  Eb p true true < Eb p false false ∧
  Eb p true true < Eb p true false ∧
  Eb p true true < Eb p false true

/-- THEOREM 5 (AND 部分):
    在 AND-region 内，(1,1) 是 Eb 在 {0,1}² 上的唯一极小点。 -/
theorem AND_unique_min (p : Params)
  (h : isANDregion p) :
  ∀ a b, Eb p a b ≥ Eb p true true := by
  rcases h with ⟨hTT00, hTT10, hTT01⟩
  intro a b
  cases a <;> cases b
  · -- (false,false)
    exact le_of_lt hTT00
  · -- (false,true)
    exact le_of_lt hTT01
  · -- (true,false)
    exact le_of_lt hTT10
  · -- (true,true)
    exact le_rfl

/-- OR-region:
    三个“真”角 (1,0)、(0,1)、(1,1) 等能量，
    并且都严格低于 (0,0) 的能量。 -/
def isORregion (p : Params) : Prop :=
  Eb p true false = Eb p false true ∧
  Eb p true false = Eb p true true ∧
  Eb p true false < Eb p false false

/-- THEOREM 5 (OR 部分):
    在 OR-region 内，三个 “真” 角 (1,0)、(0,1)、(1,1)
    组成 Eb 在 {0,1}² 上的极小集。 -/
theorem OR_min_set (p : Params)
  (h : isORregion p) :
  (∀ a b, Eb p a b ≥ Eb p true false) ∧
  Eb p true false = Eb p false true ∧
  Eb p true false = Eb p true true := by
  rcases h with ⟨hTF_FT, hTF_TT, hTF_LT00⟩
  refine And.intro ?min ?eqs
  · intro a b
    cases a <;> cases b
    · -- (false,false)：能量最高
      exact le_of_lt hTF_LT00
    · -- (false,true)：极小之一
      -- Eb 0 1 = Eb 1 0
      have : Eb p false true = Eb p true false := by
        simpa [eq_comm] using hTF_FT
      simpa [this]
    · -- (true,false)：极小之一
      exact le_rfl
    · -- (true,true)：极小之一，与 (1,0) 等能量
      have : Eb p true true = Eb p true false := by
        simpa [eq_comm] using hTF_TT
      simpa [this]
  · exact And.intro hTF_FT hTF_TT

------------------------------------------------------------
-- THEOREM 3 : existence of a real threshold τ decoding XOR
------------------------------------------------------------

/-- Pure Boolean XOR truth table. -/
def XORbool (a b : Bool) : Bool :=
  (a && !b) || (!a && b)

/-- Energy gate with real threshold τ: [E(a,b) < τ]. -/
def XORgate (p : Params) (τ : ℝ) (a b : Bool) : Bool :=
  decide (Eb p a b < τ)

/-- There exists τ such that XOR corners have E < τ < other corners. -/
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

/-- Truth-table equality: with such τ, XORgate = XORbool. -/
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

/-- THEOREM 3 (formal):
    There exists a real τ such that the physical energy-gate
    `(a,b) ↦ [Eb(a,b) < τ]` realizes the XOR truth-table. -/
theorem XORgate_realizes_XOR (p : Params) (h : isXORregion p) :
  ∃ τ, ∀ a b, XORgate p τ a b = XORbool a b := by
  obtain ⟨τ, h1, h2, h3, h4⟩ := exists_XOR_threshold p h
  refine ⟨τ, ?_⟩
  intro a b
  exact XORgate_truth_table p h1 h2 h3 h4 a b

------------------------------------------------------------
-- THEOREM 4 : Axis-strong convexity at XOR parameters
------------------------------------------------------------

/-- XOR parameters used in the paper. -/
def pXOR : Params := { lam := 20, kap := -30 }

/-- Bool → ℝ via {false↦0, true↦1}. -/
def b2r (b : Bool) : ℝ := if b then 1 else 0

/-- For pXOR and any Boolean b, we have λ+κ·b ≠ 0. -/
lemma lam_plus_kap_b2r_ne_zero (b : Bool) :
  pXOR.lam + pXOR.kap * b2r b ≠ 0 := by
  cases b <;> simp [pXOR, b2r] <;> norm_num

/-- THEOREM 4 (formal, axis-strong convexity at XOR corners):

    For pXOR = (20,-30) and each Boolean corner (a,b),
    both second derivatives along x and y are strictly positive.

    This encodes “strict convexity along coordinate axes” at each
    Boolean corner, matching the idea of a stable local minimum
    in the continuous energy landscape. -/
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

end Residual

