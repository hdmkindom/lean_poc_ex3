import Ex3LeanAct.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

-- 定义全局变量和递归关系
variable (n : ℕ)

noncomputable def x : ℕ → ℝ
| 0       => 5
| (n + 1) => x n + 1 / x n

-- 证明 x_n > 0 非负性
lemma x_pos (n : ℕ) : 0 < x n := by
  induction n with
  | zero =>
  -- x_0 = 5, 显然大于 0
    rw [x]
    norm_num
  | succ n hx0 =>
  -- 对于 n ≥ 1 的情况，使用归纳假设
    simp [x]
    -- 分别证明 x n > 0 和 1 / x n > 0
    have h01 : 0 < x n := hx0
    -- 格外小心处理除法，确保 xₙ的-1次方与 1 / xₙ
    have h02 : 0 < (x n)⁻¹ := by
      exact inv_pos.mpr hx0
    -- 相加后得出 x (n + 1) > 0
    exact add_pos h01 h02

-- 证明 x_{n+1} > x_n 单调性
lemma x_mono (n : ℕ) : x (n + 1) > x n := by
  -- 使用递归定义展开 x (n + 1)
  rw [x]
  -- 证明 x n > 0 和 1 / x n > 0
  have h1 : x n > 0 := x_pos n
  have h2 : 1 / x n > 0 := one_div_pos.mpr h1
  -- 相加后得出 x (n + 1) > x n
  exact lt_add_of_pos_right (x n) h2

-- 单调性的传递性
lemma x_mono_le (n m : ℕ) (h : n ≤ m) : x n ≤ x m := by
  -- 使用 n ≤ m 的证明 h 进行归纳
  induction h with
  | refl => rfl -- 基底情况：n = m，x n ≤ x n 是自反的
  | step h_le_m  ih =>
    -- 归纳步：假设 n ≤ m 推出 x n ≤ x m
    -- 我们需要证明 x n ≤ x (m + 1)
    -- 我们已知 x n ≤ x m (由 ih 得出)
    rename_i m
    have h_m_lt_m_succ : x m < x (m + 1) := x_mono m
    -- 使用不等式的传递性，得出 x n ≤ x (m + 1)
    exact ih.trans h_m_lt_m_succ.le

-- 对x (n+1) 展开平方
lemma square_relation (n : ℕ) :
  (x (n + 1)) ^ 2 - (x n) ^ 2 = (1 / x n) ^ 2 + 2 := by
  have h11 : (x (n + 1)) ^ 2 = (x n) ^ 2 + (1 / x n) ^ 2 + 2 := by
    have hx0 := x_pos n
    rw [x]
    field_simp [ne_of_gt hx0]
    ring
  rw [h11]
  ring

-- 累加公式
lemma sum_relation (n : ℕ) :
  (x (n + 1))^2 = 25 + 2 * (n + 1) + ∑ k ∈ Finset.range (n + 1), (1 / (x k)^2) := by
  -- Step 1: 证明伸缩和引理 (通过归纳法)
  have h21 : (x (n + 1))^2 = (x 0)^2 + ∑ k ∈ Finset.range (n + 1), ((x (k + 1))^2 - (x k)^2) := by
    -- 用 telescoping（错位相减）基本恒等式
    induction n with
    | zero =>
      rw [Finset.sum_range_succ]
      ring
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have h22 : ∀ k ∈ Finset.range (n + 1), (x (k + 1))^2 - (x k)^2 = (1 / (x k))^2 + 2 := by
    intros k hk
    exact square_relation k
  rw [Finset.sum_congr rfl h22] at h21
  rw [Finset.sum_add_distrib] at h21
  have h_sum_two : ∑ x ∈ Finset.range (n + 1), 2 = 2 * (n + 1) := by
  -- Finset.sum_const 是定理 ∑ c = s.card * c
    rw [Finset.sum_const]
    rw [Finset.card_range (n + 1)]
    rw [smul_eq_mul]
    rw [mul_comm]
  -- 不知道为什么无法 rw
  -- rw [h_sum_two] at h21

  -- simp at h21
  -- exact h21
  sorry

-- 对 x_{1000}^2 做初步整理
-- 文中 式(7)
lemma x_1000_square_7 : (x 1000)^2 = 2025 + ∑ k ∈ Finset.range 1000, (1 / (x k)^2) := by
  have h31 : (x 1000)^2 = 25 + 2 * 1000 + ∑ k ∈ Finset.range 1000, (1 / (x k)^2) := by
    simp [sum_relation 999]
    ring
  rw [h31]
  ring

-- 文中 式(10)
lemma x_1000_square_10 : (x 1000)^2 = 2025 + ∑ k ∈ Finset.range 100, (1 / (x k)^2) + ∑ k ∈ Finset.Ico 100 1000, (1 / (x k)^2) := by
  rw [x_1000_square_7]
  -- 手动分解求和范围
  have h_split : ∑ k ∈ Finset.range 1000, (1 / (x k)^2) =
    ∑ k ∈ Finset.range 100, (1 / (x k)^2) + ∑ k ∈ Finset.Ico 100 1000, (1 / (x k)^2) := by
    exact Finset.sum_range_add_sum_Ico (λ k : ℕ, (1 / (x k)^2 : ℝ)) 100 1000
  rw [h_split]
  simp









-- 证明 x_{1000}^2 > 2025
lemma lower_bound : (x 1000)^2 > 2025 := by
  have h51 : ∑ k ∈ Finset.range 1000, (1 / (x k)^2) > 0 := by
    have h56 : (Finset.range 1000).Nonempty := by
      use 0 -- Finset.range 1000 包含 0
      simp

    have h52 : ∀ i : ℕ , 1 / (x i)^2 > 0 := by
      have h53 : ∀ i : ℕ , (x i)^2 > 0 := by
        intro i
        have h54 := x_pos i -- 从 x_pos 引理得出 x i > 0
        exact pow_pos h54 2 -- x i > 0 推导出 (x i)^2 > 0
      intro i
      have h55 := h53 i -- (x i)^2 > 0
      exact one_div_pos.mpr h55 -- (x i)^2 > 0 推到数
    -- exact Finset.sum_pos h56 h52
    sorry -- 不知道为什么 Finset.sum_pos 不能直接使用
  rw [x_1000_square_7]
  exact lt_add_of_pos_right 2025 h51






lemma x0_xk_square_reciprocal_le : ∀ k : ℕ,1 / (x k) ^ 2 ≤ 1 / (x 0) ^ 2 := by
  intro k
  have h_mono_le : x 0 ≤ x k := x_mono_le 0 k (Nat.zero_le k)
  -- 证明 x 0 和 x k 都是非负数
  have h_sq_le : (x 0)^2 ≤ (x k)^2 := by
    rw [pow_two, pow_two]
    have h_x0_nonneg : 0 ≤ x 0 := (x_pos 0).le
    have h_xk_nonneg : 0 ≤ x k := (x_pos k).le
    have h_step1 : (x 0) * (x 0) ≤ (x 0) * (x k) := by
      exact mul_le_mul_of_nonneg_left h_mono_le h_x0_nonneg
    have h_step2 : (x 0) * (x k) ≤ (x k) * (x k) := by
      exact mul_le_mul_of_nonneg_right h_mono_le h_xk_nonneg
    exact le_trans h_step1 h_step2
  have h_x0_sq_pos : 0 < (x 0)^2 := by
    exact pow_pos (x_pos 0) 2
  -- 使用倒数的单调性
  -- have h_reciprocal : 1 / (x k)^2 ≤ 1 / (x 0)^2 := by
  exact one_div_le_one_div_of_le h_x0_sq_pos h_sq_le



-- 证明 x_{1000}^2 < 2033
lemma upper_bound : (x 1000)^2 < 2033 := by
  rw [x_1000_square_10]
  have h61 : ∑ k ∈ Finset.range 100, 1 / (x k) ^ 2 ≤ 4 := by
    have h62 : ∑ k ∈ Finset.range 100, 1 / (x k) ^ 2 ≤ 100 / (x 0)^2 := by
      exact Finset.sum_le_sum (x0_xk_square_reciprocal_le 100)

-- -- 最终结论
-- theorem final_result : 45 < x 1000 ∧ x 1000 < 45.1 := by
--   have h1 : (x 1000)^2 > 2025 := lower_bound
--   have h2 : (x 1000)^2 < 2033 := upper_bound
--   split
--   · apply Real.sqrt_lt'.mpr
--     · positivity
--     · exact h1
--   · apply Real.lt_sqrt'.mpr
--     · positivity
--     · exact h2
