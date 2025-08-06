import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
-- import Mathlib.Algebra.Order.Basic

namespace Ex3LeanAct
open Real Nat
-- 定义全局变量和递归关系
variable (n : ℕ)

noncomputable def x : ℕ → ℝ
| 0       => 5
| (n + 1) => x n + 1 / x n

-- lean中无计算超越函数的策略或定理,故此处采用常数近似
def e_1 : ℝ := 2.7

lemma exp_gt_2_7 : e_1 < Real.exp 1  := by
  sorry


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

-- 平方公式,对x (n+1) 展开平方
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
    ring
  have h23 : (x 0)^2 = 25 := by
    rw [x]
    norm_num

  simp at h21
  rw [h21]
  rw [h23] at h21
  simp
  ring_nf
  simp
  rw [h23]
  ring

-- 求和倒数平方大于0
lemma sum_x_square_pos (n : ℕ) :
  ∑ k ∈ Finset.range (n+1), (1 / (x k)^2) > 0 := by
  have h52 : ∀ i : ℕ ,0 < 1 / (x i)^2 := by
    have h53 : ∀ i : ℕ , 0 < (x i)^2 := by
      intro i
      have h54 := x_pos i -- 从 x_pos 引理得出 x i > 0
      exact pow_pos h54 2 -- x i > 0 推导出 (x i)^2 > 0
    intro i
    have h55 := h53 i -- (x i)^2 > 0
    exact one_div_pos.mpr h55 -- (x i)^2 > 0 推到数

  have h56 : (Finset.range (n+1)).Nonempty := by
    use 0 -- Finset.range 1000 包含 0
    simp

  have h57 : ∀ i ∈ Finset.range (n+1), 0 < 1 / (x i)^2 := by
    intro i hi
    exact h52 i
  -- 第一项 为 范围内均大于0 ; 第二项为集合非空
  exact Finset.sum_pos h57 h56

-- 平方不等式
lemma x_square_ge (n : ℕ) :
  (x (n + 1))^2 ≥ 25 + 2 * (n + 1) := by
  rw [sum_relation n]
  simp
  have h1 : ∑ k ∈ Finset.range (n + 1), (1 / (x k)^2) > 0 := sum_x_square_pos n
  have h_eq : ∑ k ∈ Finset.range (n + 1), 1 / (x k ^ 2)
          = ∑ k ∈ Finset.range (n + 1), (x k ^ 2)⁻¹ := by
    apply Finset.sum_congr rfl
    intro i hk
    rw [inv_eq_one_div]
  simp
  have h2 : ∑ k ∈ Finset.range (n + 1), (x k ^ 2)⁻¹ > 0 := by
    rw [← h_eq]
    exact h1
  exact le_of_lt h2

lemma x_square_div_ge (n : ℕ) :
  1 / (x (n + 1))^2 ≤ 1/(25 + 2 * (n + 1)) := by
  sorry

-- 求和倒数平方对数证明
lemma sum_x_square_lt_log (n : ℕ) : ∑ k ∈ Finset.range (n + 1), (1 / (x k)^2) < (1 + Real.log n) / 2 := by
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

lemma x_1000_square_10 :
  (x 1000)^2 =
  2025 + ∑ k ∈ Finset.range 100, (1 / (x k)^2) + ∑ k ∈ Finset.Ico 100 1000, (1 / (x k)^2) := by

  rw [x_1000_square_7]

  -- 明确定义求和函数 f
  let f : ℕ → ℝ := fun k => 1 / (x k)^2

  have hmn : 100 ≤ 1000 := by simp

  -- 手动分解求和范围
  have h_split :
  ∑ k ∈ Finset.range 1000, f k = ∑ k ∈ Finset.range 100, f k + ∑ k ∈ Finset.Ico 100 1000, f k := by
    -- 直接使用 f
    exact (Finset.sum_range_add_sum_Ico f hmn).symm

  rw [h_split]
  simp [f]
  ring

-- 证明 x_{1000}^2 > 2025
lemma lower_bound : (x 1000)^2 > 2025 := by
  have h51 : ∑ k ∈ Finset.range 1000, (1 / (x k)^2) > 0 := sum_x_square_pos 999

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
  exact one_div_le_one_div_of_le h_x0_sq_pos h_sq_le

  -- 证明 x_{1000}^2 < 2033
  lemma upper_bound : (x 1000)^2 < 2034 := by
  rw [x_1000_square_7]

  have h1 :∑ k ∈ Finset.range 1000, 1 / x k ^ 2 < 45.1 := by
    have h_range : Finset.range 1000 = Finset.range (999 + 1) := by simp
    rw [h_range]
    have h_result := sum_x_square_lt_log 999
    have h1 : (999 : ℝ) < Real.exp 49.2 := by
      have h2 : (999 : ℝ) < e_1 ^ 7 := by
        have h3 : e_1 ^ 7 = 2.7 ^ 7 := rfl
        rw [h3]
        norm_num
      have h4 : e_1 ^ 7 < Real.exp 49.2 := by
        have h5 : e_1 < Real.exp 1 := exp_gt_2_7
        have h6 : e_1 ^ 7 < Real.exp 1 ^ 7 := by
        -- 不知为何 pow_le_pow_of_le 无法使用
          -- pow_le_pow_of_le (by norm_num) h5 (by norm_num)
          sorry
        have h7 : Real.exp 1 ^ 7 < Real.exp 49.2 := by
          sorry
        sorry
      sorry

    have h_div_1 : (1 + Real.log 999) / 2 < 45.1 := by
      sorry

    sorry

  sorry


--
  -- have h601 : ∑ k ∈ Finset.range 100, 1 / (x k) ^ 2 ≤ 4 := by
  --   have h602 : ∑ k ∈ Finset.range 100, 1 / (x k) ^ 2 ≤ 100 / (x 0)^2 := by
  --     have h603 : ∀ k ∈ Finset.range 100, 1 / (x k)^2 ≤ 1 / (x 0)^2 := by
  --       intro k hk
  --       exact x0_xk_square_reciprocal_le k

  --     have h604 : ∑ k ∈ Finset.range 100, 1 / (x 0)^2 = 100 / (x 0)^2 := by
  --       rw [Finset.sum_const]
  --       rw [Finset.card_range 100]
  --       ring

  --     have h605 : ∑ k ∈ Finset.range 100, 1 / (x k)^2 ≤ ∑ k ∈ Finset.range 100, 1 / (x 0)^2 := by
  --       exact Finset.sum_le_sum h603

  --     exact le_of_le_of_eq h605 h604

  --   have h606 : 100 / (x 0)^2 = 4 := by
  --     rw [x]
  --     norm_num

  --   rw [h606] at h602
  --   exact h602
  -- have h607 : ∑ k ∈ Finset.Ico 100 1000, 1 / (x k)^2 ≤ 4 := by
  --   have h608 : ∑ k ∈ Finset.Ico 100 1000, 1 / (x k)^2 ≤ 900 / (x 100)^2 := by
  --     have h609 : ∀ k ∈ Finset.Ico 100 1000, 1 / (x k)^2 ≤ 1 / (x 100)^2 := by
  --       intro k hk

  --       -- ! 不等式传递以及求和范围 Finset.Ico 100 1000 表示困难
  --       sorry
  --     sorry
  --   sorry

  -- have h_sum : ∑ k ∈ Finset.range 100, 1 / x k ^ 2 + ∑ k ∈ Finset.Ico 100 1000, 1 / x k ^ 2 ≤ 4 + 4 := by
  --   exact add_le_add h601 h607

  -- -- 将 h_sum 应用到整个表达式
  -- have h_le_val : (x 1000)^2 ≤ 2025 + (4 + 4) := by
  --   rw [x_1000_square_10]

  --   -- ! 不等式传递
  --   sorry

  -- have h_const_val : 2025 + (4 + 4) = 2033 := by
  --   norm_num

  -- have h_lt_val : 2033 < 2034 := by
  --   norm_num

  -- -- ! 不等式传递
  -- sorry
--


-- 由以上的证明，我们可以得出最终的结论
theorem final_result : 45 < x 1000 ∧ x 1000 < 45.1 := by
  have h_pos : 0 < x 1000 := x_pos 1000
  have h_sqre_2025 : 2025 = (45)^2 := by
    norm_num
  have h_square_2034 : (2034 : ℝ ) < (45.1)^2 := by
    norm_num
  have h81 : (x 1000)^2 > 2025 := lower_bound
  have h82 : (x 1000)^2 < 2034 := upper_bound
  --! 不等式传递 开根号,不会表示
  sorry

end Ex3LeanAct
