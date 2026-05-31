/-
Goldbach 猜想 —— Lean 4 形式化补充层

**与 PNT 项目的关系**：
PrimeNumberTheoremAnd 的 `IEANTN/Goldbach.lean` 已经形式化了：
- `even_conjecture` / `odd_conjecture`（与本文件早期版本重复，已删）
- `even_to_odd_goldbach_triv`（= 我们的 `strong_implies_weak`）
- 数值上界：`ramare_saouter_odd_goldbach` (≤ 1.13×10²²)、
  `helfgott_odd_goldbach_finite` (≤ 1.13×10²⁶)、
  `kadiri_lumley_odd_goldbach_finite` (≤ 7.78×10²⁷)
**全部已证毕**（剩 2 个 sorry 是 Richstein/eSHP 的 80GB 数值验证）。

**所以本文件只保留 PNT 没做的部分**：
1. 强 Goldbach (n → ∞)（PNT 完全没碰）
2. Hardy-Littlewood 定量渐近（PNT 完全没碰）
3. r(n) 计数函数（PNT 完全没碰）
4. 强→弱蕴含（PNT 的版本是有限版 H+3，我们写无限版）

参考：
- Goldbach (1742): 每个偶数 ≥ 4 都可以写成两个素数之和
- Vinogradov (1937): 充分大的奇数是三个素数之和
- Helfgott (2013, arXiv:1305.2897): 弱 Goldbach 完全证明（≥ 7 的奇数 = 3 素数）
- Oliveira e Silva 等 (2014): 强 Goldbach 数值验证至 4 × 10^18
-/

import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace Goldbach

/-- **强 Goldbach 猜想**（无限版，对所有 n ≥ 4 偶）。
    OPEN since 1742. 数值验证至 4×10^18 (Oliveira e Silva, 2014). -/
def StrongGoldbach : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- **弱 Goldbach 定理**（无限版，对所有 n ≥ 7 奇）。
    PROVED by Helfgott (2013), 350-page proof, NOT YET fully formalized in Lean.
    PNT 项目已证到 n ≤ 7.78×10²⁷（Kadiri-Lumley），剩 (7.78×10²⁷, ∞) 的渐近部分。 -/
def WeakGoldbach : Prop :=
  ∀ n : ℕ, 7 ≤ n → Odd n → ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n

/-- **强蕴含弱**（无限版，trivial direction）：取 n - 3 为偶数 ≥ 4，应用强 Goldbach。
    与 PNT 的 `even_to_odd_goldbach_triv` 不同，这是 H → ∞ 版本。 -/
theorem strong_implies_weak : StrongGoldbach → WeakGoldbach := by
  intro hSG n hn hodd
  have h3le : 3 ≤ n := by omega
  have hsub_ge : 4 ≤ n - 3 := by omega
  have hsub_even : Even (n - 3) := by
    rcases hodd with ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    omega
  obtain ⟨p, q, hp, hq, hpq⟩ := hSG (n - 3) hsub_ge hsub_even
  refine ⟨p, q, 3, hp, hq, by decide, ?_⟩
  omega

/-- **奇偶必要条件**：两素数之和奇 ⇒ 其中之一是 2。 -/
theorem two_primes_sum_parity (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hodd : Odd (p + q)) :
    p = 2 ∨ q = 2 := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hp2, hq2⟩ := h
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  exact (Nat.not_odd_iff_even.mpr (Odd.add_odd hpodd hqodd)) hodd

/-! ## Goldbach 计数函数与 Hardy-Littlewood 渐近（PNT 项目未覆盖） -/

/-- **Goldbach 计数函数** r(n) := #{(p,q) : p ≤ q, p+q=n, p,q 素数}。
    Hardy-Littlewood 猜测：r(n) ~ 𝔖(n) · n / log² n
    其中 𝔖(n) = 2 C₂ · ∏_{p|n,p>2} ((p-1)/(p-2)) 是奇异级数。 -/
noncomputable def goldbachCount (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (fun p =>
    p.Prime ∧ (n - p).Prime ∧ p ≤ n - p) |>.card

/-- **Hardy-Littlewood 渐近猜想**（强 Goldbach 的定量版本）。
    比强 Goldbach 更强：不仅有解，而且解的数量按预期渐近增长。
    OPEN. 经验上 r(n) / (𝔖(n) · n / log²(n)) → 1，但 N=10⁴ 时比值还在 0.6 左右
    （数值实验见 `experiments/numerical/singular_series.py`）。 -/
def HardyLittlewoodAsymptotic : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, Even n →
      |((goldbachCount n : ℝ) - C * n / (Real.log n)^2)| < ε * n / (Real.log n)^2

/-- **HL 蕴含 强 Goldbach**（充分大 n）：HL 渐近 ⇒ 对充分大偶 n 必有 Goldbach 分解。
    这建立了"渐近"与"存在性"两种 OPEN 问题间的关系。 -/
theorem hl_implies_strong_large : HardyLittlewoodAsymptotic →
    ∃ N : ℕ, ∀ n ≥ N, Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  rintro ⟨C, hC, hHL⟩
  obtain ⟨N, hN⟩ := hHL (C / 2) (by linarith)
  refine ⟨max N 2, fun n hn hEven => ?_⟩
  have hnN : N ≤ n := le_of_max_le_left hn
  have hn2 : 2 ≤ n := le_of_max_le_right hn
  have hn_pos : (0 : ℝ) < n :=
    by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hn2
  have hlog_pos : 0 < Real.log n := by
    apply Real.log_pos
    exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hn2
  have hlog_sq_pos : 0 < (Real.log n)^2 := pow_pos hlog_pos 2
  have hbound := hN n hnN hEven
  have habs := abs_sub_lt_iff.mp hbound
  have hr_pos_real : (0 : ℝ) < goldbachCount n := by
    have h1 : (goldbachCount n : ℝ) > C * n / (Real.log n)^2 - C / 2 * n / (Real.log n)^2 := by
      linarith [habs.1]
    have hquarter : C / 2 * n / (Real.log n)^2 > 0 := by positivity
    have : C * ↑n / (Real.log ↑n) ^ 2 - C / 2 * ↑n / (Real.log ↑n) ^ 2
        = C / 2 * ↑n / (Real.log ↑n) ^ 2 := by ring
    linarith
  have hr_nat_pos : 0 < goldbachCount n := by exact_mod_cast hr_pos_real
  unfold goldbachCount at hr_nat_pos
  obtain ⟨p, hp_mem⟩ := Finset.card_pos.mp hr_nat_pos
  rw [Finset.mem_filter, Finset.mem_range] at hp_mem
  obtain ⟨hp_range, hp_prime, hnp_prime, _⟩ := hp_mem
  refine ⟨p, n - p, hp_prime, hnp_prime, ?_⟩
  omega

/-! ## 小 case 验证（by decide） -/

theorem goldbach_4 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 4 :=
  ⟨2, 2, by decide, by decide, rfl⟩

theorem goldbach_6 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 6 :=
  ⟨3, 3, by decide, by decide, rfl⟩

theorem goldbach_8 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 8 :=
  ⟨3, 5, by decide, by decide, rfl⟩

theorem goldbach_10 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 10 :=
  ⟨3, 7, by decide, by decide, rfl⟩

theorem weak_goldbach_7 : ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = 7 :=
  ⟨2, 2, 3, by decide, by decide, by decide, rfl⟩

theorem weak_goldbach_9 : ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = 9 :=
  ⟨3, 3, 3, by decide, by decide, by decide, rfl⟩

/-! ## 由 Claude (Opus 4.7) 写的若干结构性引理 -/

/-- **r(n) 与存在性等价**：r(n) > 0 当且仅当 n 有 Goldbach 分解（且 n ≥ 4 偶）。 -/
theorem goldbachCount_pos_iff (n : ℕ) (_hn : 4 ≤ n) (_hEven : Even n) :
    0 < goldbachCount n ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  unfold goldbachCount
  constructor
  · intro h
    obtain ⟨p, hp⟩ := Finset.card_pos.mp h
    rw [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨_, hp_prime, hnp_prime, _⟩ := hp
    exact ⟨p, n - p, hp_prime, hnp_prime, by omega⟩
  · rintro ⟨p, q, hp, hq, hpq⟩
    apply Finset.card_pos.mpr
    by_cases hpq' : p ≤ q
    · refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp, ?_, ?_⟩⟩
      · omega
      · have : n - p = q := by omega
        rw [this]; exact hq
      · omega
    · refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hq, ?_, ?_⟩⟩
      · omega
      · have : n - q = p := by omega
        rw [this]; exact hp
      · omega

/-- **强 Goldbach 与 r(n) 正性的等价**。 -/
theorem strongGoldbach_iff_count_pos :
    StrongGoldbach ↔ ∀ n : ℕ, 4 ≤ n → Even n → 0 < goldbachCount n := by
  unfold StrongGoldbach
  refine ⟨fun h n hn hE => (goldbachCount_pos_iff n hn hE).mpr (h n hn hE), ?_⟩
  intro h n hn hE
  exact (goldbachCount_pos_iff n hn hE).mp (h n hn hE)

/-- **奇偶联合必要条件**：n ≥ 4 偶 ⇒ Goldbach 分解中两素数同奇偶（同 ≥3，或都 = 2）。 -/
theorem goldbach_decomp_parity (n p q : ℕ) (_hn : 4 ≤ n) (hEven : Even n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p + q = n) :
    (p = 2 ∧ q = 2 ∧ n = 4) ∨ (Odd p ∧ Odd q) := by
  by_cases hp2 : p = 2
  · by_cases hq2 : q = 2
    · left; exact ⟨hp2, hq2, by omega⟩
    · exfalso
      have hqodd : Odd q := hq.odd_of_ne_two hq2
      rcases hqodd with ⟨k, hk⟩
      rcases hEven with ⟨m, hm⟩
      omega
  · by_cases hq2 : q = 2
    · exfalso
      have hpodd : Odd p := hp.odd_of_ne_two hp2
      rcases hpodd with ⟨k, hk⟩
      rcases hEven with ⟨m, hm⟩
      omega
    · right
      exact ⟨hp.odd_of_ne_two hp2, hq.odd_of_ne_two hq2⟩

/-- **强 Goldbach ⇒ 弱 Goldbach（≥ 9 奇）的另一证法**：用 n - 3 偶 ≥ 4，且第三素数恒为 3。 -/
theorem strong_implies_weak_via_four_minus :
    StrongGoldbach → ∀ n : ℕ, 9 ≤ n → Odd n →
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n ∧ r = 3 := by
  intro hSG n hn hodd
  have hsub_even : Even (n - 3) := by
    rcases hodd with ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    omega
  obtain ⟨p, q, hp, hq, hpq⟩ := hSG (n - 3) (by omega) hsub_even
  exact ⟨p, q, 3, hp, hq, by decide, by omega, rfl⟩

/-! ## 数论副产物（mathlib 已有但 Goldbach 论证常用） -/

/-- **奇素数的最小者是 3**：任何奇素数 ≥ 3。-/
theorem odd_prime_ge_three (p : ℕ) (hp : p.Prime) (hodd : Odd p) : 3 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  rcases eq_or_lt_of_le h2 with heq | hlt
  · exfalso
    have : p = 2 := heq.symm
    rw [this] at hodd
    exact (Nat.not_odd_iff_even.mpr (by decide : Even 2)) hodd
  · omega

/-- **强 Goldbach 在 n=4 时不需要假设也成立**。 -/
theorem strong_goldbach_at_4 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 4 := goldbach_4

/-- **r(n) 上界**：r(n) ≤ n+1（粗略，对所有 n）。
    更精确的上界（如 Brun 筛）给出 r(n) ≪ n/log²n，但这里只给一个 trivially 可证版本。 -/
theorem goldbachCount_trivial_upper (n : ℕ) :
    goldbachCount n ≤ n + 1 := by
  unfold goldbachCount
  exact le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range _))

/-- **若 n 偶 ≥ 4 且 n - 3 不是素数，则 Goldbach 分解中没有 (3, n-3)**。 -/
theorem goldbach_no_3_decomp (n : ℕ) (_hn : 4 ≤ n) (_hEven : Even n)
    (h3 : ¬ (n - 3).Prime) :
    ∀ p q : ℕ, p.Prime → q.Prime → p + q = n → p ≠ 3 ∧ q ≠ 3 := by
  intro p q hp hq hpq
  constructor
  · intro hp3
    apply h3
    have : n - 3 = q := by omega
    rw [this]; exact hq
  · intro hq3
    apply h3
    have : n - 3 = p := by omega
    rw [this]; exact hp

/-- **Goldbach 分解的对称性**：(p, q) 是分解 ⇔ (q, p) 是分解。 -/
theorem goldbach_symm (n p q : ℕ) :
    (p.Prime ∧ q.Prime ∧ p + q = n) ↔ (q.Prime ∧ p.Prime ∧ q + p = n) := by
  constructor
  · rintro ⟨hp, hq, h⟩; exact ⟨hq, hp, by omega⟩
  · rintro ⟨hq, hp, h⟩; exact ⟨hp, hq, by omega⟩

/-! ## Hardy-Littlewood 路线的辅助引理 -/

/-- **强 Goldbach 等价命题 1**：每个 ≥ 4 偶数 n，集合 {p 素 : p ≤ n/2, n-p 素} 非空。 -/
theorem strongGoldbach_iff_decomp_set_nonempty :
    StrongGoldbach ↔ ∀ n : ℕ, 4 ≤ n → Even n →
      ((Finset.range (n + 1)).filter
        (fun p => p.Prime ∧ (n - p).Prime ∧ p ≤ n - p)).Nonempty := by
  rw [strongGoldbach_iff_count_pos]
  refine ⟨fun h n hn hE => ?_, fun h n hn hE => ?_⟩
  · exact Finset.card_pos.mp (h n hn hE)
  · exact Finset.card_pos.mpr (h n hn hE)

/-- **存在性意义下的 r(n) 单调性**（不是数值单调，而是逻辑：r(n)>0 ⇒ Goldbach 在 n 成立）。 -/
theorem goldbach_at_n_iff (n : ℕ) (hn : 4 ≤ n) (hE : Even n) :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n) ↔ 0 < goldbachCount n :=
  (goldbachCount_pos_iff n hn hE).symm

/-- **强 Goldbach 的 contrapositive 形式**：若某偶数 n ≥ 4 无 Goldbach 分解，
    则 StrongGoldbach 不成立（作为反证陈述模板）。 -/
theorem not_strongGoldbach_of_counterexample (n : ℕ) (hn : 4 ≤ n) (hE : Even n)
    (h_no : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n) :
    ¬ StrongGoldbach := fun hSG => h_no (hSG n hn hE)

/-- **弱 Goldbach 的 contrapositive 形式**。 -/
theorem not_weakGoldbach_of_counterexample (n : ℕ) (hn : 7 ≤ n) (hO : Odd n)
    (h_no : ¬ ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n) :
    ¬ WeakGoldbach := fun hWG => h_no (hWG n hn hO)

/-! ## 更多结构性引理（数值实验启发） -/

/-- **HL 渐近 ⇒ 充分大 r(n) 严格正**（更精细版本，标出依赖于 ε = C/2 的下界）。 -/
theorem hl_implies_count_lower_bound : HardyLittlewoodAsymptotic →
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, Even n → 2 ≤ n →
      (C / 2) * n / (Real.log n)^2 < goldbachCount n := by
  rintro ⟨C, hC, hHL⟩
  refine ⟨C, hC, ?_⟩
  obtain ⟨N, hN⟩ := hHL (C / 2) (by linarith)
  refine ⟨max N 2, fun n hn hEven _hn2 => ?_⟩
  have hnN : N ≤ n := le_of_max_le_left hn
  have hbound := hN n hnN hEven
  have habs := abs_sub_lt_iff.mp hbound
  have heq : C * (n : ℝ) / (Real.log n)^2 - C / 2 * n / (Real.log n)^2
      = C / 2 * n / (Real.log n)^2 := by ring
  linarith [habs.1]

/-- **Goldbach 偶数最大素因子下界**：如果 p + q = n 是 Goldbach 分解，
    那么 max(p, q) ≥ n / 2。 -/
theorem goldbach_max_prime_lower (n p q : ℕ) (hpq : p + q = n) :
    n ≤ 2 * max p q := by
  have h := le_max_left p q
  have h' := le_max_right p q
  omega

/-- **Goldbach 分解中最小素至多 n / 2**。 -/
theorem goldbach_min_prime_upper (n p q : ℕ) (hpq : p + q = n) :
    2 * min p q ≤ n := by
  have h := min_le_left p q
  have h' := min_le_right p q
  omega

/-- **强 Goldbach 蕴含 Schnirelmann 密度全集**（任何充分大偶数都是两素数和）。 -/
theorem strongGoldbach_implies_full_density :
    StrongGoldbach →
    ∀ n : ℕ, 4 ≤ n → Even n →
      ∃ p ∈ {p : ℕ | p.Prime ∧ p ≤ n}, (n - p).Prime := by
  intro hSG n hn hE
  obtain ⟨p, q, hp, hq, hpq⟩ := hSG n hn hE
  refine ⟨p, ⟨hp, ?_⟩, ?_⟩
  · omega
  · have : n - p = q := by omega
    rw [this]; exact hq

/-- **r(n) 与 r(n+2) 无单调关系** 的断言形式（陈述，非定理；
    实际上 r(n) 在不同 n 上波动很大，见 `experiments/numerical/singular_series.py`）。 -/
def goldbachCount_not_monotone_statement : Prop :=
  ∀ n : ℕ, goldbachCount n ≤ goldbachCount (n + 2)

/-- **r(4) = 1**：唯一分解 4 = 2 + 2。 -/
theorem goldbachCount_4 : goldbachCount 4 = 1 := by decide

/-- **r(6) = 1**：唯一分解 6 = 3 + 3。 -/
theorem goldbachCount_6 : goldbachCount 6 = 1 := by decide

/-- **r(10) = 2**：分解 10 = 3 + 7 和 10 = 5 + 5。 -/
theorem goldbachCount_10 : goldbachCount 10 = 2 := by decide

end Goldbach
