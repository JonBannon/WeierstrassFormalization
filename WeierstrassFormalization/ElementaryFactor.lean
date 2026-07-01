/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.Basic

/-!
# Modified elementary factors

Formalizes Section 2 of the paper: the modified Weierstrass elementary
factor `E_n(w; c)` and the structural Lemma `lem:structure`.
-/

namespace Weierstrass

open Complex
open scoped Topology

/-- The modified elementary factor of order `n` with parameter `c`,
\[
  E_n(w;\,c) = (1-w)\exp\Bigl(\sum_{k=1}^{n}\frac{w^k}{k} +
    \frac{c\,w^{n+1}}{n+1}\Bigr).
\]
For `c = 1` this is the classical Weierstrass elementary factor. -/
noncomputable def E (n : ℕ) (c w : ℂ) : ℂ :=
  (1 - w) * Complex.exp ((∑ k ∈ Finset.Icc 1 n, w ^ k / k) + c * w ^ (n + 1) / (n + 1))

/-- The exponent `G_n(w;c)` from \eqref{eq:Gdef}, valid for `w ∈ 𝔻`:
\[
  G_n(w;\,c) = \frac{(c-1)\,w^{n+1}}{n+1} - \sum_{k=n+2}^{\infty}\frac{w^k}{k}.
\]
-/
noncomputable def G (n : ℕ) (c w : ℂ) : ℂ :=
  (c - 1) * w ^ (n + 1) / (n + 1) - ∑' k : ℕ, if k ≥ n + 2 then w ^ k / k else 0

/-- **Lemma (Structure of the modified factor), Eq. (2.3)–(2.4).**
On the disk, `E_n(w;c) = exp(G_n(w;c))`. -/
theorem E_eq_exp_G {n : ℕ} {c w : ℂ} (hw : w ∈ 𝔻) :
    E n c w = Complex.exp (G n c w) := by
  have hw' : ‖w‖ < 1 := mem_𝔻_iff.mp hw
  have hw1 : w ≠ 1 := by
    intro h; rw [h, norm_one] at hw'; exact lt_irrefl 1 hw'
  set f0 : ℕ → ℂ := fun k => w ^ k / k with hf0_def
  have hSum0 : HasSum f0 (-Complex.log (1 - w)) := Complex.hasSum_taylorSeries_neg_log hw'
  have hSummable0 : Summable f0 := hSum0.summable
  have htsum0 : ∑' k, f0 k = -Complex.log (1 - w) := hSum0.tsum_eq
  have hf00 : f0 0 = 0 := by simp [hf0_def]
  -- the tail sum `T` agrees with the shifted tsum `∑' i, f0 (i + (n+2))`
  have hginj : Function.Injective (fun i : ℕ => i + (n + 2)) := add_left_injective (n + 2)
  have hfzero : ∀ x, x ∉ Set.range (fun i : ℕ => i + (n + 2)) →
      (if x ≥ n + 2 then f0 x else 0) = 0 := by
    intro x hx
    rw [if_neg]
    intro hge
    exact hx ⟨x - (n + 2), Nat.sub_add_cancel hge⟩
  have hshiftSummable : Summable (fun i : ℕ => f0 (i + (n + 2))) :=
    (summable_nat_add_iff (n + 2)).2 hSummable0
  have hcomp : (fun k : ℕ => if k ≥ n + 2 then f0 k else 0) ∘ (fun i : ℕ => i + (n + 2))
      = fun i : ℕ => f0 (i + (n + 2)) := by
    funext i
    simp only [Function.comp_apply]
    rw [if_pos (Nat.le_add_left (n + 2) i)]
  have hTHasSum : HasSum (fun k : ℕ => if k ≥ n + 2 then f0 k else 0) (∑' i, f0 (i + (n + 2))) :=
    (hginj.hasSum_iff hfzero).mp (hcomp ▸ hshiftSummable.hasSum)
  have hT_eq : (∑' k : ℕ, if k ≥ n + 2 then f0 k else 0) = ∑' i, f0 (i + (n + 2)) :=
    hTHasSum.tsum_eq
  -- split the full series at `n + 2`
  have hsplit : (∑ i ∈ Finset.range (n + 2), f0 i) + ∑' i, f0 (i + (n + 2)) = ∑' i, f0 i :=
    Summable.sum_add_tsum_nat_add (n + 2) hSummable0
  have hrange : ∑ i ∈ Finset.range (n + 2), f0 i
      = (∑ k ∈ Finset.Icc 1 n, f0 k) + f0 (n + 1) := by
    have hLHS : ∑ i ∈ Finset.range (n + 2), f0 i
        = (∑ k ∈ Finset.range n, f0 (k + 1)) + f0 (n + 1) := by
      rw [show n + 2 = n + 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ', hf00,
        add_zero]
    have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have hRHS : ∑ k ∈ Finset.Icc 1 n, f0 k = ∑ k ∈ Finset.range n, f0 (k + 1) := by
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      exact Finset.sum_congr rfl (fun k _ => by rw [add_comm])
    rw [hLHS, hRHS]
  have hkey : (∑ k ∈ Finset.Icc 1 n, f0 k) + f0 (n + 1)
      + (∑' k : ℕ, if k ≥ n + 2 then f0 k else 0) = -Complex.log (1 - w) := by
    rw [hT_eq, ← hrange, hsplit, htsum0]
  have hB_eq : G n c w = Complex.log (1 - w)
      + ((∑ k ∈ Finset.Icc 1 n, w ^ k / k) + c * w ^ (n + 1) / (n + 1)) := by
    have hf0_succ : f0 (n + 1) = w ^ (n + 1) / (n + 1) := by
      simp only [hf0_def]; push_cast; ring
    rw [hf0_succ] at hkey
    unfold G
    field_simp at hkey ⊢
    linear_combination -hkey
  rw [hB_eq, Complex.exp_add, Complex.exp_log (sub_ne_zero.mpr hw1.symm)]
  rfl

/-- **Lemma `lem:structure` (i).** `E_n(0;c) = 1`. -/
theorem E_zero (n : ℕ) (c : ℂ) : E n c 0 = 1 := by
  unfold E
  have hsum : ∑ k ∈ Finset.Icc 1 n, (0 : ℂ) ^ k / k = 0 := by
    refine Finset.sum_eq_zero (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    simp [zero_pow (Nat.one_le_iff_ne_zero.mp hk.1)]
  simp [hsum]

/-- The exponent appearing in the definition of `E`, as a standalone function. -/
private noncomputable def auxQ (n : ℕ) (c w : ℂ) : ℂ :=
  (∑ k ∈ Finset.Icc 1 n, w ^ k / k) + c * w ^ (n + 1) / (n + 1)

/-- `log (1 - w) + auxQ n c w`: agrees with `E n c` after taking `exp`, away from `w = 1`. -/
private noncomputable def auxK (n : ℕ) (c w : ℂ) : ℂ :=
  Complex.log (1 - w) + auxQ n c w

private lemma E_eq_exp_auxK {n : ℕ} {c w : ℂ} (hw1 : w ≠ 1) :
    E n c w = Complex.exp (auxK n c w) := by
  have h1w : (1 : ℂ) - w = Complex.exp (Complex.log (1 - w)) :=
    (Complex.exp_log (sub_ne_zero.mpr hw1.symm)).symm
  unfold E auxK auxQ
  conv_lhs => rw [h1w]
  rw [← Complex.exp_add]

private lemma analyticAt_auxQ (n : ℕ) (c w : ℂ) : AnalyticAt ℂ (auxQ n c) w := by
  unfold auxQ
  fun_prop

private lemma analyticAt_auxK {n : ℕ} {c w : ℂ} (hw : (1 : ℂ) - w ∈ Complex.slitPlane) :
    AnalyticAt ℂ (auxK n c) w := by
  have hlog : AnalyticAt ℂ (fun z : ℂ => Complex.log (1 - z)) w :=
    AnalyticAt.clog (by fun_prop) hw
  exact hlog.add (analyticAt_auxQ n c w)

private lemma auxK_zero (n : ℕ) (c : ℂ) : auxK n c 0 = 0 := by
  unfold auxK auxQ
  have hsum : ∑ k ∈ Finset.Icc 1 n, (0 : ℂ) ^ k / k = 0 := by
    refine Finset.sum_eq_zero (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    simp [zero_pow (Nat.one_le_iff_ne_zero.mp hk.1)]
  simp [hsum]

private lemma iteratedDeriv_auxQ {n : ℕ} (c : ℂ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    iteratedDeriv k (auxQ n c) 0 = (Nat.factorial (k - 1) : ℂ) := by
  have h1 : iteratedDeriv k (fun w : ℂ => ∑ j ∈ Finset.Icc 1 n, w ^ j / j) 0
      = ∑ j ∈ Finset.Icc 1 n, iteratedDeriv k (fun w : ℂ => w ^ j / j) 0 :=
    iteratedDeriv_fun_sum (fun j _ => by fun_prop)
  have h2 : ∀ j : ℕ, iteratedDeriv k (fun w : ℂ => w ^ j / j) 0
      = if k = j then (Nat.factorial (k - 1) : ℂ) else 0 := by
    intro j
    rw [iteratedDeriv_div_const, iteratedDeriv_fun_pow_zero]
    split_ifs with h
    · subst h
      have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      rw [eq_comm, eq_div_iff hk0, ← Nat.cast_mul,
        mul_comm (Nat.factorial (k - 1)) k, Nat.mul_factorial_pred (by omega : k ≠ 0)]
    · simp
  have h3 : iteratedDeriv k (fun w : ℂ => c * w ^ (n + 1) / (n + 1)) 0 = 0 := by
    rw [iteratedDeriv_div_const, iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero,
      if_neg (by omega)]
    simp
  have h4 : iteratedDeriv k (auxQ n c) 0
      = iteratedDeriv k (fun w : ℂ => ∑ j ∈ Finset.Icc 1 n, w ^ j / j) 0
        + iteratedDeriv k (fun w : ℂ => c * w ^ (n + 1) / (n + 1)) 0 := by
    unfold auxQ
    exact iteratedDeriv_fun_add (by fun_prop) (by fun_prop)
  rw [h4, h3, add_zero, h1]
  rw [Finset.sum_eq_single k]
  · rw [h2]; simp
  · intro j _ hjk
    rw [h2]; simp [Ne.symm hjk]
  · intro hk_notmem
    exact absurd (Finset.mem_Icc.mpr ⟨hk1, hkn⟩) hk_notmem

private lemma iteratedDeriv_auxQ_succ (n : ℕ) (c : ℂ) :
    iteratedDeriv (n + 1) (auxQ n c) 0 = c * (Nat.factorial n : ℂ) := by
  have h1 : iteratedDeriv (n + 1) (fun w : ℂ => ∑ j ∈ Finset.Icc 1 n, w ^ j / j) 0
      = ∑ j ∈ Finset.Icc 1 n, iteratedDeriv (n + 1) (fun w : ℂ => w ^ j / j) 0 :=
    iteratedDeriv_fun_sum (fun j _ => by fun_prop)
  have h1' : iteratedDeriv (n + 1) (fun w : ℂ => ∑ j ∈ Finset.Icc 1 n, w ^ j / j) 0 = 0 := by
    rw [h1]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    rw [iteratedDeriv_div_const, iteratedDeriv_fun_pow_zero, if_neg (by omega)]
    simp
  have h3 : iteratedDeriv (n + 1) (fun w : ℂ => c * w ^ (n + 1) / (n + 1)) 0
      = c * (Nat.factorial n : ℂ) := by
    rw [iteratedDeriv_div_const, iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero,
      if_pos rfl, Nat.factorial_succ]
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    push_cast
    field_simp
  have h4 : iteratedDeriv (n + 1) (auxQ n c) 0
      = iteratedDeriv (n + 1) (fun w : ℂ => ∑ j ∈ Finset.Icc 1 n, w ^ j / j) 0
        + iteratedDeriv (n + 1) (fun w : ℂ => c * w ^ (n + 1) / (n + 1)) 0 := by
    unfold auxQ
    exact iteratedDeriv_fun_add (by fun_prop) (by fun_prop)
  rw [h4, h1', zero_add, h3]

private lemma iteratedDeriv_log_one_sub {k : ℕ} (hk1 : 1 ≤ k) :
    iteratedDeriv k (fun w : ℂ => Complex.log (1 - w)) 0 = -(Nat.factorial (k - 1) : ℂ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h1 := congrFun (iteratedDeriv_comp_const_sub (𝕜 := ℂ) (F := ℂ) (j + 1) Complex.log (1 : ℂ)) 0
  simp only [sub_zero] at h1
  have h2 : iteratedDeriv (j + 1) Complex.log (1 : ℂ) = (-1 : ℂ) ^ j * (Nat.factorial j : ℂ) := by
    rw [iteratedDeriv_succ_log Complex.one_mem_slitPlane]
    simp
  rw [h1, h2, smul_eq_mul]
  simp only [Nat.succ_sub_one]
  have hpow : (-1 : ℂ) ^ (j + 1) * (-1 : ℂ) ^ j = -1 := by
    rw [← pow_add, show j + 1 + j = 2 * j + 1 by ring, pow_succ, pow_mul]
    norm_num
  calc (-1 : ℂ) ^ (j + 1) * ((-1 : ℂ) ^ j * (Nat.factorial j : ℂ))
      = ((-1 : ℂ) ^ (j + 1) * (-1 : ℂ) ^ j) * (Nat.factorial j : ℂ) := by ring
    _ = -(Nat.factorial j : ℂ) := by rw [hpow]; ring

private lemma iteratedDeriv_auxK {n : ℕ} (c : ℂ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    iteratedDeriv k (auxK n c) 0 = 0 := by
  have hlogAnalytic : AnalyticAt ℂ (fun z : ℂ => Complex.log (1 - z)) 0 :=
    AnalyticAt.clog (by fun_prop) (by simp)
  have hadd : iteratedDeriv k (auxK n c) 0
      = iteratedDeriv k (fun w : ℂ => Complex.log (1 - w)) 0 + iteratedDeriv k (auxQ n c) 0 := by
    unfold auxK
    exact iteratedDeriv_fun_add hlogAnalytic.contDiffAt (analyticAt_auxQ n c 0).contDiffAt
  rw [hadd, iteratedDeriv_log_one_sub hk1, iteratedDeriv_auxQ c hk1 hkn]
  ring

private lemma iteratedDeriv_auxK_succ (n : ℕ) (c : ℂ) :
    iteratedDeriv (n + 1) (auxK n c) 0 = (c - 1) * (Nat.factorial n : ℂ) := by
  have hlogAnalytic : AnalyticAt ℂ (fun z : ℂ => Complex.log (1 - z)) 0 :=
    AnalyticAt.clog (by fun_prop) (by simp)
  have hadd : iteratedDeriv (n + 1) (auxK n c) 0
      = iteratedDeriv (n + 1) (fun w : ℂ => Complex.log (1 - w)) 0
        + iteratedDeriv (n + 1) (auxQ n c) 0 := by
    unfold auxK
    exact iteratedDeriv_fun_add hlogAnalytic.contDiffAt (analyticAt_auxQ n c 0).contDiffAt
  rw [hadd, iteratedDeriv_log_one_sub (Nat.succ_le_succ (Nat.zero_le n)), Nat.succ_sub_one,
    iteratedDeriv_auxQ_succ]
  ring

/-- **Lemma `lem:structure` (ii).** The Taylor coefficients of degree
`1, …, n` of `E_n(·;c)` vanish, independently of `c`. -/
theorem taylorCoeff_E_eq_zero {n : ℕ} {c : ℂ} {m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    taylorCoeff (E n c) m = 0 := by
  -- `E n c` agrees with `exp ∘ auxK n c` near `0` (away from the pole at `w = 1`).
  have hnbhd : {w : ℂ | w ≠ 1} ∈ 𝓝 (0 : ℂ) :=
    isOpen_compl_singleton.mem_nhds (by norm_num)
  have hEK : (E n c) =ᶠ[𝓝 (0 : ℂ)] (fun w => Complex.exp (auxK n c w)) := by
    filter_upwards [hnbhd] with w hw
    exact E_eq_exp_auxK hw
  have hKanalytic : AnalyticAt ℂ (auxK n c) 0 := analyticAt_auxK (by simp)
  -- All Taylor coefficients of `auxK n c` of degree `< n + 1` vanish.
  have hKiter : ∀ i < n + 1, iteratedDeriv i (auxK n c) 0 = 0 := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · simp [hi0, iteratedDeriv_zero, auxK_zero]
    · exact iteratedDeriv_auxK c hi0 (by omega)
  have hKorder : (↑(n + 1) : ℕ∞) ≤ analyticOrderAt (auxK n c) 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hKanalytic).mpr hKiter
  -- `exp z - 1` has a simple zero at `0`.
  set f : ℂ → ℂ := fun z => Complex.exp z - 1 with hf_def
  have hK0 : auxK n c 0 = 0 := auxK_zero n c
  have hfAnalytic0 : AnalyticAt ℂ f 0 := by rw [hf_def]; fun_prop
  have hfAnalytic : AnalyticAt ℂ f (auxK n c 0) := by rw [hK0]; exact hfAnalytic0
  have hf0 : f 0 = 0 := by simp [hf_def]
  have hf' : deriv f 0 ≠ 0 := by
    have : deriv f = fun z => Complex.exp z := by
      rw [hf_def]
      funext z
      simp [(Complex.hasDerivAt_exp z).sub_const 1 |>.deriv]
    simp [this]
  have hforder : analyticOrderAt f 0 = 1 :=
    hfAnalytic0.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hf0 hf'
  -- Composing, `exp (auxK n c ·) - 1` inherits the high order of vanishing.
  have hcomp_order : analyticOrderAt (f ∘ auxK n c) 0 = analyticOrderAt (auxK n c) 0 := by
    have hraw := hfAnalytic.analyticOrderAt_comp hKanalytic
    rw [hK0] at hraw
    simp only [sub_zero] at hraw
    rwa [hforder, one_mul] at hraw
  have hcompAnalytic : AnalyticAt ℂ (f ∘ auxK n c) 0 := hfAnalytic.comp hKanalytic
  have hcomp_iter : ∀ i < n + 1, iteratedDeriv i (f ∘ auxK n c) 0 = 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hcompAnalytic).mp
      (hcomp_order ▸ hKorder)
  have hm_lt : m < n + 1 := by omega
  have hzero1 : iteratedDeriv m (fun w => Complex.exp (auxK n c w) - 1) 0 = 0 :=
    hcomp_iter m hm_lt
  have hexpAnalytic : AnalyticAt ℂ (fun w => Complex.exp (auxK n c w)) 0 := hKanalytic.cexp'
  have hzero2 : iteratedDeriv m (fun w => Complex.exp (auxK n c w)) 0 = 0 := by
    have hsplit := iteratedDeriv_sub (n := m) (x := (0 : ℂ))
      hexpAnalytic.contDiffAt (contDiffAt_const (c := (1 : ℂ)))
    simp only [iteratedDeriv_const, if_neg (by omega : ¬ m = 0)] at hsplit
    rw [sub_zero] at hsplit
    rwa [← hsplit]
  rw [taylorCoeff, hEK.iteratedDeriv_eq m, hzero2]
  simp

/-- **Lemma `lem:structure` (iii).** The Taylor coefficient of degree `n+1`
of `E_n(·;c)` is `(c-1)/(n+1)`, affine in `c` with slope `1/(n+1)`. -/
theorem taylorCoeff_E_succ (n : ℕ) (c : ℂ) :
    taylorCoeff (E n c) (n + 1) = (c - 1) / (n + 1) := by
  have hnbhd : {w : ℂ | w ≠ 1} ∈ 𝓝 (0 : ℂ) :=
    isOpen_compl_singleton.mem_nhds (by norm_num)
  have hEK : (E n c) =ᶠ[𝓝 (0 : ℂ)] (fun w => Complex.exp (auxK n c w)) := by
    filter_upwards [hnbhd] with w hw
    exact E_eq_exp_auxK hw
  have hKanalytic : AnalyticAt ℂ (auxK n c) 0 := analyticAt_auxK (by simp)
  have hK0 : auxK n c 0 = 0 := auxK_zero n c
  have hKiter : ∀ i < n + 1, iteratedDeriv i (auxK n c) 0 = 0 := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · simp [hi0, iteratedDeriv_zero, auxK_zero]
    · exact iteratedDeriv_auxK c hi0 (by omega)
  have hKorder : (↑(n + 1) : ℕ∞) ≤ analyticOrderAt (auxK n c) 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hKanalytic).mpr hKiter
  have hKsucc : iteratedDeriv (n + 1) (auxK n c) 0 = (c - 1) * (Nat.factorial n : ℂ) :=
    iteratedDeriv_auxK_succ n c
  -- `g z = exp z - 1 - z` vanishes to order `≥ 2` at `0`.
  set g : ℂ → ℂ := fun z => Complex.exp z - 1 - z with hg_def
  have hgAnalytic0 : AnalyticAt ℂ g 0 := by rw [hg_def]; fun_prop
  have hgiter : ∀ i < 2, iteratedDeriv i g 0 = 0 := by
    intro i hi
    interval_cases i
    · simp [iteratedDeriv_zero, hg_def]
    · have hderiv : deriv g = fun z => Complex.exp z - 1 := by
        rw [hg_def]
        funext z
        have he : HasDerivAt Complex.exp (Complex.exp z) z := Complex.hasDerivAt_exp z
        have hc : HasDerivAt (fun _ : ℂ => (1 : ℂ)) (0 : ℂ) z := hasDerivAt_const z 1
        have hid : HasDerivAt (fun w : ℂ => w) (1 : ℂ) z := hasDerivAt_id z
        have h1 : HasDerivAt (fun w : ℂ => Complex.exp w - 1 - w) (Complex.exp z - 0 - 1) z :=
          (he.sub hc).sub hid
        simp [h1.deriv]
      rw [show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_zero, hderiv]
      simp
  have hgorder : (2 : ℕ∞) ≤ analyticOrderAt g 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hgAnalytic0).mpr hgiter
  have hgAnalytic : AnalyticAt ℂ g (auxK n c 0) := by rw [hK0]; exact hgAnalytic0
  have hcomp_order : (↑(n + 2) : ℕ∞) ≤ analyticOrderAt (g ∘ auxK n c) 0 := by
    have hraw := hgAnalytic.analyticOrderAt_comp hKanalytic
    rw [hK0] at hraw
    simp only [sub_zero] at hraw
    rw [hraw]
    have hmono : (2 : ℕ∞) * (↑(n + 1) : ℕ∞)
        ≤ analyticOrderAt g 0 * analyticOrderAt (auxK n c) 0 := by
      gcongr
    have hcast : (↑(n + 2) : ℕ∞) ≤ (2 : ℕ∞) * (↑(n + 1) : ℕ∞) := by
      have heq : (2 : ℕ∞) * (↑(n + 1) : ℕ∞) = ↑(2 * (n + 1)) := by norm_cast
      rw [heq]
      exact_mod_cast (by omega : n + 2 ≤ 2 * (n + 1))
    exact hcast.trans hmono
  have hcompAnalytic : AnalyticAt ℂ (g ∘ auxK n c) 0 := hgAnalytic.comp hKanalytic
  have hcomp_iter : ∀ i < n + 2, iteratedDeriv i (g ∘ auxK n c) 0 = 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hcompAnalytic).mp hcomp_order
  have hzero_g : iteratedDeriv (n + 1) (fun w => Complex.exp (auxK n c w) - 1 - auxK n c w) 0 = 0 :=
    hcomp_iter (n + 1) (by omega)
  have hexpAnalytic : AnalyticAt ℂ (fun w => Complex.exp (auxK n c w)) 0 := hKanalytic.cexp'
  have hexpSub1Analytic : AnalyticAt ℂ (fun w => Complex.exp (auxK n c w) - 1) 0 :=
    hexpAnalytic.sub analyticAt_const
  have hstep1 : iteratedDeriv (n + 1) (fun w => Complex.exp (auxK n c w) - 1 - auxK n c w) 0
      = iteratedDeriv (n + 1) (fun w => Complex.exp (auxK n c w) - 1) 0
        - iteratedDeriv (n + 1) (auxK n c) 0 :=
    iteratedDeriv_sub hexpSub1Analytic.contDiffAt hKanalytic.contDiffAt
  have hstep2 : iteratedDeriv (n + 1) (fun w => Complex.exp (auxK n c w) - 1) 0
      = iteratedDeriv (n + 1) (fun w => Complex.exp (auxK n c w)) 0 := by
    have hsplit : iteratedDeriv (n + 1) (fun w => Complex.exp (auxK n c w) - 1) 0
        = iteratedDeriv (n + 1) (fun w => Complex.exp (auxK n c w)) 0
          - iteratedDeriv (n + 1) (fun _ : ℂ => (1 : ℂ)) 0 :=
      iteratedDeriv_sub hexpAnalytic.contDiffAt (contDiffAt_const (c := (1 : ℂ)))
    rw [iteratedDeriv_const, if_neg (Nat.succ_ne_zero n), sub_zero] at hsplit
    exact hsplit
  have heq : iteratedDeriv (n + 1) (fun w => Complex.exp (auxK n c w) - 1) 0
      = iteratedDeriv (n + 1) (auxK n c) 0 := by
    have h := hzero_g
    rw [hstep1] at h
    exact eq_of_sub_eq_zero h
  have hEsucc : iteratedDeriv (n + 1) (fun w => Complex.exp (auxK n c w)) 0
      = (c - 1) * (Nat.factorial n : ℂ) := by
    rw [← hstep2, heq, hKsucc]
  rw [taylorCoeff, hEK.iteratedDeriv_eq (n + 1), hEsucc]
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hnf : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- **Lemma `lem:structure` (iv).** `E_n(·;c)` is nowhere vanishing on `𝔻`. -/
theorem E_ne_zero {n : ℕ} {c w : ℂ} (hw : w ∈ 𝔻) : E n c w ≠ 0 := by
  have hw' : ‖w‖ < 1 := mem_𝔻_iff.mp hw
  have hw1 : w ≠ 1 := by
    intro h; rw [h, norm_one] at hw'; exact lt_irrefl 1 hw'
  unfold E
  exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hw1)) (Complex.exp_ne_zero _)

/-- **Lemma `lem:structure` (v).** As an entire function, `E_n(·;c)` has a
simple zero at `w = 1` and no other zeros. -/
theorem E_zero_iff {n : ℕ} {c w : ℂ} : E n c w = 0 ↔ w = 1 := by
  unfold E
  rw [mul_eq_zero, sub_eq_zero, eq_comm]
  simp [Complex.exp_ne_zero]

end Weierstrass
