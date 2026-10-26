import Mathlib



namespace OAI

/-! Contour moments, Newton coefficients and monic root polynomials. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Metric Complex Topology
open scoped Polynomial BigOperators

namespace DegeneratingTrees

 
def contourNewtonCoeff (s : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => -(∑ j : Fin (k + 1), contourNewtonCoeff s j * s (k + 1 - j)) / (k + 1)
termination_by k => k

 
def contourMoment (f : ℂ → ℂ) (r : ℝ) (k : ℕ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * ∮ z in C(0, r), z ^ k * deriv f z / f z

 
def contourPolynomial (f : ℂ → ℂ) (r : ℝ) (d : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    Polynomial.C (contourNewtonCoeff (contourMoment f r) k) * Polynomial.X ^ (d - k)

 

def FixedContourPreparationStatement : Prop :=
  ∀ (n d : ℕ) (F : (Fin n → ℂ) × ℂ → ℂ), AnalyticAt ℂ F (0, 0) →
    analyticOrderAt (fun y => F (0, y)) 0 = (d : ℕ∞) →
    ∃ (r : ℝ) (U : Set (Fin n → ℂ)) (g : (Fin n → ℂ) × ℂ → ℂ),
      0 < r ∧ IsOpen U ∧ (0 : Fin n → ℂ) ∈ U ∧
      AnalyticOnNhd ℂ F (U ×ˢ closedBall 0 r) ∧
      AnalyticOnNhd ℂ g (U ×ˢ closedBall 0 (r / 2)) ∧
      (∀ q ∈ U, ∀ y ∈ closedBall (0 : ℂ) (r / 2), g (q, y) ≠ 0) ∧
      (∀ q ∈ U, ∀ y ∈ sphere (0 : ℂ) r, F (q, y) ≠ 0) ∧
      (∀ q ∈ U, (contourPolynomial (fun y => F (q, y)) r d).Monic ∧
        (contourPolynomial (fun y => F (q, y)) r d).natDegree = d) ∧
      (∀ k, AnalyticOnNhd ℂ
        (fun q => (contourPolynomial (fun y => F (q, y)) r d).coeff k) U) ∧
      (∀ q ∈ U, ∀ y ∈ closedBall (0 : ℂ) (r / 2),
        F (q, y) = (contourPolynomial (fun y => F (q, y)) r d).eval y * g (q, y))

 

theorem factor_closedDisc {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hne : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0) :
    ∃ (s : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ a ∈ s, a ∈ ball (0 : ℂ) r ∧ 0 < m a) ∧
      AnalyticOnNhd ℂ g (closedBall 0 r) ∧
      (∀ z ∈ closedBall (0 : ℂ) r, g z ≠ 0) ∧
      EqOn f (fun z => (∏ a ∈ s, (z - a) ^ m a) * g z) (closedBall 0 r) := by
  classical
  let D := MeromorphicOn.divisor f (closedBall (0 : ℂ) r)
  have hD : 0 ≤ D :=
    (hf.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd).2 hf
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  have hb : (r : ℂ) ∈ sphere (0 : ℂ) r := by
    simp [abs_of_pos hr]
  have hb' : (r : ℂ) ∈ closedBall (0 : ℂ) r := sphere_subset_closedBall hb
  have hb0 : meromorphicOrderAt f (r : ℂ) = 0 :=
    ((hf _ hb').meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).2 (hne _ hb)
  have hfinite : ∀ z : closedBall (0 : ℂ) r, meromorphicOrderAt f z ≠ ⊤ :=
    (hf.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
      (isConnected_closedBall hr.le)).1 ⟨⟨r, hb'⟩, by simp [hb0]⟩
  obtain ⟨g, hg, hgn, hfg⟩ := hf.meromorphicOn.extract_zeros_poles hfinite hfin
  let φ : ℂ → ℂ := ∏ᶠ a, (· - a) ^ D a
  have hφ : AnalyticOnNhd ℂ φ (closedBall 0 r) := by
    intro z hz
    apply Function.FactorizedRational.analyticAt
    exact hD z
  have heq : EqOn f (fun z => φ z * g z) (closedBall 0 r) := by
    apply hf.eqOn_of_preconnected_of_frequently_eq (hφ.mul hg)
      isPreconnected_closedBall (mem_closedBall_self hr.le) (z₀ := 0)
    have hloc : f =ᶠ[𝓝[≠] 0] fun z => φ z * g z := by
      have hc := (mem_codiscreteWithin.mp hfg) 0 (mem_closedBall_self hr.le)
      rw [disjoint_principal_right] at hc
      have hnb : ∀ᶠ z : ℂ in 𝓝[≠] 0, z ∈ closedBall (0 : ℂ) r :=
        mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds (0 : ℂ) hr)
      filter_upwards [hc, hnb] with z hz hz'
      by_contra hn
      exact hz ⟨hz', hn⟩
    exact hloc.frequently
  refine ⟨hfin.toFinset, fun a => (D a).toNat, g, ?_, hg,
    fun z hz => hgn ⟨z, hz⟩, ?_⟩
  · intro a ha
    have haD : D a ≠ 0 := by simpa using ha
    have haB := D.supportWithinDomain (by exact haD)
    have ham : 0 < (D a).toNat := by
      have ha0 : (0 : ℤ) ≤ D a := hD a
      omega
    refine ⟨?_, ham⟩
    rw [mem_ball_zero_iff]
    have hle : ‖a‖ ≤ r := by simpa [mem_closedBall_zero_iff] using haB
    apply lt_of_le_of_ne hle
    intro he
    have hs : a ∈ sphere (0 : ℂ) r := by simpa [mem_sphere_zero_iff_norm] using he
    apply haD
    dsimp [D]
    rw [hf.meromorphicOn.divisor_apply haB]
    rw [((hf _ haB).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).2 (hne a hs)]
    simp
  · intro z hz
    calc
      f z = φ z * g z := heq hz
      _ = _ := ?_
    apply congrArg (fun w => w * g z)
    dsimp [φ]
    rw [finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset)]
    · simp only [Finset.prod_apply, Pi.pow_apply]
      apply Finset.prod_congr rfl
      intro a ha
      have hc : ((D a).toNat : ℤ) = D a := Int.toNat_of_nonneg (hD a)
      simpa only [hc] using (zpow_natCast (z - a) (D a).toNat)
    · intro a ha
      apply hfin.mem_toFinset.mpr
      simpa only [Function.FactorizedRational.mulSupport] using ha

private theorem deriv_eqOn_closedDisc {f h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hh : AnalyticOnNhd ℂ h (closedBall 0 r))
    (heq : EqOn f h (closedBall 0 r)) :
    EqOn (deriv f) (deriv h) (closedBall 0 r) := by
  have heq' := (heq.mono ball_subset_closedBall).deriv isOpen_ball
  exact heq'.of_subset_closure hf.deriv.continuousOn hh.deriv.continuousOn
    ball_subset_closedBall (by rw [closure_ball _ hr.ne'])

 

theorem contourMoment_eq_sum {f g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (s : Finset ℂ) (m : ℂ → ℕ)
    (hs : ∀ a ∈ s, a ∈ ball (0 : ℂ) r)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r))
    (hgn : ∀ z ∈ closedBall (0 : ℂ) r, g z ≠ 0)
    (heq : EqOn f (fun z => (∏ a ∈ s, (z - a) ^ m a) * g z)
      (closedBall 0 r)) (k : ℕ) :
    contourMoment f r k = ∑ a ∈ s, (m a : ℂ) * a ^ k := by
  classical
  let P : ℂ → ℂ := fun z => ∏ a ∈ s, (z - a) ^ m a
  have hp : AnalyticOnNhd ℂ P (closedBall 0 r) := by
    intro z hz
    exact s.analyticAt_fun_prod fun a ha => (analyticAt_id.sub analyticAt_const).pow _
  have hder := deriv_eqOn_closedDisc hr hf (hp.mul hg) heq
  have hza : ∀ z ∈ sphere (0 : ℂ) r, ∀ a ∈ s, z - a ≠ 0 := by
    intro z hz a ha he
    have hza := sub_eq_zero.mp he
    have hz' : ‖z‖ = r := by simpa using hz
    have ha' : ‖a‖ < r := by simpa using hs a ha
    rw [hza] at hz'
    exact (ne_of_lt ha') hz'
  have hld (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) :
      logDeriv f z = (∑ a ∈ s, (m a : ℂ) / (z - a)) + logDeriv g z := by
    have hzc := sphere_subset_closedBall hz
    calc
      logDeriv f z = logDeriv (fun z => P z * g z) z := by
        simp only [logDeriv_apply, hder hzc, heq hzc, P]
      _ = logDeriv P z + logDeriv g z :=
        logDeriv_mul z (Finset.prod_ne_zero_iff.mpr
          fun a ha => pow_ne_zero _ (hza z hz a ha))
          (hgn z hzc) (hp z hzc).differentiableAt (hg z hzc).differentiableAt
      _ = _ := by
        congr 1
        have hPfun : (∏ a ∈ s, fun z => (z - a) ^ m a) =
            fun x => ∏ a ∈ s, (x - a) ^ m a := by
          ext x
          simp only [Finset.prod_apply]
        rw [show P = ∏ a ∈ s, fun z => (z - a) ^ m a from by
              ext point
              simp only [P, Finset.prod_apply],
          hPfun,
          logDeriv_prod (f := fun (a z : ℂ) => (z - a) ^ m a)
            (fun a ha => pow_ne_zero _ (hza z hz a ha))
            (fun a ha => by fun_prop)]
        apply Finset.sum_congr rfl
        intro a ha
        rw [logDeriv_fun_pow (by fun_prop)]
        simp [logDeriv_apply, div_eq_mul_inv]
  let T : ℂ → ℂ → ℂ := fun a z => (m a : ℂ) * ((z - a)⁻¹ * z ^ k)
  have hTc : ∀ a ∈ s, ContinuousOn (T a) (sphere (0 : ℂ) r) := by
    intro a ha
    exact continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).inv₀ (fun z hz => hza z hz a ha)
        |>.mul (continuousOn_id.pow k))
  have hT : ∀ a ∈ s, CircleIntegrable (T a) 0 r :=
    fun a ha => (hTc a ha).circleIntegrable hr.le
  have hunit : AnalyticOnNhd ℂ (fun z => z ^ k * logDeriv g z) (closedBall 0 r) := by
    exact (analyticOnNhd_id.pow k).mul (hg.deriv.div hg hgn)
  have hUi : CircleIntegrable (fun z => z ^ k * logDeriv g z) 0 r :=
    (hunit.continuousOn.mono sphere_subset_closedBall).circleIntegrable hr.le
  have hSi : CircleIntegrable (fun z => ∑ a ∈ s, T a z) 0 r := by
    exact (continuousOn_finsetSum s hTc).circleIntegrable hr.le
  have hformula : (∮ z in C(0, r), z ^ k * deriv f z / f z) =
      ∑ a ∈ s, (m a : ℂ) * ((2 * Real.pi * I) * a ^ k) := by
    calc
      (∮ z in C(0, r), z ^ k * deriv f z / f z) =
          ∮ z in C(0, r), (∑ a ∈ s, T a z) + z ^ k * logDeriv g z := by
        apply circleIntegral.integral_congr hr.le
        intro z hz
        dsimp only
        rw [mul_div_assoc, ← logDeriv_apply, hld z hz, mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        dsimp [T]
        ring
      _ = (∑ a ∈ s, ∮ z in C(0, r), T a z) + 0 := by
        rw [circleIntegral.integral_add hSi hUi, circleIntegral.integral_fun_sum hT]
        rw [DiffContOnCl.circleIntegral_eq_zero hr.le
          (hunit.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl]
      _ = _ := by
        rw [add_zero]
        apply Finset.sum_congr rfl
        intro a ha
        dsimp [T]
        rw [circleIntegral.integral_const_mul]
        congr 1
        exact (by simpa only [smul_eq_mul] using
          (show DifferentiableOn ℂ (fun z : ℂ => z ^ k) (closedBall 0 r) from
            by fun_prop).circleIntegral_sub_inv_smul (hs a ha))
  rw [contourMoment, hformula]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hn : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  field_simp

 
theorem contourNewtonCoeff_powerSum {ι : Type*} [Fintype ι] (x : ι → ℂ) (k : ℕ) :
    contourNewtonCoeff (fun j => ∑ i, x i ^ j) k =
      (-1) ^ k * (Finset.univ.val.map x).esymm k := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [contourNewtonCoeff, Multiset.esymm]
    | succ k =>
      rw [contourNewtonCoeff]
      have hn := congrArg (MvPolynomial.aeval x)
        (MvPolynomial.mul_esymm_eq_sum ι ℂ (k + 1))
      simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
        MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum,
        MvPolynomial.aeval_X] at hn
      rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ] at hn
      simp only [lt_self_iff_false, ↓reduceIte, add_zero] at hn
      have hs : (∑ j : Fin (k + 1),
          contourNewtonCoeff (fun j => ∑ i, x i ^ j) j * ∑ i, x i ^ (k + 1 - j)) =
          ∑ j ∈ Finset.range (k + 1),
            (-1 : ℂ) ^ j * (Finset.univ.val.map x).esymm j *
              ∑ i, x i ^ (k + 1 - j) := by
        rw [Fin.sum_univ_eq_sum_range (fun j =>
          contourNewtonCoeff (fun j => ∑ i, x i ^ j) j * ∑ i, x i ^ (k + 1 - j))]
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih j (Finset.mem_range.mp hj)]
      rw [hs]
      have hn' : ((k + 1 : ℕ) : ℂ) * (Finset.univ.val.map x).esymm (k + 1) =
          (-1 : ℂ) ^ (k + 1 + 1) *
            ∑ j ∈ Finset.range (k + 1),
              (-1 : ℂ) ^ j * (Finset.univ.val.map x).esymm j *
                ∑ i, x i ^ (k + 1 - j) := by
        convert hn using 2
        apply Finset.sum_congr rfl
        intro j hj
        simp [Finset.mem_range.mp hj]
      have hz : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      apply (div_eq_iff hz).2
      have hsign : (-1 : ℂ) ^ (k + 1) * (-1) ^ (k + 1 + 1) = -1 := by
        rw [← pow_add]
        convert (Odd.neg_one_pow (show Odd (k + 1 + (k + 1 + 1)) by exact ⟨k + 1, by omega⟩) : _)
      have hmul := congrArg (fun z : ℂ => (-1) ^ (k + 1) * z) hn'
      simp only [← mul_assoc, hsign, neg_one_mul, Nat.cast_add, Nat.cast_one] at hmul
      linear_combination -hmul

 
theorem contourPolynomial_eq_prod {ι : Type*} [Fintype ι] (x : ι → ℂ)
    {f : ℂ → ℂ} {r : ℝ}
    (hs : ∀ k, contourMoment f r k = ∑ i, x i ^ k) :
    contourPolynomial f r (Fintype.card ι) = ∏ i, (Polynomial.X - Polynomial.C (x i)) := by
  classical
  have hf : contourMoment f r = fun k => ∑ i, x i ^ k := funext hs
  rw [contourPolynomial, hf]
  simp_rw [contourNewtonCoeff_powerSum]
  have hv := (Finset.univ.val.map x).prod_X_sub_X_eq_sum_esymm
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ,
    Multiset.map_map, Function.comp_def] at hv
  change (∏ i, (Polynomial.X - Polynomial.C (x i))) = _ at hv
  rw [hv]
  apply Finset.sum_congr rfl
  intro k hk
  simp [map_mul, map_pow, mul_assoc]

end DegeneratingTrees
end

end OAI


namespace OAI

/-! Analytic functions with values in continuous-function Banach spaces. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Metric Filter Topology
open scoped BigOperators NNReal ENNReal
namespace DegeneratingTrees

variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

 
def liftCML {n : ℕ} (p : E [×n]→L[ℂ] F) : C(K, E) [×n]→L[ℂ] C(K, F) :=
  let P : MultilinearMap ℂ (fun _ : Fin n => C(K, E)) C(K, F) :=
    { toFun := fun v => ⟨fun t => p (fun i => v i t),
        p.cont.comp (continuous_pi fun i => (v i).continuous)⟩
      map_update_add' := by
        intro _ v i a b
        ext t
        change p (fun j => Function.update v i (a + b) j t) =
          p (fun j => Function.update v i a j t) + p (fun j => Function.update v i b j t)
        have he (u : C(K, E)) : (fun j => Function.update v i u j t) =
            Function.update (fun j => v j t) i (u t) := by
          ext j
          by_cases hj : j = i <;> simp [hj]
        simp_rw [he]
        exact p.map_update_add (fun j => v j t) i (a t) (b t)
      map_update_smul' := by
        intro _ v i c a
        ext t
        change p (fun j => Function.update v i (c • a) j t) =
          c • p (fun j => Function.update v i a j t)
        have he (u : C(K, E)) : (fun j => Function.update v i u j t) =
            Function.update (fun j => v j t) i (u t) := by
          ext j
          by_cases hj : j = i <;> simp [hj]
        simp_rw [he]
        exact p.map_update_smul (fun j => v j t) i c (a t) }
  P.mkContinuous ‖p‖ (by
    intro v
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro t
    exact (p.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun i _ => (v i).norm_coe_le_norm t)) (norm_nonneg p)))

@[simp] theorem liftCML_apply {n : ℕ} (p : E [×n]→L[ℂ] F)
    (v : Fin n → C(K, E)) (t : K) : liftCML p v t = p (fun i => v i t) := rfl

theorem liftCML_norm_le {n : ℕ} (p : E [×n]→L[ℂ] F) :
    ‖liftCML (K := K) p‖ ≤ ‖p‖ :=
  by
    unfold liftCML
    apply MultilinearMap.mkContinuous_norm_le
    exact norm_nonneg _

 

theorem liftSeries_radius {p : FormalMultilinearSeries ℂ E F} {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < p.radius) :
    (r : ℝ≥0∞) ≤ (show FormalMultilinearSeries ℂ C(K, E) C(K, F) from
      fun n => liftCML (K := K) (p n)).radius := by
  apply FormalMultilinearSeries.le_radius_of_summable
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun n => mul_le_mul_of_nonneg_right (liftCML_norm_le (p n)) (by positivity))
    (p.summable_norm_mul_pow hr)

 

theorem analytic_continuousMap_of_series [CompleteSpace F] {f : E → F}
    {p : FormalMultilinearSeries ℂ E F} {R : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p 0 R) {r : ℝ≥0} (hrR : (r : ℝ≥0∞) < R) :
    ∃ Φ : C(K, E) → C(K, F), AnalyticOnNhd ℂ Φ (ball 0 (r : ℝ)) ∧
      ∀ v ∈ ball (0 : C(K, E)) (r : ℝ), ∀ t, Φ v t = f (v t) := by
  let P : FormalMultilinearSeries ℂ C(K, E) C(K, F) := fun n => liftCML (p n)
  have hrP : (r : ℝ≥0∞) ≤ P.radius := liftSeries_radius (hrR.trans_le hp.r_le)
  refine ⟨P.sum, ?_, ?_⟩
  · apply P.analyticOnNhd.mono
    intro v hv
    rw [mem_eball_zero_iff]
    apply lt_of_lt_of_le _ hrP
    have hn : ‖v‖ < (r : ℝ) := by simpa using hv
    exact_mod_cast hn
  · intro v hv t
    have hv' : (‖v‖₊ : ℝ≥0∞) < r := by
      have hn : ‖v‖ < (r : ℝ) := by simpa using hv
      exact_mod_cast hn
    have hvP : v ∈ eball (0 : C(K, E)) P.radius := by
      exact (mem_eball_zero_iff).2 (hv'.trans_le hrP)
    have hvR : v t ∈ eball (0 : E) R := by
      rw [mem_eball_zero_iff]
      exact (show (‖v t‖₊ : ℝ≥0∞) ≤ ‖v‖₊ from by
        exact_mod_cast v.norm_coe_le_norm t).trans_lt (hv'.trans hrR)
    have h₁ := (ContinuousMap.evalCLM (R := ℂ) (M := F) t).hasSum (P.hasSum hvP)
    have h₂ := hp.hasSum hvR
    simp only [zero_add] at h₂
    exact h₁.unique h₂

 

theorem analytic_continuousMap_realization [CompleteSpace F] {f : E → F}
    (hf : AnalyticAt ℂ f 0) :
    ∃ (r : ℝ), 0 < r ∧ ∃ Φ : C(K, E) → C(K, F),
      AnalyticOnNhd ℂ Φ (ball 0 r) ∧
      ∀ v ∈ ball (0 : C(K, E)) r, ∀ t, Φ v t = f (v t) := by
  obtain ⟨p, R, hp⟩ := hf
  obtain ⟨r, hr0, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  exact ⟨r, by exact_mod_cast hr0, analytic_continuousMap_of_series hp hrR⟩

 

def circleExtension {r : ℝ} (f : C(sphere (0 : ℂ) r, ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ sphere (0 : ℂ) r then f ⟨z, hz⟩ else 0

@[simp] theorem circleExtension_on {r : ℝ} (f : C(sphere (0 : ℂ) r, ℂ))
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) r) : circleExtension f z = f ⟨z, hz⟩ := by
  simp only [circleExtension, dif_pos hz]

private theorem circleExtension_continuousOn {r : ℝ} (f : C(sphere (0 : ℂ) r, ℂ)) :
    ContinuousOn (circleExtension f) (sphere (0 : ℂ) r) := by
  rw [continuousOn_iff_continuous_restrict]
  convert f.continuous using 1
  ext z
  exact circleExtension_on f z.property

 
def circleFunctional (r : ℝ) (hr : 0 ≤ r) : C(sphere (0 : ℂ) r, ℂ) →L[ℂ] ℂ :=
  let L : C(sphere (0 : ℂ) r, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∮ z in C(0, r), circleExtension f z
      map_add' := by
        intro f g
        have he : circleExtension (f + g) = fun z => circleExtension f z + circleExtension g z := by
          ext z
          by_cases hz : z ∈ sphere (0 : ℂ) r <;> simp only [circleExtension, hz, dite_true, dite_false, ContinuousMap.add_apply, add_zero]
        rw [he]
        exact circleIntegral.integral_add
          ((circleExtension_continuousOn f).circleIntegrable hr)
          ((circleExtension_continuousOn g).circleIntegrable hr)
      map_smul' := by
        intro c f
        have he : circleExtension (c • f) = fun z => c • circleExtension f z := by
          ext z
          by_cases hz : z ∈ sphere (0 : ℂ) r <;> simp only [circleExtension, hz, dite_true, dite_false, ContinuousMap.smul_apply, smul_zero]
        rw [he, circleIntegral.integral_smul]
        rfl }
  L.mkContinuous (2 * Real.pi * r) (by
    intro f
    apply circleIntegral.norm_integral_le_of_norm_le_const hr
    intro z hz
    rw [circleExtension_on f hz]
    exact f.norm_coe_le_norm ⟨z, hz⟩)

theorem circleFunctional_eq {r : ℝ} (hr : 0 ≤ r) (f : C(sphere (0 : ℂ) r, ℂ))
    (h : ℂ → ℂ) (he : ∀ z : sphere (0 : ℂ) r, f z = h z) :
    circleFunctional r hr f = ∮ z in C(0, r), h z := by
  apply circleIntegral.integral_congr hr
  intro z hz
  rw [circleExtension_on f hz]
  exact he ⟨z, hz⟩

 

theorem analytic_circle_profiles {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {F : A × ℂ → ℂ} (hF : AnalyticAt ℂ F 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ r : ℝ, 0 < r → r < a →
      ∃ φ ψ : A → C(sphere (0 : ℂ) r, ℂ),
        AnalyticOnNhd ℂ F (ball 0 a ×ˢ closedBall 0 r) ∧
        AnalyticOnNhd ℂ φ (ball 0 a) ∧ AnalyticOnNhd ℂ ψ (ball 0 a) ∧
        (∀ q ∈ ball (0 : A) a, ∀ z : sphere (0 : ℂ) r, φ q z = F (q, z)) ∧
        (∀ q ∈ ball (0 : A) a, ∀ z : sphere (0 : ℂ) r,
          ψ q z = deriv (fun y => F (q, y)) z) := by
  let H : A × ℂ → ℂ × ℂ := fun x => (F x, fderiv ℂ F x (0, 1))
  have hH : AnalyticAt ℂ H 0 := hF.prod
    (((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : A × ℂ)).analyticAt _).comp hF.fderiv)
  obtain ⟨p, R, hp⟩ := hH
  obtain ⟨b, hb0, hbR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hb : (0 : ℝ) < b := by exact_mod_cast hb0
  refine ⟨b / 2, half_pos hb, ?_⟩
  intro r hr hra
  let K := sphere (0 : ℂ) r
  let w : C(K, A × ℂ) := ⟨fun z => (0, z),
    continuous_const.prodMk continuous_subtype_val⟩
  let L : A →L[ℂ] C(K, A × ℂ) :=
    (ContinuousLinearMap.const ℂ K).comp (ContinuousLinearMap.inl ℂ A ℂ)
  let v : A → C(K, A × ℂ) := fun q => L q + w
  have hve (q : A) (z : K) : v q z = (q, (z : ℂ)) := by simp [v, L, w]
  have hva : AnalyticOnNhd ℂ v (ball 0 ((b : ℝ) / 2)) :=
    fun q _ => (L.analyticAt q).add analyticAt_const
  have hvb (q : A) (hq : q ∈ ball (0 : A) ((b : ℝ) / 2)) :
      v q ∈ ball (0 : C(K, A × ℂ)) (b : ℝ) := by
    have hnq : ‖q‖ < (b : ℝ) / 2 := by simpa using hq
    have hnv : ‖v q‖ ≤ max ‖q‖ r := by
      apply (ContinuousMap.norm_le _ (le_max_of_le_left (norm_nonneg q))).2
      intro z
      rw [hve, Prod.norm_def]
      have hnz : ‖(z : ℂ)‖ = r := by simp
      rw [hnz]
    have : ‖v q‖ < (b : ℝ) := hnv.trans_lt
      ((max_lt hnq hra).trans (half_lt_self hb))
    simpa using this
  obtain ⟨Φ, hΦ, hΦe⟩ := analytic_continuousMap_of_series (K := K) hp hbR
  let π₁ := ContinuousLinearMap.compLeftContinuous ℂ K (ContinuousLinearMap.fst ℂ ℂ ℂ)
  let π₂ := ContinuousLinearMap.compLeftContinuous ℂ K (ContinuousLinearMap.snd ℂ ℂ ℂ)
  let φ : A → C(K, ℂ) := fun q => π₁ (Φ (v q))
  let ψ : A → C(K, ℂ) := fun q => π₂ (Φ (v q))
  have hFball : AnalyticOnNhd ℂ F (ball 0 ((b : ℝ) / 2) ×ˢ closedBall 0 r) := by
    intro x hx
    have hn : ‖x‖ < (b : ℝ) := by
      rw [Prod.norm_def]
      have hx₁ : ‖x.1‖ < (b : ℝ) / 2 := by simpa using hx.1
      have hx₂ : ‖x.2‖ ≤ r := by simpa using hx.2
      exact (max_lt hx₁ (hx₂.trans_lt hra)).trans (half_lt_self hb)
    have hxR : x ∈ eball (0 : A × ℂ) R := by
      rw [mem_eball_zero_iff]
      exact (show (‖x‖₊ : ℝ≥0∞) < b from by exact_mod_cast hn).trans hbR
    exact ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _).comp (hp.analyticOnNhd x hxR)
  refine ⟨φ, ψ, hFball, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact (π₁.analyticAt _).comp ((hΦ _ (hvb q hq)).comp (hva q hq))
  · intro q hq
    exact (π₂.analyticAt _).comp ((hΦ _ (hvb q hq)).comp (hva q hq))
  · intro q hq z
    change (Φ (v q) z).1 = F (q, z)
    rw [hΦe _ (hvb q hq), hve]
  · intro q hq z
    change (Φ (v q) z).2 = deriv (fun y => F (q, y)) z
    rw [hΦe _ (hvb q hq), hve]
    have hFd := (hFball (q, z) ⟨hq, sphere_subset_closedBall z.property⟩).differentiableAt
    exact ((hFd.hasFDerivAt.comp_hasDerivAt (z : ℂ)
      ((hasDerivAt_const (z : ℂ) q).prodMk (hasDerivAt_id (z : ℂ)))).deriv).symm

 

omit [CompactSpace K] in
theorem continuousMap_ringInverse_apply (f : C(K, ℂ)) (hf : IsUnit f) (z : K) :
    Ring.inverse f z = (f z)⁻¹ := by
  have hn : f z ≠ 0 := (f.isUnit_iff_forall_ne_zero).1 hf z
  apply mul_left_cancel₀ hn
  rw [← ContinuousMap.mul_apply, Ring.mul_inverse_cancel f hf]
  simp [hn]

end DegeneratingTrees
end

end OAI


namespace OAI

/-! Analytic contour moments and fixed-contour polynomial division. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

namespace DegeneratingTrees
open Set Metric Filter Topology Complex
open scoped BigOperators NNReal ENNReal

 

theorem analytic_contourMoment {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {F : A × ℂ → ℂ} {r : ℝ} (hr : 0 < r) {U : Set A} (hU : IsOpen U)
    {φ ψ : A → C(sphere (0 : ℂ) r, ℂ)}
    (hφ : AnalyticOnNhd ℂ φ U) (hψ : AnalyticOnNhd ℂ ψ U)
    (hφe : ∀ q ∈ U, ∀ z : sphere (0 : ℂ) r, φ q z = F (q, z))
    (hψe : ∀ q ∈ U, ∀ z : sphere (0 : ℂ) r, ψ q z = deriv (fun y => F (q, y)) z)
    (hφn : ∀ q ∈ U, IsUnit (φ q)) (k : ℕ) :
    AnalyticOnNhd ℂ (fun q => contourMoment (fun y => F (q, y)) r k) U := by
  let w : C(sphere (0 : ℂ) r, ℂ) := ⟨fun z => (z : ℂ) ^ k, continuous_subtype_val.pow k⟩
  let T : A → ℂ := fun q => (2 * Real.pi * I)⁻¹ *
    circleFunctional r hr.le (w * ψ q * Ring.inverse (φ q))
  have hT : AnalyticOnNhd ℂ T U := by
    intro q hq
    apply AnalyticAt.mul analyticAt_const
    apply (circleFunctional r hr.le).analyticAt _ |>.comp
    apply AnalyticAt.mul (analyticAt_const.mul (hψ q hq))
    exact (analyticOnNhd_inverse _ (hφn q hq)).comp (hφ q hq)
  have hTe : EqOn T (fun q => contourMoment (fun y => F (q, y)) r k) U := by
    intro q hq
    dsimp [T, contourMoment]
    congr 1
    apply circleFunctional_eq
    intro z
    simp only [ContinuousMap.mul_apply, continuousMap_ringInverse_apply _ (hφn q hq),
      hφe q hq, hψe q hq, w, ContinuousMap.coe_mk, div_eq_mul_inv]
  intro q hq
  apply (hT q hq).congr
  filter_upwards [hU.mem_nhds hq] with x hx
  exact hTe hx

 

theorem contour_fiber_factorization {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hne : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0) :
    ∃ (d : ℕ) (g : ℂ → ℂ), contourMoment f r 0 = (d : ℂ) ∧
      (contourPolynomial f r d).Monic ∧ (contourPolynomial f r d).natDegree = d ∧
      AnalyticOnNhd ℂ g (closedBall 0 r) ∧
      (∀ z ∈ closedBall (0 : ℂ) r, g z ≠ 0) ∧
      EqOn f (fun z => (contourPolynomial f r d).eval z * g z) (closedBall 0 r) := by
  classical
  obtain ⟨s, m, g, hs, hg, hgn, hfg⟩ := factor_closedDisc hr hf hne
  let ι := Σ a : s, Fin (m a)
  let x : ι → ℂ := fun i => i.1
  have hm (k : ℕ) : contourMoment f r k = ∑ i : ι, x i ^ k := by
    rw [contourMoment_eq_sum hr hf s m (fun a ha => (hs a ha).1) hg hgn hfg k]
    simpa [ι, x, Fintype.sum_sigma] using
      (Finset.sum_attach s (fun a => (m a : ℂ) * a ^ k)).symm
  have hP := contourPolynomial_eq_prod (f := f) (r := r) x hm
  refine ⟨Fintype.card ι, g, ?_, ?_, ?_, hg, hgn, ?_⟩
  · simpa using hm 0
  · rw [hP]
    exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (x i)
  · rw [hP, Polynomial.natDegree_prod_of_monic _ _
      (fun i _ => Polynomial.monic_X_sub_C (x i))]
    simp
  · intro z hz
    rw [hfg hz, hP]
    dsimp only
    rw [Polynomial.eval_prod]
    congr 1
    simpa [ι, x, Fintype.prod_sigma] using
      (Finset.prod_attach s (fun a => (z - a) ^ m a)).symm

private theorem nat_eq_of_complex_dist_lt_one {m n : ℕ}
    (h : dist (m : ℂ) (n : ℂ) < 1) : m = n := by
  have h' : |((m : ℤ) - n : ℤ)| < 1 := by
    have hc : ((m : ℂ) - n) = (((m : ℤ) - n : ℤ) : ℂ) := by push_cast; rfl
    rw [dist_eq_norm, hc, Complex.norm_intCast] at h
    exact_mod_cast h
  have he := Int.abs_lt_one_iff.mp h'
  omega

 

theorem fixed_circle_data {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {F : A × ℂ → ℂ} (hF : AnalyticAt ℂ F 0) {d : ℕ}
    (hd : analyticOrderAt (fun y => F (0, y)) 0 = (d : ℕ∞)) :
    ∃ (r : ℝ) (U : Set A) (φ : A → C(sphere (0 : ℂ) r, ℂ)),
      0 < r ∧ IsOpen U ∧ (0 : A) ∈ U ∧
      AnalyticOnNhd ℂ F (U ×ˢ closedBall 0 r) ∧
      AnalyticOnNhd ℂ φ U ∧
      (∀ q ∈ U, ∀ z : sphere (0 : ℂ) r, φ q z = F (q, z)) ∧
      (∀ q ∈ U, IsUnit (φ q)) ∧
      (∀ k, AnalyticOnNhd ℂ (fun q => contourMoment (fun y => F (q, y)) r k) U) ∧
      (∀ q ∈ U, contourMoment (fun y => F (q, y)) r 0 = (d : ℂ)) := by
  classical
  obtain ⟨a, ha, hprof⟩ := analytic_circle_profiles hF
  have hF₀ : AnalyticAt ℂ (fun y => F (0, y)) 0 :=
    hF.comp (f := fun y : ℂ => ((0 : A), y)) (x := 0)
      (analyticAt_const.prod analyticAt_id)
  obtain ⟨g, hg, hg0, hge⟩ := hF₀.analyticOrderAt_eq_natCast.mp hd
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
      F (0, z) = z ^ d * g z := by
    filter_upwards [hg.eventually_analyticAt, hg.continuousAt.eventually_ne hg0, hge]
      with z hz hn he
    exact ⟨hz, hn, by simpa using he⟩
  obtain ⟨ε, hε, hεe⟩ := Metric.mem_nhds_iff.mp hev
  let r : ℝ := min a ε / 2
  have hr : 0 < r := half_pos (lt_min ha hε)
  have hra : r < a := (half_lt_self (lt_min ha hε)).trans_le (min_le_left _ _)
  have hrε : r < ε := (half_lt_self (lt_min ha hε)).trans_le (min_le_right _ _)
  have hgeB (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r) :
      AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ F (0, z) = z ^ d * g z :=
    hεe (lt_of_le_of_lt (show dist z 0 ≤ r from hz) hrε)
  obtain ⟨φ, ψ, hFA, hφ, hψ, hφe, hψe⟩ := hprof r hr hra
  have h0a : (0 : A) ∈ ball 0 a := mem_ball_self ha
  have hφ0 : IsUnit (φ 0) := by
    rw [ContinuousMap.isUnit_iff_forall_ne_zero]
    intro z
    rw [hφe 0 h0a z, (hgeB z (sphere_subset_closedBall z.property)).2.2]
    apply mul_ne_zero _ (hgeB z (sphere_subset_closedBall z.property)).2.1
    apply pow_ne_zero
    have hnz : ‖(z : ℂ)‖ = r := by simp
    intro he
    exact hr.ne' (by simpa [he] using hnz.symm)
  have hunitN : φ ⁻¹' {v | IsUnit v} ∈ 𝓝 (0 : A) :=
    (hφ 0 h0a).continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hφ0)
  obtain ⟨b, hb, hbU⟩ := Metric.mem_nhds_iff.mp hunitN
  let V : Set A := ball 0 a ∩ ball 0 b
  have hV : IsOpen V := isOpen_ball.inter isOpen_ball
  have h0V : (0 : A) ∈ V := ⟨h0a, mem_ball_self hb⟩
  have hunit (q : A) (hq : q ∈ V) : IsUnit (φ q) := hbU hq.2
  have hm (k : ℕ) : AnalyticOnNhd ℂ
      (fun q => contourMoment (fun y => F (q, y)) r k) V :=
    analytic_contourMoment hr hV (hφ.mono inter_subset_left) (hψ.mono inter_subset_left)
      (fun q hq => hφe q hq.1) (fun q hq => hψe q hq.1) hunit k
  have hm0 : contourMoment (fun y => F (0, y)) r 0 = (d : ℂ) := by
    have heq : EqOn (fun z => F (0, z))
        (fun z => (∏ a ∈ ({0} : Finset ℂ), (z - a) ^ d) * g z) (closedBall 0 r) := by
      intro z hz
      simpa using (hgeB z hz).2.2
    have hfB : AnalyticOnNhd ℂ (fun z => F (0, z)) (closedBall 0 r) := by
      intro z hz
      exact (hFA (0, z) ⟨h0a, hz⟩).comp (analyticAt_const.prod analyticAt_id)
    simpa using contourMoment_eq_sum hr hfB ({0} : Finset ℂ) (fun _ => d)
      (by intro z hz; have he : z = 0 := Finset.mem_singleton.mp hz;
          subst z; exact mem_ball_self hr)
      (fun z hz => (hgeB z hz).1) (fun z hz => (hgeB z hz).2.1) heq 0
  have hcountN : {q : A | dist (contourMoment (fun y => F (q, y)) r 0) (d : ℂ) < 1}
      ∈ 𝓝 (0 : A) := by
    have hn := (hm 0 0 h0V).continuousAt.preimage_mem_nhds (ball_mem_nhds
      (contourMoment (fun y => F (0, y)) r 0) (show (0 : ℝ) < 1 by norm_num))
    change {q : A | dist (contourMoment (fun y => F (q, y)) r 0)
      (contourMoment (fun y => F (0, y)) r 0) < 1} ∈ 𝓝 (0 : A) at hn
    simpa only [hm0] using hn
  obtain ⟨c, hc, hcU⟩ := Metric.mem_nhds_iff.mp hcountN
  let U : Set A := V ∩ ball 0 c
  have hUV : U ⊆ V := inter_subset_left
  refine ⟨r, U, φ, hr, hV.inter isOpen_ball, ⟨h0V, mem_ball_self hc⟩,
    hFA.mono (fun x hx => ⟨hx.1.1.1, hx.2⟩), hφ.mono (fun q hq => hq.1.1),
    (fun q hq => hφe q hq.1.1), (fun q hq => hunit q hq.1),
    (fun k => (hm k).mono hUV), ?_⟩
  intro q hq
  have hfB : AnalyticOnNhd ℂ (fun z => F (q, z)) (closedBall 0 r) := by
    intro z hz
    exact (hFA (q, z) ⟨hq.1.1, hz⟩).comp (analyticAt_const.prod analyticAt_id)
  have hnB : ∀ z ∈ sphere (0 : ℂ) r, F (q, z) ≠ 0 := by
    intro z hz
    rw [← hφe q hq.1.1 ⟨z, hz⟩]
    exact (ContinuousMap.isUnit_iff_forall_ne_zero _).1 (hunit q hq.1) ⟨z, hz⟩
  obtain ⟨N, _, hN, _⟩ := contour_fiber_factorization hr hfB hnB
  have heNd : N = d := nat_eq_of_complex_dist_lt_one (by rw [← hN]; exact hcU hq.2)
  simpa only [heNd] using hN

 
theorem analytic_contourNewtonCoeff {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {s : A → ℕ → ℂ} {U : Set A}
    (hs : ∀ k, AnalyticOnNhd ℂ (fun q => s q k) U) (k : ℕ) :
    AnalyticOnNhd ℂ (fun q => contourNewtonCoeff (s q) k) U := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simpa only [contourNewtonCoeff] using (analyticOnNhd_const :
        AnalyticOnNhd ℂ (fun _ : A => (1 : ℂ)) U)
    | succ k =>
      intro q hq
      simp only [contourNewtonCoeff]
      apply AnalyticAt.div_const
      apply AnalyticAt.neg
      apply Finset.analyticAt_fun_sum
      intro j _
      exact (ih j (Fin.is_lt j) q hq).mul (hs (k + 1 - j) q hq)

 
theorem analytic_contourPolynomial_coeff {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {F : A × ℂ → ℂ} {r : ℝ} {U : Set A}
    (hm : ∀ k, AnalyticOnNhd ℂ (fun q => contourMoment (fun y => F (q, y)) r k) U)
    (d k : ℕ) :
    AnalyticOnNhd ℂ (fun q => (contourPolynomial (fun y => F (q, y)) r d).coeff k) U := by
  intro q hq
  simp only [contourPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (analytic_contourNewtonCoeff hm j q hq).mul analyticAt_const

 
def contourPolynomialProfile {A : Type*} (F : A × ℂ → ℂ) (r : ℝ) (d : ℕ) (q : A) :
    C(sphere (0 : ℂ) r, ℂ) :=
  ∑ k ∈ Finset.range (d + 1),
    ContinuousMap.const _ (contourNewtonCoeff (contourMoment (fun y => F (q, y)) r) k) *
      (⟨fun z => (z : ℂ), continuous_subtype_val⟩ : C(sphere (0 : ℂ) r, ℂ)) ^ (d - k)

theorem contourPolynomialProfile_apply {A : Type*} (F : A × ℂ → ℂ) (r : ℝ) (d : ℕ)
    (q : A) (z : sphere (0 : ℂ) r) :
    contourPolynomialProfile F r d q z = (contourPolynomial (fun y => F (q, y)) r d).eval (z : ℂ) := by
  simp [contourPolynomialProfile, contourPolynomial, Polynomial.eval_finsetSum]

theorem analytic_contourPolynomialProfile {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {F : A × ℂ → ℂ} {r : ℝ} {U : Set A}
    (hm : ∀ k, AnalyticOnNhd ℂ (fun q => contourMoment (fun y => F (q, y)) r k) U) (d : ℕ) :
    AnalyticOnNhd ℂ (contourPolynomialProfile F r d) U := by
  intro q hq
  unfold contourPolynomialProfile
  apply Finset.analyticAt_fun_sum
  intro j _
  apply AnalyticAt.mul _ analyticAt_const
  exact ((ContinuousLinearMap.const ℂ (sphere (0 : ℂ) r)).analyticAt _).comp
    (analytic_contourNewtonCoeff hm j q hq)

 
def cauchyKernelProfile (r : ℝ) (y : ℂ) : C(sphere (0 : ℂ) r, ℂ) :=
  ⟨fun z => (z : ℂ), continuous_subtype_val⟩ - ContinuousMap.const _ y

@[simp] theorem cauchyKernelProfile_apply (r : ℝ) (y : ℂ) (z : sphere (0 : ℂ) r) :
    cauchyKernelProfile r y z = (z : ℂ) - y := rfl

theorem cauchyKernelProfile_isUnit {r : ℝ} {y : ℂ} (hy : y ∈ ball (0 : ℂ) r) :
    IsUnit (cauchyKernelProfile r y) := by
  rw [ContinuousMap.isUnit_iff_forall_ne_zero]
  intro z
  apply sub_ne_zero.mpr
  intro he
  have hz : ‖(z : ℂ)‖ = r := by simp
  have hy' : ‖y‖ < r := by simpa using hy
  change (z : ℂ) = y at he
  exact (not_lt_of_ge (by simpa only [he] using hz.ge)) hy'

theorem analytic_cauchyKernelProfile (r : ℝ) : AnalyticOnNhd ℂ (cauchyKernelProfile r) univ := by
  intro y _
  exact analyticAt_const.sub ((ContinuousLinearMap.const ℂ (sphere (0 : ℂ) r)).analyticAt y)

 

def cauchyTransformProfile {A : Type*} (r : ℝ) (hr : 0 < r)
    (κ : A → C(sphere (0 : ℂ) r, ℂ)) (x : A × ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * circleFunctional r hr.le
    (κ x.1 * Ring.inverse (cauchyKernelProfile r x.2))

theorem analytic_cauchyTransformProfile {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℂ A] {r : ℝ} (hr : 0 < r) {U : Set A}
    {κ : A → C(sphere (0 : ℂ) r, ℂ)} (hκ : AnalyticOnNhd ℂ κ U) :
    AnalyticOnNhd ℂ (cauchyTransformProfile r hr κ) (U ×ˢ ball 0 r) := by
  intro x hx
  apply analyticAt_const.mul
  apply ((circleFunctional r hr.le).analyticAt _).comp
  apply (hκ x.1 hx.1).comp analyticAt_fst |>.mul
  have hi : AnalyticAt ℂ (fun y : ℂ => Ring.inverse (cauchyKernelProfile r y)) x.2 :=
    (analyticOnNhd_inverse _ (cauchyKernelProfile_isUnit hx.2)).comp
      (analytic_cauchyKernelProfile r x.2 (mem_univ _))
  exact hi.comp analyticAt_snd

theorem cauchyTransformProfile_eq {A : Type*} {r : ℝ} (hr : 0 < r)
    {κ : A → C(sphere (0 : ℂ) r, ℂ)} {q : A} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r))
    (he : ∀ z : sphere (0 : ℂ) r, κ q z = g z) {y : ℂ} (hy : y ∈ ball 0 r) :
    cauchyTransformProfile r hr κ (q, y) = g y := by
  have hunit := cauchyKernelProfile_isUnit hy
  have hEq : ∀ z : sphere (0 : ℂ) r,
      (κ q * Ring.inverse (cauchyKernelProfile r y)) z = ((z : ℂ) - y)⁻¹ * g z := by
    intro z
    simp only [ContinuousMap.mul_apply, continuousMap_ringInverse_apply _ hunit,
      cauchyKernelProfile_apply, he]
    ring
  rw [cauchyTransformProfile, circleFunctional_eq hr.le _ (fun z => (z - y)⁻¹ * g z) hEq]
  have hdiff : DiffContOnCl ℂ g (ball 0 r) :=
    (hg.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
  simpa only [smul_eq_mul] using hdiff.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hy

 

theorem fixed_contour_preparation_on_ball {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {F : A × ℂ → ℂ} (hF : AnalyticAt ℂ F 0) {d : ℕ}
    (hd : analyticOrderAt (fun y => F (0, y)) 0 = (d : ℕ∞)) :
    ∃ (r : ℝ) (U : Set A) (g : A × ℂ → ℂ),
      0 < r ∧ IsOpen U ∧ (0 : A) ∈ U ∧
      AnalyticOnNhd ℂ F (U ×ˢ closedBall 0 r) ∧
      AnalyticOnNhd ℂ g (U ×ˢ ball 0 r) ∧
      (∀ q ∈ U, ∀ y ∈ ball (0 : ℂ) r, g (q, y) ≠ 0) ∧
      (∀ q ∈ U, ∀ y ∈ sphere (0 : ℂ) r, F (q, y) ≠ 0) ∧
      (∀ q ∈ U, (contourPolynomial (fun y => F (q, y)) r d).Monic ∧
        (contourPolynomial (fun y => F (q, y)) r d).natDegree = d) ∧
      (∀ k, AnalyticOnNhd ℂ
        (fun q => (contourPolynomial (fun y => F (q, y)) r d).coeff k) U) ∧
      (∀ q ∈ U, ∀ y ∈ ball (0 : ℂ) r,
        F (q, y) = (contourPolynomial (fun y => F (q, y)) r d).eval y * g (q, y)) := by
  classical
  obtain ⟨r, U, φ, hr, hU, h0U, hFA, hφ, hφe, hφu, hm, hm0⟩ := fixed_circle_data hF hd
  have hfB (q : A) (hq : q ∈ U) : AnalyticOnNhd ℂ (fun y => F (q, y)) (closedBall 0 r) := by
    intro y hy
    exact (hFA (q, y) ⟨hq, hy⟩).comp (analyticAt_const.prod analyticAt_id)
  have hnB (q : A) (hq : q ∈ U) (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) : F (q, z) ≠ 0 := by
    rw [← hφe q hq ⟨z, hz⟩]
    exact (ContinuousMap.isUnit_iff_forall_ne_zero _).1 (hφu q hq) ⟨z, hz⟩
  have hfac (q : A) (hq : q ∈ U) :
      ∃ g : ℂ → ℂ, (contourPolynomial (fun y => F (q, y)) r d).Monic ∧
        (contourPolynomial (fun y => F (q, y)) r d).natDegree = d ∧
        AnalyticOnNhd ℂ g (closedBall 0 r) ∧
        (∀ z ∈ closedBall (0 : ℂ) r, g z ≠ 0) ∧
        EqOn (fun y => F (q, y))
          (fun y => (contourPolynomial (fun y => F (q, y)) r d).eval y * g y) (closedBall 0 r) := by
    obtain ⟨N, g, hN, hM, hD, hg, hgn, hfg⟩ := contour_fiber_factorization hr (hfB q hq) (hnB q hq)
    have hNd : N = d := by exact_mod_cast hN.symm.trans (hm0 q hq)
    subst N
    exact ⟨g, hM, hD, hg, hgn, hfg⟩
  have hpU (q : A) (hq : q ∈ U) : IsUnit (contourPolynomialProfile F r d q) := by
    rw [ContinuousMap.isUnit_iff_forall_ne_zero]
    intro z
    rw [contourPolynomialProfile_apply]
    obtain ⟨g, _, _, _, _, hfg⟩ := hfac q hq
    have he := hfg (sphere_subset_closedBall z.property)
    dsimp only at he
    exact left_ne_zero_of_mul (by rw [← he]; exact hnB q hq z z.property)
  let κ : A → C(sphere (0 : ℂ) r, ℂ) := fun q => φ q * Ring.inverse (contourPolynomialProfile F r d q)
  have hκ : AnalyticOnNhd ℂ κ U := by
    intro q hq
    exact (hφ q hq).mul ((analyticOnNhd_inverse _ (hpU q hq)).comp
      (analytic_contourPolynomialProfile hm d q hq))
  let g : A × ℂ → ℂ := cauchyTransformProfile r hr κ
  have hgFiber (q : A) (hq : q ∈ U) (v : ℂ → ℂ)
      (hv : AnalyticOnNhd ℂ v (closedBall 0 r))
      (hfv : EqOn (fun y => F (q, y))
        (fun y => (contourPolynomial (fun y => F (q, y)) r d).eval y * v y) (closedBall 0 r))
      (y : ℂ) (hy : y ∈ ball (0 : ℂ) r) : g (q, y) = v y := by
    apply cauchyTransformProfile_eq hr hv _ hy
    intro z
    dsimp only [κ]
    rw [ContinuousMap.mul_apply, continuousMap_ringInverse_apply _ (hpU q hq),
      hφe q hq, contourPolynomialProfile_apply]
    have he := hfv (sphere_subset_closedBall z.property)
    dsimp only at he
    rw [he]
    have hn : (contourPolynomial (fun y => F (q, y)) r d).eval (z : ℂ) ≠ 0 := by
      rw [← contourPolynomialProfile_apply]
      exact (ContinuousMap.isUnit_iff_forall_ne_zero _).1 (hpU q hq) z
    field_simp
  refine ⟨r, U, g, hr, hU, h0U, hFA, analytic_cauchyTransformProfile hr hκ, ?_, hnB, ?_,
    fun k => analytic_contourPolynomial_coeff hm d k, ?_⟩
  · intro q hq y hy
    obtain ⟨v, _, _, hv, hvn, hfv⟩ := hfac q hq
    rw [hgFiber q hq v hv hfv y hy]
    exact hvn y (ball_subset_closedBall hy)
  · intro q hq
    obtain ⟨_, hM, hD, _⟩ := hfac q hq
    exact ⟨hM, hD⟩
  · intro q hq y hy
    obtain ⟨v, _, _, hv, _, hfv⟩ := hfac q hq
    rw [hgFiber q hq v hv hfv y hy]
    exact hfv (ball_subset_closedBall hy)

 
theorem fixed_contour_preparation : FixedContourPreparationStatement := by
  intro n d F hF hd
  obtain ⟨r, U, g, hr, hU, h0, hf, hg, hgn, hfn, hP, hc, he⟩ :=
    fixed_contour_preparation_on_ball hF hd
  have hi : closedBall (0 : ℂ) (r / 2) ⊆ ball 0 r :=
    closedBall_subset_ball (half_lt_self hr)
  exact ⟨r, U, g, hr, hU, h0, hf, hg.mono (fun x hx => ⟨hx.1, hi hx.2⟩),
    (fun q hq y hy => hgn q hq y (hi hy)), hfn, hP, hc,
    (fun q hq y hy => he q hq y (hi hy))⟩

 
def normalizedCircleFunctional (r : ℝ) (hr : 0 < r) : C(sphere (0 : ℂ) r, ℂ) →L[ℂ] ℂ :=
  (2 * Real.pi * I)⁻¹ • circleFunctional r hr.le

 

def dividedCoeffProfile (P : Polynomial ℂ) (d : ℕ) (r : ℝ) (k : ℕ) :
    C(sphere (0 : ℂ) r, ℂ) :=
  ∑ i ∈ Finset.Icc (k + 1) d,
    (⟨fun z => (z : ℂ), continuous_subtype_val⟩ : C(sphere (0 : ℂ) r, ℂ)) ^ (i - (k + 1)) *
      ContinuousMap.const _ (P.coeff i)

theorem dividedCoeffProfile_apply {P : Polynomial ℂ} {d : ℕ} (hd : P.natDegree = d)
    (r : ℝ) (k : ℕ) (z : sphere (0 : ℂ) r) :
    dividedCoeffProfile P d r k z = (P /ₘ (Polynomial.X - Polynomial.C (z : ℂ))).coeff k := by
  rw [Polynomial.coeff_divByMonic_X_sub_C, hd]
  simp [dividedCoeffProfile]

theorem analytic_dividedCoeffProfile {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {P : A → Polynomial ℂ} {U : Set A}
    (hP : ∀ k, AnalyticOnNhd ℂ (fun q => (P q).coeff k) U) (d : ℕ) (r : ℝ) (k : ℕ) :
    AnalyticOnNhd ℂ (fun q => dividedCoeffProfile (P q) d r k) U := by
  intro q hq
  unfold dividedCoeffProfile
  apply Finset.analyticAt_fun_sum
  intro j _
  apply analyticAt_const.mul
  exact ((ContinuousLinearMap.const ℂ (sphere (0 : ℂ) r)).analyticAt _).comp (hP j q hq)

def divisionRemainder (P : Polynomial ℂ) (d : ℕ) (r : ℝ) (hr : 0 < r)
    (κ : C(sphere (0 : ℂ) r, ℂ)) : Polynomial ℂ :=
  ∑ k : Fin d, Polynomial.C (normalizedCircleFunctional r hr (κ * dividedCoeffProfile P d r k)) *
    Polynomial.X ^ (k : ℕ)

theorem divisionRemainder_degree_lt (P : Polynomial ℂ) (d : ℕ) (r : ℝ) (hr : 0 < r)
    (κ : C(sphere (0 : ℂ) r, ℂ)) : (divisionRemainder P d r hr κ).degree < d :=
  Polynomial.degree_sum_fin_lt _

theorem analytic_divisionRemainder_coeff {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {radius : ℝ} {P : A → Polynomial ℂ} {κ : A → C(sphere (0 : ℂ) radius, ℂ)} {U : Set A}
    (hP : ∀ k, AnalyticOnNhd ℂ (fun q => (P q).coeff k) U) (hκ : AnalyticOnNhd ℂ κ U)
    (d : ℕ) (hr : 0 < radius) (k : ℕ) :
    AnalyticOnNhd ℂ (fun q => (divisionRemainder (P q) d radius hr (κ q)).coeff k) U := by
  intro q hq
  simp only [divisionRemainder, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  apply Finset.analyticAt_fun_sum
  intro j _
  apply AnalyticAt.mul _ analyticAt_const
  exact ((normalizedCircleFunctional radius hr).analyticAt _).comp
    ((hκ q hq).mul (analytic_dividedCoeffProfile hP d radius j q hq))

private theorem eval_sum_of_degree_lt {P : Polynomial ℂ} {d : ℕ}
    (hd : P.degree < d) (y : ℂ) : P.eval y = ∑ k : Fin d, P.coeff k * y ^ (k : ℕ) := by
  by_cases hP : P = 0
  · simp [hP]
  · rw [Polynomial.eval_eq_sum_range' ((Polynomial.natDegree_lt_iff_degree_lt hP).2 hd)]
    exact (Fin.sum_univ_eq_sum_range _ _).symm

def dividedEvaluationProfile (P : Polynomial ℂ) (d : ℕ) (r : ℝ) (y : ℂ) :
    C(sphere (0 : ℂ) r, ℂ) := ∑ k : Fin d, (y ^ (k : ℕ)) • dividedCoeffProfile P d r k

theorem dividedEvaluationProfile_apply {P : Polynomial ℂ} (hP : P.Monic) {d : ℕ}
    (hd : P.natDegree = d) (r : ℝ) (y : ℂ) (z : sphere (0 : ℂ) r) :
    dividedEvaluationProfile P d r y z = (P /ₘ (Polynomial.X - Polynomial.C (z : ℂ))).eval y := by
  have hdeg : (P /ₘ (Polynomial.X - Polynomial.C (z : ℂ))).degree < d := by
    have hi := Polynomial.degree_divByMonic_lt P (Polynomial.X - Polynomial.C (z : ℂ))
      hP.ne_zero (by simp)
    simpa [Polynomial.degree_eq_natDegree hP.ne_zero, hd] using hi
  rw [eval_sum_of_degree_lt hdeg]
  simp only [dividedEvaluationProfile, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, dividedCoeffProfile_apply hd]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem divisionRemainder_eval (P : Polynomial ℂ) (d : ℕ) (r : ℝ) (hr : 0 < r)
    (κ : C(sphere (0 : ℂ) r, ℂ)) (y : ℂ) :
    (divisionRemainder P d r hr κ).eval y =
      normalizedCircleFunctional r hr (κ * dividedEvaluationProfile P d r y) := by
  simp only [divisionRemainder, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, dividedEvaluationProfile,
    Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

 

theorem fixed_circle_division {P : Polynomial ℂ} (hP : P.Monic) {d : ℕ}
    (hd : P.natDegree = d) {r : ℝ} (hr : 0 < r) {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (closedBall 0 r))
    (hPn : ∀ z ∈ sphere (0 : ℂ) r, P.eval z ≠ 0)
    (κ : C(sphere (0 : ℂ) r, ℂ))
    (hκ : ∀ z : sphere (0 : ℂ) r, κ z = G z / P.eval (z : ℂ))
    {y : ℂ} (hy : y ∈ ball (0 : ℂ) r) :
    G y = P.eval y * cauchyTransformProfile r hr (fun _ : Unit => κ) ((), y) +
      (divisionRemainder P d r hr κ).eval y := by
  have hk := cauchyKernelProfile_isUnit hy
  let T := κ * Ring.inverse (cauchyKernelProfile r y)
  let R := κ * dividedEvaluationProfile P d r y
  have hboundary : ∀ z : sphere (0 : ℂ) r,
      ((P.eval y) • T + R) z = ((z : ℂ) - y)⁻¹ * G z := by
    intro z
    have hdiff := congrArg (Polynomial.eval y) (P.modByMonic_add_div (Polynomial.X - Polynomial.C (z : ℂ)))
    rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at hdiff
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X] at hdiff
    have hn : (z : ℂ) - y ≠ 0 :=
      (ContinuousMap.isUnit_iff_forall_ne_zero _).1 hk z
    simp only [T, R, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul,
      ContinuousMap.mul_apply, continuousMap_ringInverse_apply _ hk,
      cauchyKernelProfile_apply, dividedEvaluationProfile_apply hP hd, hκ]
    field_simp [hPn z z.property, hn]
    linear_combination -(G (z : ℂ)) * hdiff
  have hc : normalizedCircleFunctional r hr ((P.eval y) • T + R) = G y := by
    change (2 * Real.pi * I)⁻¹ * circleFunctional r hr.le ((P.eval y) • T + R) = G y
    rw [circleFunctional_eq hr.le _ (fun z => (z - y)⁻¹ * G z) hboundary]
    have hdiff : DiffContOnCl ℂ G (ball 0 r) :=
      (hG.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
    simpa only [smul_eq_mul] using hdiff.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hy
  rw [divisionRemainder_eval, ← hc, map_add, map_smul]
  rfl

end DegeneratingTrees
end

end OAI


namespace OAI

/-! Fixed-contour preparation polynomials, division and stable root counts. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Metric Polynomial

namespace PathSelection.Preparation

lemma eqOn_closedBall_of_codiscrete {f g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (closedBall 0 r)) (hg : ContinuousOn g (closedBall 0 r))
    (heq : f =ᶠ[codiscreteWithin (closedBall 0 r)] g) :
    EqOn f g (closedBall 0 r) := by
  have hi : EqOn f g (ball 0 r) := by
    intro z hz
    have hznear : closedBall (0 : ℂ) r ∈ 𝓝 z :=
      mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall
    have hle : 𝓝[≠] z ≤ codiscreteWithin (closedBall (0 : ℂ) r) := by
      rw [codiscreteWithin]
      exact le_iSup_of_le z (le_iSup_of_le (ball_subset_closedBall hz) (by
        rw [sdiff_eq, nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hznear)]))
    have he := heq.filter_mono hle
    have hfc := (hf z (ball_subset_closedBall hz)).continuousAt hznear
    have hgc := (hg z (ball_subset_closedBall hz)).continuousAt hznear
    exact tendsto_nhds_unique (hfc.tendsto.mono_left nhdsWithin_le_nhds)
      ((hgc.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)
  exact hi.of_subset_closure hf hg ball_subset_closedBall (by rw [closure_ball _ hr.ne'])

 

lemma nonnegative_factor_polynomial (d : ℂ → ℤ) (hd : d.HasFiniteSupport)
    (hnonneg : ∀ z, 0 ≤ d z) :
    ∃ P : ℂ[X], P.Monic ∧
      (∀ z, P.eval z = (∏ᶠ w : ℂ, (fun t : ℂ => t-w) ^ d w) z) ∧
      (∀ z, P.eval z = 0 → z ∈ Function.support d) := by
  classical
  let s := hd.toFinset
  let P : ℂ[X] := ∏ w ∈ s, (X - C w) ^ (d w).toNat
  have hP : P.Monic := monic_prod_of_monic s _ (fun w _ => (monic_X_sub_C w).pow _)
  have heq (z : ℂ) : P.eval z = (∏ᶠ w : ℂ, (fun t : ℂ => t-w) ^ d w) z := by
    rw [Function.FactorizedRational.finprod_eq_fun hd]
    dsimp only
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := s) ?_]
    · simp only [P, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
      apply Finset.prod_congr rfl
      intro w _
      conv_rhs => rw [← Int.toNat_of_nonneg (hnonneg w), zpow_natCast]
    · intro w hw
      apply hd.mem_toFinset.mpr
      by_contra hn
      have : d w = 0 := by simpa using hn
      simp [Function.mem_mulSupport, this] at hw
  refine ⟨P, hP, heq, ?_⟩
  intro z hz
  by_contra hn
  have hprod : P.eval z ≠ 0 := by
    simp only [P, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro w hw
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    intro hzw
    apply hn
    rw [hzw]
    exact hd.mem_toFinset.mp hw
  exact hprod hz

 

theorem exists_preparation_on_disc {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hnz : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0) :
    ∃ P : ℂ[X], P.Monic ∧
      (∀ z : ℂ, P.eval z = 0 → z ∈ ball 0 r) ∧
      ∃ u : ℂ → ℂ, AnalyticOnNhd ℂ u (closedBall 0 r) ∧
        (∀ z ∈ closedBall (0 : ℂ) r, u z ≠ 0) ∧
        EqOn f (fun z => P.eval z * u z) (closedBall 0 r) := by
  have hz : (r : ℂ) ∈ sphere (0 : ℂ) r := by
    simp [abs_of_pos hr]
  have hzc := sphere_subset_closedBall hz
  have horder : ∀ z ∈ closedBall (0 : ℂ) r, meromorphicOrderAt f z ≠ ⊤ := by
    intro z hz'
    apply hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (isConnected_closedBall hr.le).isPreconnected hzc hz'
    rw [(hf _ hzc).meromorphicOrderAt_eq, (hf _ hzc).analyticOrderAt_eq_zero.mpr (hnz _ hz)]
    simp
  let d := MeromorphicOn.divisor f (closedBall (0 : ℂ) r)
  have hd : (d : ℂ → ℤ).HasFiniteSupport := d.finiteSupport (isCompact_closedBall _ _)
  have hdpos : ∀ z, 0 ≤ d z := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf
  obtain ⟨P, hP, hPeq, hroot⟩ := nonnegative_factor_polynomial d hd hdpos
  obtain ⟨u, hu, hunz, heq⟩ := hf.meromorphicOn.extract_zeros_poles
    (fun z => horder z z.property) hd
  refine ⟨P, hP, ?_, u, hu, fun z hz => hunz ⟨z, hz⟩, ?_⟩
  · intro z hz
    have hs := hroot z hz
    have hzc := d.supportWithinDomain hs
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hzc) with hlt | he
    · exact mem_ball_zero_iff.mpr hlt
    have hzsp : z ∈ sphere (0 : ℂ) r := mem_sphere_zero_iff_norm.mpr he
    have hd0 : d z = 0 := by
      dsimp [d]
      rw [hf.meromorphicOn.divisor_apply hzc, (hf z hzc).meromorphicOrderAt_eq,
        (hf z hzc).analyticOrderAt_eq_zero.mpr (hnz z hzsp)]
      simp
    exact False.elim (hs hd0)
  · apply eqOn_closedBall_of_codiscrete hr hf.continuousOn
      (P.continuous.continuousOn.mul hu.continuousOn)
    filter_upwards [heq] with z hz
    change f z = P.eval z * u z
    rw [hPeq]
    simpa only [d, Pi.smul_apply', smul_eq_mul] using hz

 
def divisionKernel (P : ℂ[X]) (w : ℂ) : ℂ[X] :=
  ∑ n ∈ Finset.range (P.natDegree + 1),
    ∑ k ∈ Finset.range n, C (P.coeff n * w ^ (n - 1 - k)) * X ^ k

lemma divisionKernel_eval (P : ℂ[X]) (w y : ℂ) :
    (divisionKernel P w).eval y * (w-y) = P.eval w - P.eval y := by
  simp only [divisionKernel, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [Finset.sum_mul]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hk (n : ℕ) :
      (∑ k ∈ Finset.range n, w ^ (n - 1 - k) * y ^ k) * (w-y) = w^n-y^n := by
    calc
      _ = (∑ k ∈ Finset.range n, y ^ k * w ^ (n-1-k)) * (w-y) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
      _ = (∑ k ∈ Finset.range n, w ^ k * y ^ (n-1-k)) * (w-y) := by
        rw [geom_sum₂_comm y w n]
      _ = _ := geom_sum₂_mul w y n
  simp_rw [mul_assoc, hk, mul_sub]
  rw [Finset.sum_sub_distrib, eval_eq_sum_range, eval_eq_sum_range]

lemma divisionKernel_degree (P : ℂ[X]) (w : ℂ) :
    (divisionKernel P w).degree < P.natDegree := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  simp only [divisionKernel, finsetSum_coeff, coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  have hnd : n ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hne : k ≠ m := by omega
  simp [hne.symm]

lemma divisionKernel_continuous (P : ℂ[X]) (y : ℂ) :
    Continuous (fun w => (divisionKernel P w).eval y) := by
  simp only [divisionKernel, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  fun_prop

open scoped Real
open Complex

 

theorem fixed_circle_division {G : ℂ → ℂ} {P : ℂ[X]} {r : ℝ}
    (hG : AnalyticOnNhd ℂ G (closedBall 0 r))
    (hP : ∀ w ∈ sphere (0 : ℂ) r, P.eval w ≠ 0)
    {y : ℂ} (hy : y ∈ ball (0 : ℂ) r) :
    G y = P.eval y * ((2 * π * I)⁻¹ *
      ∮ w in C(0, r), G w / (P.eval w * (w-y))) +
      (2 * π * I)⁻¹ * ∮ w in C(0, r),
        G w / P.eval w * (divisionKernel P w).eval y := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg y) (mem_ball_zero_iff.mp hy)
  have hwy : ∀ w ∈ sphere (0 : ℂ) r, w-y ≠ 0 := by
    intro w hw
    apply sub_ne_zero.mpr
    intro he
    subst w
    exact (ne_of_lt (mem_ball_zero_iff.mp hy)) (mem_sphere_zero_iff_norm.mp hw)
  have hc₁ : ContinuousOn (fun w => G w / (P.eval w * (w-y))) (sphere 0 r) :=
    (hG.continuousOn.mono sphere_subset_closedBall).div
      (P.continuous.continuousOn.mul (continuousOn_id.sub continuousOn_const))
      (fun w hw => mul_ne_zero (hP w hw) (hwy w hw))
  have hc₂ : ContinuousOn (fun w => G w / P.eval w * (divisionKernel P w).eval y)
      (sphere 0 r) :=
    ((hG.continuousOn.mono sphere_subset_closedBall).div P.continuous.continuousOn hP).mul
      (divisionKernel_continuous P y).continuousOn
  have hi : (∮ w in C(0, r), G w / (w-y)) =
      P.eval y * (∮ w in C(0, r), G w / (P.eval w * (w-y))) +
        ∮ w in C(0, r), G w / P.eval w * (divisionKernel P w).eval y := by
    have hci₁ : CircleIntegrable (fun w => P.eval y * (G w / (P.eval w * (w-y)))) 0 r :=
      (continuousOn_const.mul hc₁).circleIntegrable hr.le
    rw [← circleIntegral.integral_const_mul,
      ← circleIntegral.integral_add hci₁ (hc₂.circleIntegrable hr.le)]
    apply circleIntegral.integral_congr hr.le
    intro w hw
    have hk := divisionKernel_eval P w y
    field_simp [hP w hw, hwy w hw]
    linear_combination -G w * hk
  have hc := circleIntegral_div_sub_of_differentiable_on_off_countable
    Set.countable_empty hy hG.continuousOn
    (fun z hz => (hG z (ball_subset_closedBall hz.1)).differentiableAt)
  rw [hc] at hi
  have htwo : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  apply (mul_left_cancel₀ htwo)
  rw [mul_add]
  field_simp
  simpa only [div_mul_eq_mul_div] using hi

 
def divisionRemainder (G : ℂ → ℂ) (P : ℂ[X]) (r : ℝ) : ℂ[X] :=
  ∑ n ∈ Finset.range (P.natDegree + 1),
    ∑ k ∈ Finset.range n,
      C ((2 * π * I)⁻¹ * ∮ w in C(0,r),
        G w / P.eval w * (P.coeff n * w ^ (n-1-k))) * X ^ k

lemma divisionRemainder_degree (G : ℂ → ℂ) (P : ℂ[X]) (r : ℝ) :
    (divisionRemainder G P r).degree < P.natDegree := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  simp only [divisionRemainder, finsetSum_coeff, coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  have hnd : n ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hne : m ≠ k := by omega
  simp [hne]

lemma divisionRemainder_eval {G : ℂ → ℂ} {P : ℂ[X]} {r : ℝ} (hr : 0 ≤ r)
    (hG : ContinuousOn G (sphere 0 r))
    (hP : ∀ w ∈ sphere (0 : ℂ) r, P.eval w ≠ 0) (y : ℂ) :
    (divisionRemainder G P r).eval y =
      (2 * π * I)⁻¹ * ∮ w in C(0,r), G w / P.eval w * (divisionKernel P w).eval y := by
  have hcont (n k : ℕ) : ContinuousOn
      (fun w => G w / P.eval w * (P.coeff n * w ^ (n-1-k)) * y ^ k) (sphere 0 r) :=
    (((hG.div P.continuous.continuousOn hP).mul
      (continuousOn_const.mul (continuousOn_id.pow _))).mul continuousOn_const)
  simp only [divisionRemainder, divisionKernel, eval_finsetSum, eval_mul, eval_C,
    eval_pow, eval_X]
  simp_rw [Finset.mul_sum]
  rw [circleIntegral.integral_fun_sum (fun n _ =>
    (continuousOn_finsetSum _ (fun k _ => by simpa only [mul_assoc] using hcont n k)).circleIntegrable hr)]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [circleIntegral.integral_fun_sum (fun k _ =>
    (by simpa only [mul_assoc] using (hcont n k).circleIntegrable hr))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show (fun w => G w / P.eval w * (P.coeff n * w ^ (n-1-k) * y^k)) =
      (fun w => (G w / P.eval w * (P.coeff n * w ^ (n-1-k))) • y^k) by
        funext w; simp only [smul_eq_mul, mul_assoc], circleIntegral.integral_smul_const]
  simp only [smul_eq_mul, mul_assoc]

def divisionQuotient (G : ℂ → ℂ) (P : ℂ[X]) (r : ℝ) (y : ℂ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ w in C(0,r), G w / (P.eval w * (w-y))

lemma divisionQuotient_analyticOnNhd {G : ℂ → ℂ} {P : ℂ[X]} {r : ℝ} (hr : 0 < r)
    (hG : ContinuousOn G (sphere 0 r))
    (hP : ∀ w ∈ sphere (0 : ℂ) r, P.eval w ≠ 0) :
    AnalyticOnNhd ℂ (divisionQuotient G P r) (ball 0 r) := by
  have hi := (hG.div P.continuous.continuousOn hP).circleIntegrable hr.le
  have ha := (hasFPowerSeriesOn_cauchy_integral (R := ⟨r, hr.le⟩) hi hr).analyticOnNhd
  convert! ha using 1
  · funext y
    simp only [divisionQuotient, smul_eq_mul, Pi.div_apply, div_eq_mul_inv, mul_inv_rev]
    congr 1
    apply congrArg (fun f : ℂ → ℂ => ∮ w in C(0,r), f w)
    funext w
    ring
  · exact (Metric.eball_coe (x := (0 : ℂ)) (ε := ⟨r, hr.le⟩)).symm

 

theorem fixed_disc_division {G : ℂ → ℂ} {P : ℂ[X]} {r : ℝ} (hr : 0 < r)
    (hG : AnalyticOnNhd ℂ G (closedBall 0 r))
    (hP : ∀ w ∈ sphere (0 : ℂ) r, P.eval w ≠ 0) :
    AnalyticOnNhd ℂ (divisionQuotient G P r) (ball 0 r) ∧
    (divisionRemainder G P r).degree < P.natDegree ∧
    EqOn G (fun y => P.eval y * divisionQuotient G P r y +
      (divisionRemainder G P r).eval y) (ball 0 r) := by
  refine ⟨divisionQuotient_analyticOnNhd hr (hG.continuousOn.mono sphere_subset_closedBall) hP,
    divisionRemainder_degree G P r, ?_⟩
  intro y hy
  dsimp only
  rw [divisionRemainder_eval hr.le (hG.continuousOn.mono sphere_subset_closedBall) hP]
  exact fixed_circle_division hG hP hy

 

lemma eqOn_deriv_closedBall {f g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r))
    (heq : EqOn f g (closedBall 0 r)) : EqOn (deriv f) (deriv g) (closedBall 0 r) := by
  have hi := (heq.mono ball_subset_closedBall).deriv isOpen_ball
  exact hi.of_subset_closure hf.deriv.continuousOn hg.deriv.continuousOn
    ball_subset_closedBall (by rw [closure_ball _ hr.ne'])

lemma circleIntegral_root_sum {r : ℝ} (hr : 0 < r) (l : ℕ) (a : Multiset ℂ)
    (ha : ∀ w ∈ a, w ∈ ball (0 : ℂ) r) :
    CircleIntegrable (fun z => (a.map (fun w => z^l / (z-w))).sum) 0 r ∧
    (∮ z in C(0,r), (a.map (fun w => z^l / (z-w))).sum) =
      (2 * π * I) * (a.map (fun w => w^l)).sum := by
  induction a using Multiset.induction_on with
  | empty => simp [circleIntegral]
  | cons a s ih =>
    have hai : a ∈ ball (0 : ℂ) r := ha a (by simp)
    obtain ⟨hsi, hseq⟩ := ih (fun w hw => ha w (by simp [hw]))
    have hane (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) : z-a ≠ 0 := by
      apply sub_ne_zero.mpr
      rintro rfl
      exact (ne_of_lt (mem_ball_zero_iff.mp hai)) (mem_sphere_zero_iff_norm.mp hz)
    have hai' : CircleIntegrable (fun z => z^l / (z-a)) 0 r :=
      ((continuousOn_id.pow l).div (continuousOn_id.sub continuousOn_const) hane).circleIntegrable hr.le
    have haeq : (∮ z in C(0,r), z^l / (z-a)) = (2 * π * I) * a^l :=
      circleIntegral_div_sub_of_differentiable_on_off_countable Set.countable_empty hai
        ((continuous_pow l).continuousOn) (fun z _ => by fun_prop)
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact ⟨hai'.add hsi, by rw [circleIntegral.integral_add hai' hsi, haeq, hseq, mul_add]⟩

 
theorem polynomial_power_sum_contour {P : ℂ[X]} {r : ℝ} (hr : 0 < r)
    (hP : P ≠ 0) (hroot : ∀ z : ℂ, P.eval z = 0 → z ∈ ball 0 r) (l : ℕ) :
    (2 * π * I)⁻¹ * (∮ z in C(0,r), z^l * P.derivative.eval z / P.eval z) =
      (P.roots.map (fun w => w^l)).sum := by
  have ha : ∀ w ∈ P.roots, w ∈ ball (0 : ℂ) r := fun w hw =>
    hroot w ((mem_roots hP).mp hw)
  have hi := (circleIntegral_root_sum hr l P.roots ha).2
  have he : (∮ z in C(0,r), z^l * P.derivative.eval z / P.eval z) =
      ∮ z in C(0,r), (P.roots.map (fun w => z^l / (z-w))).sum := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hnz : P.eval z ≠ 0 := by
      intro he
      exact (ne_of_lt (mem_ball_zero_iff.mp (hroot z he))) (mem_sphere_zero_iff_norm.mp hz)
    dsimp only
    rw [mul_div_assoc, (IsAlgClosed.splits P).eval_derivative_div_eval_of_ne_zero hnz,
      ← Multiset.sum_map_mul_left]
    simp only [mul_one_div]
  rw [he, hi, ← mul_assoc, inv_mul_cancel₀, one_mul]
  simp [Real.pi_ne_zero, I_ne_zero]

 

theorem preparation_power_sum_contour {f u : ℂ → ℂ} {P : ℂ[X]} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (hP : P.Monic)
    (hroot : ∀ z : ℂ, P.eval z = 0 → z ∈ ball 0 r)
    (hu : AnalyticOnNhd ℂ u (closedBall 0 r))
    (hunz : ∀ z ∈ closedBall (0 : ℂ) r, u z ≠ 0)
    (heq : EqOn f (fun z => P.eval z * u z) (closedBall 0 r)) (l : ℕ) :
    (2 * π * I)⁻¹ * (∮ z in C(0,r), z^l * deriv f z / f z) =
      (P.roots.map (fun w => w^l)).sum := by
  have hPa : AnalyticOnNhd ℂ (fun z => P.eval z) (closedBall 0 r) :=
    fun z _ => AnalyticOnNhd.eval_polynomial P z (mem_univ z)
  have hdeq := eqOn_deriv_closedBall hr hf (hPa.mul hu) heq
  have hPn (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) : P.eval z ≠ 0 := by
    intro he
    exact (ne_of_lt (mem_ball_zero_iff.mp (hroot z he))) (mem_sphere_zero_iff_norm.mp hz)
  have hunit : AnalyticOnNhd ℂ (fun z => z^l * deriv u z / u z) (closedBall 0 r) :=
    ((analyticOnNhd_id.pow l).mul hu.deriv).div hu hunz
  have hzero : (∮ z in C(0,r), z^l * deriv u z / u z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      hunit.continuousOn (fun z hz => (hunit z (ball_subset_closedBall hz.1)).differentiableAt)
  have hpoly : CircleIntegrable (fun z => z^l * P.derivative.eval z / P.eval z) 0 r :=
    (((continuousOn_id.pow l).mul P.derivative.continuous.continuousOn).div
      P.continuous.continuousOn hPn).circleIntegrable hr.le
  have hi : (∮ z in C(0,r), z^l * deriv f z / f z) =
      (∮ z in C(0,r), z^l * P.derivative.eval z / P.eval z) +
      ∮ z in C(0,r), z^l * deriv u z / u z := by
    rw [← circleIntegral.integral_add hpoly
      ((hunit.continuousOn.mono sphere_subset_closedBall).circleIntegrable hr.le)]
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hzc := sphere_subset_closedBall hz
    dsimp only
    rw [heq hzc, hdeq hzc, deriv_fun_mul (P.differentiableAt) (hu z hzc).differentiableAt,
      (P.hasDerivAt z).deriv]
    field_simp [hPn z hz, hunz z hzc]
  rw [hi, hzero, add_zero]
  exact polynomial_power_sum_contour hr hP.ne_zero hroot l

 

def newtonEsymm (powerSum : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 1 else (n : ℂ)⁻¹ * (-1)^(n+1) *
    ∑ a ∈ (Finset.HasAntidiagonal.antidiagonal n).filter (fun a => a.1 < n),
      if h : a.1 < n then (-1)^a.1 * newtonEsymm powerSum a.1 * powerSum a.2 else 0
termination_by n
decreasing_by assumption

lemma multiset_newton_identity (a : Multiset ℂ) (n : ℕ) :
    (n : ℂ) * a.esymm n = (-1)^(n+1) *
        ∑ t ∈ (Finset.HasAntidiagonal.antidiagonal n).filter (fun t => t.1 < n),
          (-1)^t.1 * a.esymm t.1 * (a.map (fun w => w^t.2)).sum := by
  classical
  have h := congrArg (MvPolynomial.aeval (R := ℂ) (fun w : a => (w : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum a ℂ n)
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe] at h
  convert h using 2
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
  rw [← Finset.sum_map_val (Finset.univ : Finset a)]
  exact (congrArg Multiset.sum (Multiset.map_univ a (fun w => w^t.2))).symm

lemma newtonEsymm_eq (a : Multiset ℂ) (n : ℕ) :
    newtonEsymm (fun k => (a.map (fun w => w^k)).sum) n = a.esymm n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [newtonEsymm]
    split_ifs with hn
    · subst n
      simp [Multiset.esymm]
    · have hsum : (∑ t ∈ (Finset.HasAntidiagonal.antidiagonal n).filter (fun t => t.1 < n),
          if h : t.1 < n then (-1 : ℂ)^t.1 * newtonEsymm (fun k => (a.map (fun w => w^k)).sum) t.1 *
            (a.map (fun w => w^t.2)).sum else 0) =
        ∑ t ∈ (Finset.HasAntidiagonal.antidiagonal n).filter (fun t => t.1 < n),
          (-1 : ℂ)^t.1 * a.esymm t.1 * (a.map (fun w => w^t.2)).sum := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [dif_pos (Finset.mem_filter.mp ht).2, ih t.1 (Finset.mem_filter.mp ht).2]
      rw [hsum, mul_assoc, ← multiset_newton_identity]
      exact inv_mul_cancel_left₀ (by exact_mod_cast hn) _

 

def contourPowerSum (f : ℂ → ℂ) (r : ℝ) (l : ℕ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ z in C(0,r), z^l * deriv f z / f z

 
def preparationPolynomial (f : ℂ → ℂ) (r : ℝ) (d : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (d+1),
    C ((-1)^(d-k) * newtonEsymm (contourPowerSum f r) (d-k)) * X^k

lemma polynomial_newton_formula (P : ℂ[X]) (hP : P.Monic) :
    (∑ k ∈ Finset.range (P.natDegree+1),
      C ((-1)^(P.natDegree-k) *
        newtonEsymm (fun l => (P.roots.map (fun w => w^l)).sum) (P.natDegree-k)) * X^k) = P := by
  conv_rhs => rw [P.as_sum_range_C_mul_X_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [newtonEsymm_eq,
    coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits P) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)),
    hP.leadingCoeff, one_mul]

lemma preparationPolynomial_eq {f u : ℂ → ℂ} {P : ℂ[X]} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (hP : P.Monic)
    (hroot : ∀ z : ℂ, P.eval z = 0 → z ∈ ball 0 r)
    (hu : AnalyticOnNhd ℂ u (closedBall 0 r))
    (hunz : ∀ z ∈ closedBall (0 : ℂ) r, u z ≠ 0)
    (heq : EqOn f (fun z => P.eval z * u z) (closedBall 0 r)) :
    preparationPolynomial f r P.natDegree = P := by
  have hs : contourPowerSum f r = fun l => (P.roots.map (fun w => w^l)).sum :=
    funext (preparation_power_sum_contour hr hf hP hroot hu hunz heq)
  simpa only [preparationPolynomial, hs] using polynomial_newton_formula P hP

lemma divisionQuotient_eq_unit {f u : ℂ → ℂ} {P : ℂ[X]} {r : ℝ}
    (hu : AnalyticOnNhd ℂ u (closedBall 0 r))
    (hPn : ∀ z ∈ sphere (0 : ℂ) r, P.eval z ≠ 0)
    (heq : EqOn f (fun z => P.eval z * u z) (sphere 0 r)) :
    EqOn (divisionQuotient f P r) u (ball 0 r) := by
  intro y hy
  have hr : 0 < r := (mem_ball_zero_iff.mp hy).trans_le' (norm_nonneg y)
  have hi : (∮ z in C(0,r), f z / (P.eval z * (z-y))) =
      ∮ z in C(0,r), u z / (z-y) := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    dsimp only
    rw [heq hz]
    exact mul_div_mul_left (u z) (z-y) (hPn z hz)
  have hc := circleIntegral_div_sub_of_differentiable_on_off_countable
    Set.countable_empty hy hu.continuousOn
      (fun z hz => (hu z (ball_subset_closedBall hz.1)).differentiableAt)
  rw [divisionQuotient, hi, hc, ← mul_assoc, inv_mul_cancel₀, one_mul]
  simp [Real.pi_ne_zero, I_ne_zero]

 

theorem fixed_contour_preparation {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hnz : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0) :
    ∃ d : ℕ, let W := preparationPolynomial f r d
      W.Monic ∧ W.natDegree = d ∧
      (∀ z : ℂ, W.eval z = 0 → z ∈ ball 0 r) ∧
      AnalyticOnNhd ℂ (divisionQuotient f W r) (ball 0 r) ∧
      (∀ z ∈ ball (0 : ℂ) r, divisionQuotient f W r z ≠ 0) ∧
      EqOn f (fun z => W.eval z * divisionQuotient f W r z) (ball 0 r) := by
  obtain ⟨P, hP, hroot, u, hu, hunz, heq⟩ := exists_preparation_on_disc hr hf hnz
  refine ⟨P.natDegree, ?_⟩
  dsimp only
  rw [preparationPolynomial_eq hr hf hP hroot hu hunz heq]
  have hPn (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) : P.eval z ≠ 0 := by
    intro he
    exact (ne_of_lt (mem_ball_zero_iff.mp (hroot z he))) (mem_sphere_zero_iff_norm.mp hz)
  have hquot := divisionQuotient_eq_unit hu hPn (heq.mono sphere_subset_closedBall)
  refine ⟨hP, rfl, hroot,
    divisionQuotient_analyticOnNhd hr (hf.continuousOn.mono sphere_subset_closedBall) hPn, ?_, ?_⟩
  · intro z hz
    rw [hquot hz]
    exact hunz z (ball_subset_closedBall hz)
  · intro z hz
    simp only [heq (ball_subset_closedBall hz), hquot hz]

lemma preparation_zero_count {f u : ℂ → ℂ} {P : ℂ[X]} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (hP : P.Monic)
    (hroot : ∀ z : ℂ, P.eval z = 0 → z ∈ ball 0 r)
    (hu : AnalyticOnNhd ℂ u (closedBall 0 r))
    (hunz : ∀ z ∈ closedBall (0 : ℂ) r, u z ≠ 0)
    (heq : EqOn f (fun z => P.eval z * u z) (closedBall 0 r)) :
    contourPowerSum f r 0 = (P.natDegree : ℂ) := by
  have h := preparation_power_sum_contour hr hf hP hroot hu hunz heq 0
  simpa [contourPowerSum, ← (IsAlgClosed.splits P).natDegree_eq_card_roots] using h

lemma contour_zero_count_nat {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hnz : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0) :
    contourPowerSum f r 0 ∈ Set.range (fun n : ℕ => (n : ℂ)) := by
  obtain ⟨P, hP, hroot, u, hu, hunz, heq⟩ := exists_preparation_on_disc hr hf hnz
  exact ⟨P.natDegree, (preparation_zero_count hr hf hP hroot hu hunz heq).symm⟩

lemma continuousOn_circleIntegral {E : Type*} [NormedAddCommGroup E]
    {A : Set E} {F : E → ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hA : IsCompact A) (hF : ContinuousOn (Function.uncurry F) (A ×ˢ sphere 0 r)) :
    ContinuousOn (fun a => ∮ z in C(0,r), F a z) A := by
  have hu := (hA.prod (isCompact_sphere (0 : ℂ) r)).uniformContinuousOn_of_continuous hF
  intro a ha
  apply TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn hr
  · filter_upwards [self_mem_nhdsWithin] with b hb
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨hb, hz⟩)
  · exact hu.tendstoUniformlyOn ha

 

theorem contour_zero_count_constant {E : Type*} [NormedAddCommGroup E]
    {A : Set E} {F : E → ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hA : IsCompact A) (hcA : IsPreconnected A)
    (hf : ∀ a ∈ A, AnalyticOnNhd ℂ (F a) (closedBall 0 r))
    (hnz : ∀ a ∈ A, ∀ z ∈ sphere (0 : ℂ) r, F a z ≠ 0)
    (hF : ContinuousOn (Function.uncurry F) (A ×ˢ sphere 0 r))
    (hdF : ContinuousOn (fun p : E × ℂ => deriv (F p.1) p.2) (A ×ˢ sphere 0 r))
    {a b : E} (ha : a ∈ A) (hb : b ∈ A) :
    contourPowerSum (F a) r 0 = contourPowerSum (F b) r 0 := by
  have hi : ContinuousOn (fun a => contourPowerSum (F a) r 0) A := by
    have h := continuousOn_circleIntegral (F := fun a z => deriv (F a) z / F a z) hr.le hA
      (hdF.div hF (fun p hp => hnz p.1 hp.1 p.2 hp.2))
    simpa only [contourPowerSum, pow_zero, one_mul] using h.const_mul ((2 * π * I)⁻¹)
  have hc : (Set.range (fun n : ℕ => (n : ℂ))).Countable := countable_range _
  have hsub : (fun a => contourPowerSum (F a) r 0) '' A ⊆
      Set.range (fun n : ℕ => (n : ℂ)) := by
    rintro _ ⟨a, ha, rfl⟩
    exact contour_zero_count_nat hr (hf a ha) (hnz a ha)
  exact hc.isTotallyDisconnected _ hsub (hcA.image _ hi)
    (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)

 

theorem contour_zero_count_eq_of_norm_sub_lt {f g : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r))
    (hsmall : ∀ z ∈ sphere (0 : ℂ) r, ‖g z - f z‖ < ‖f z‖) :
    contourPowerSum f r 0 = contourPowerSum g r 0 := by
  let F : ℝ → ℂ → ℂ := fun t z => f z + (t : ℂ) * (g z - f z)
  have hfa (t : ℝ) : AnalyticOnNhd ℂ (F t) (closedBall 0 r) :=
    hf.add (analyticOnNhd_const.mul (hg.sub hf))
  have hnz (t : ℝ) (ht : t ∈ Icc 0 1) (z : ℂ) (hz : z ∈ sphere 0 r) : F t z ≠ 0 := by
    have hn : ‖(t : ℂ) * (g z - f z)‖ < ‖f z‖ := by
      rw [norm_mul, Complex.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt (hsmall z hz)
    intro he
    have he' : f z = -((t : ℂ) * (g z - f z)) := eq_neg_of_add_eq_zero_left he
    have he'' := congrArg norm he'
    rw [norm_neg] at he''
    exact (ne_of_lt hn) he''.symm
  have hs : ∀ p ∈ (Icc (0 : ℝ) 1) ×ˢ sphere (0 : ℂ) r, p.2 ∈ closedBall (0 : ℂ) r :=
    fun _ hp => sphere_subset_closedBall hp.2
  have hfc : ContinuousOn (fun p : ℝ × ℂ => f p.2) (Icc (0 : ℝ) 1 ×ˢ sphere 0 r) :=
    hf.continuousOn.comp continuous_snd.continuousOn hs
  have hgc : ContinuousOn (fun p : ℝ × ℂ => g p.2) (Icc (0 : ℝ) 1 ×ˢ sphere 0 r) :=
    hg.continuousOn.comp continuous_snd.continuousOn hs
  have hdfc : ContinuousOn (fun p : ℝ × ℂ => deriv f p.2) (Icc (0 : ℝ) 1 ×ˢ sphere 0 r) :=
    hf.deriv.continuousOn.comp continuous_snd.continuousOn hs
  have hdgc : ContinuousOn (fun p : ℝ × ℂ => deriv g p.2) (Icc (0 : ℝ) 1 ×ˢ sphere 0 r) :=
    hg.deriv.continuousOn.comp continuous_snd.continuousOn hs
  have htc : ContinuousOn (fun p : ℝ × ℂ => (p.1 : ℂ)) (Icc (0 : ℝ) 1 ×ˢ sphere 0 r) :=
    (Complex.continuous_ofReal.comp continuous_fst).continuousOn
  have hFc : ContinuousOn (Function.uncurry F) (Icc (0 : ℝ) 1 ×ˢ sphere 0 r) :=
    hfc.add (htc.mul (hgc.sub hfc))
  have hdFc : ContinuousOn (fun p : ℝ × ℂ => deriv (F p.1) p.2)
      (Icc (0 : ℝ) 1 ×ˢ sphere 0 r) := by
    apply (hdfc.add (htc.mul (hdgc.sub hdfc))).congr
    intro p hp
    have hfd := (hf p.2 (hs p hp)).differentiableAt
    have hgd := (hg p.2 (hs p hp)).differentiableAt
    dsimp only [F]
    simpa only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.add_def] using
      (hfd.hasDerivAt.add ((hgd.hasDerivAt.sub hfd.hasDerivAt).const_mul (p.1 : ℂ))).deriv
  have h := contour_zero_count_constant hr isCompact_Icc isPreconnected_Icc
    (fun t _ => hfa t) hnz hFc hdFc (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  simpa [F] using h

 

theorem fixed_contour_preparation_of_count {f : ℂ → ℂ} {r : ℝ} {d : ℕ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hnz : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0)
    (hcount : contourPowerSum f r 0 = (d : ℂ)) :
    let W := preparationPolynomial f r d
    W.Monic ∧ W.natDegree = d ∧
      (∀ z : ℂ, W.eval z = 0 → z ∈ ball 0 r) ∧
      AnalyticOnNhd ℂ (divisionQuotient f W r) (ball 0 r) ∧
      (∀ z ∈ ball (0 : ℂ) r, divisionQuotient f W r z ≠ 0) ∧
      EqOn f (fun z => W.eval z * divisionQuotient f W r z) (ball 0 r) := by
  obtain ⟨P, hP, hroot, u, hu, hunz, heq⟩ := exists_preparation_on_disc hr hf hnz
  have hd : P.natDegree = d := by
    exact_mod_cast (preparation_zero_count hr hf hP hroot hu hunz heq).symm.trans hcount
  dsimp only
  rw [← hd, preparationPolynomial_eq hr hf hP hroot hu hunz heq]
  have hPn (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) : P.eval z ≠ 0 := by
    intro he
    exact (ne_of_lt (mem_ball_zero_iff.mp (hroot z he))) (mem_sphere_zero_iff_norm.mp hz)
  have hquot := divisionQuotient_eq_unit hu hPn (heq.mono sphere_subset_closedBall)
  refine ⟨hP, rfl, hroot,
    divisionQuotient_analyticOnNhd hr (hf.continuousOn.mono sphere_subset_closedBall) hPn, ?_, ?_⟩
  · intro z hz
    rw [hquot hz]
    exact hunz z (ball_subset_closedBall hz)
  · intro z hz
    simp only [heq (ball_subset_closedBall hz), hquot hz]

end PathSelection.Preparation
end

end OAI


open MeromorphicOn
open Polynomial
open Set Filter Topology Metric
open scoped BigOperators

namespace Submission

open OAI.PathSelection.Preparation

/-- For an analytic function on the closed ball, with no zeros on the sphere, the contour power
sum `(2πi)⁻¹ ∮ deriv H / H` equals the sum of the positive part of the divisor. -/
lemma contourPowerSum_eq_divisor_sum {H : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hH : AnalyticOnNhd ℂ H (Metric.closedBall 0 R))
    (hnz : ∀ z ∈ Metric.sphere 0 R, H z ≠ 0) :
    contourPowerSum H R 0 =
      (∑ᶠ z, ((divisor H (Metric.closedBall 0 R))⁺) z : ℂ) := by
  classical
  let B : Set ℂ := Metric.closedBall 0 R
  let d : Function.locallyFinsuppWithin B ℤ := divisor H B
  have hd : (d : ℂ → ℤ).HasFiniteSupport := d.finiteSupport (isCompact_closedBall 0 R)
  have hdnonneg : ∀ z, 0 ≤ d z := by
    intro z
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hH z
  let s := hd.toFinset
  let P : ℂ[X] := ∏ a ∈ s, (X - C a) ^ (d a).toNat
  have hPmonic : P.Monic := by
    apply monic_prod_of_monic
    intro a ha
    exact (monic_X_sub_C a).pow _
  have hPeval : ∀ z, P.eval z = (∏ᶠ w : ℂ, (fun t : ℂ => t - w) ^ d w) z := by
    intro z
    rw [Function.FactorizedRational.finprod_eq_fun hd]
    dsimp only
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := s) ?_]
    · simp only [P, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
      apply Finset.prod_congr rfl
      intro a _
      conv_rhs => rw [← Int.toNat_of_nonneg (hdnonneg a), zpow_natCast]
    · intro a ha
      apply hd.mem_toFinset.mpr
      by_contra hn
      have : d a = 0 := by simpa using hn
      simp [Function.mem_mulSupport, this] at ha
  have hProot : ∀ z, P.eval z = 0 → z ∈ Function.support d := by
    intro z hz
    by_contra hn
    have hprod : P.eval z ≠ 0 := by
      simp only [P, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
      apply Finset.prod_ne_zero_iff.mpr
      intro a ha
      apply pow_ne_zero
      apply sub_ne_zero.mpr
      intro hza
      apply hn
      rw [hza]
      exact hd.mem_toFinset.mp ha
    exact hprod hz
  have hPdiv : divisor (fun z => P.eval z) B = d := by
    rw [show (fun z => P.eval z) = (∏ᶠ w, (fun t => t - w) ^ d w) from funext hPeval]
    exact Function.FactorizedRational.divisor (U := B) (D := d) hd
  have hPdeg : (P.natDegree : ℤ) = ∑ᶠ z, d z := by
    have h1 : P.natDegree = ∑ a ∈ s, (d a).toNat := by
      simp only [P]
      rw [Polynomial.natDegree_prod]
      · apply Finset.sum_congr rfl
        intro a ha
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
      · intro a ha
        exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a)
    rw [h1]
    simp only [Nat.cast_sum]
    have h2 : (∑ a ∈ s, (d a).toNat : ℤ) = ∑ a ∈ s, d a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Int.toNat_of_nonneg (hdnonneg a)
    rw [h2]
    symm
    apply finsum_eq_sum_of_support_subset
    intro a ha
    exact hd.mem_toFinset.mpr ha
  have hz0 : (R : ℂ) ∈ Metric.sphere 0 R := by simp [abs_of_pos hR]
  have hz0B : (R : ℂ) ∈ B := Metric.sphere_subset_closedBall hz0
  have horder : ∀ z ∈ B, meromorphicOrderAt H z ≠ ⊤ := by
    intro z hz
    apply hH.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (isConnected_closedBall hR.le).isPreconnected hz0B hz
    rw [(hH _ hz0B).meromorphicOrderAt_eq,
      (hH _ hz0B).analyticOrderAt_eq_zero.mpr (hnz _ hz0)]
    simp
  obtain ⟨u, hu, hunz, heq_codisc⟩ := hH.meromorphicOn.extract_zeros_poles (fun z => horder z z.property) hd
  have hunz' : ∀ z ∈ B, u z ≠ 0 := fun z hz => hunz ⟨z, hz⟩
  have heq : EqOn H (fun z => P.eval z * u z) B := by
    apply eqOn_closedBall_of_codiscrete hR hH.continuousOn
      (P.continuous.continuousOn.mul hu.continuousOn)
    filter_upwards [heq_codisc] with z hz
    change H z = P.eval z * u z
    rw [hPeval]
    simpa only [Pi.smul_apply', smul_eq_mul] using hz
  have hroot : ∀ z, P.eval z = 0 → z ∈ Metric.ball 0 R := by
    intro z hz
    have hs := hProot z hz
    have hzc := d.supportWithinDomain hs
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hzc) with hlt | he
    · exact mem_ball_zero_iff.mpr hlt
    · have hzsp : z ∈ Metric.sphere 0 R := mem_sphere_zero_iff_norm.mpr he
      have hd0 : d z = 0 := by
        dsimp [d]
        rw [hH.meromorphicOn.divisor_apply hzc, (hH z hzc).meromorphicOrderAt_eq,
          (hH z hzc).analyticOrderAt_eq_zero.mpr (hnz z hzsp)]
        simp
      exact False.elim (hs hd0)
  have hcount := preparation_zero_count hR hH hPmonic hroot hu hunz' heq
  have hpos : (∑ᶠ z, ((divisor H B)⁺) z : ℤ) = ∑ᶠ z, d z := by
    apply finsum_congr
    intro z
    exact max_eq_left (hdnonneg z)
  have hPdegC : (P.natDegree : ℂ) = ((∑ᶠ z, d z : ℤ) : ℂ) := by
    rw [← hPdeg]; norm_cast
  have hcast : (∑ᶠ z, (((divisor H B)⁺) z : ℂ)) =
      ((∑ᶠ z, ((divisor H B)⁺) z : ℤ) : ℂ) :=
    (map_finsum (Int.castRingHom ℂ)
      (((divisor H B)⁺).finiteSupport (isCompact_closedBall 0 R))).symm
  rw [hcount, hPdegC, ← hpos, hcast]

end Submission


open MeromorphicOn
open Polynomial
open Set Filter Topology Metric
open OAI.PathSelection.Preparation

namespace Submission

theorem rouche_zero_count_eq {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∑ᶠ z, ((divisor (f + g) (Metric.closedBall 0 R))⁺) z) =
      (∑ᶠ z, ((divisor f (Metric.closedBall 0 R))⁺) z) := by
  classical
  let B : Set ℂ := Metric.closedBall 0 R
  have hgN : AnalyticOnNhd ℂ g Set.univ := by simpa using hg
  have hfB : MeromorphicOn f B := fun z _ => hf.meromorphicOn z (mem_univ z)
  have hfgB : MeromorphicOn (f + g) B :=
    fun z _ => (hf.meromorphicOn.add hgN.meromorphicOn) z (mem_univ z)
  let D : Function.locallyFinsuppWithin B ℤ := divisor f B
  have hDfin : D.support.Finite := D.finiteSupport (isCompact_closedBall 0 R)
  let Dneg : Function.locallyFinsuppWithin B ℤ := D⁻
  have hDnegfin : Dneg.support.Finite := by
    apply hDfin.subset
    intro z hz
    by_contra h
    have hz0 : D z = 0 := by simpa [Function.mem_support, not_not] using h
    have : Dneg z = 0 := by simp [Dneg, hz0]
    exact hz (by simpa [Function.mem_support] using this)
  have hDnegnonneg : ∀ z, 0 ≤ Dneg z := by
    intro z
    simpa [Dneg] using negPart_nonneg (D z)
  obtain ⟨Q, hQmonic, hQeval, hQroot⟩ :=
    nonnegative_factor_polynomial (Dneg : ℂ → ℤ) hDnegfin hDnegnonneg
  have hQdiv : divisor (fun z => Q.eval z) B = Dneg := by
    rw [show (fun z => Q.eval z) = (∏ᶠ w, (fun t => t - w) ^ Dneg w) from funext hQeval]
    exact Function.FactorizedRational.divisor (U := B) (D := Dneg) hDnegfin
  have hQan : AnalyticOnNhd ℂ (fun z => Q.eval z) B :=
    (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) Q).mono (Set.subset_univ B)
  have hQ_nf : ∀ z ∈ B, meromorphicOrderAt (fun z => Q.eval z) z ≠ ⊤ := by
    intro z hz
    rw [show (fun z => Q.eval z) = (∏ᶠ w, (fun t => t - w) ^ Dneg w) from funext hQeval]
    exact Function.FactorizedRational.meromorphicOrderAt_ne_top (z := z) Dneg
  -- f has finite order on the ball (no pole on the sphere, connectedness)
  have hz0 : (R : ℂ) ∈ Metric.sphere 0 R := by simp [abs_of_pos hR]
  have hz0B : (R : ℂ) ∈ B := Metric.sphere_subset_closedBall hz0
  have hfz0 : f (R : ℂ) ≠ 0 := by
    intro h
    have := hbound (R : ℂ) (by simp [abs_of_pos hR])
    rw [h, norm_zero] at this
    exact not_lt_of_ge (norm_nonneg _) this
  have hfgz0 : f (R : ℂ) + g (R : ℂ) ≠ 0 := by
    have := hbound (R : ℂ) (by simp [abs_of_pos hR])
    intro h
    have hle : ‖f (R : ℂ)‖ ≤ ‖g (R : ℂ)‖ := by
      rw [eq_neg_of_add_eq_zero_left h, norm_neg]
    linarith
  have hf_an_z0 : AnalyticAt ℂ f (R : ℂ) := by
    have hnf0 : MeromorphicNFAt f (R : ℂ) := hf (mem_univ _)
    have hnot : ¬ meromorphicOrderAt f (R : ℂ) < 0 := by
      intro hneg
      have hzero : f (R : ℂ) = 0 := by
        rcases (meromorphicNFAt_iff_analyticAt_or.1 hnf0) with ha | ⟨_, _, hzero⟩
        · exact absurd hneg (not_lt.mpr ha.meromorphicOrderAt_nonneg)
        · exact hzero
      exact hfz0 hzero
    exact (hnf0.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_not_gt hnot))
  have hfg_an_z0 : AnalyticAt ℂ (fun z => f z + g z) (R : ℂ) :=
    hf_an_z0.add (hgN _ (mem_univ _))
  have hf_nf : ∀ z ∈ B, meromorphicOrderAt f z ≠ ⊤ := by
    intro z hz
    apply hfB.meromorphicOrderAt_ne_top_of_isPreconnected
      (isConnected_closedBall hR.le).isPreconnected hz0B hz
    rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (hf.meromorphicOn _ (mem_univ _))]
    exact (hf_an_z0.continuousAt.eventually_ne hfz0).filter_mono nhdsWithin_le_nhds
  have hfg_nf : ∀ z ∈ B, meromorphicOrderAt (f + g) z ≠ ⊤ := by
    intro z hz
    apply hfgB.meromorphicOrderAt_ne_top_of_isPreconnected
      (isConnected_closedBall hR.le).isPreconnected hz0B hz
    rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      ((hf.meromorphicOn.add hgN.meromorphicOn) _ (mem_univ _))]
    exact (hfg_an_z0.continuousAt.eventually_ne hfgz0).filter_mono nhdsWithin_le_nhds
  -- F = Q * f, in normal form
  let hfun : ℂ → ℂ := fun z => Q.eval z * f z
  let F : ℂ → ℂ := toMeromorphicNFOn hfun B
  have hh_mer : MeromorphicOn hfun B := hQan.meromorphicOn.mul hfB
  have hF_nf : MeromorphicNFOn F B := meromorphicNFOn_toMeromorphicNFOn hfun B
  have hF_div : divisor F B = D⁺ := by
    rw [MeromorphicOn.divisor_of_toMeromorphicNFOn hh_mer]
    change divisor ((fun z => Q.eval z) * f) B = D⁺
    rw [divisor_mul hQan.meromorphicOn hfB hQ_nf hf_nf]
    rw [hQdiv]
    ext z
    change (D z)⁻ + D z = (D z)⁺
    have := posPart_sub_negPart (D z)
    omega
  have hF_an : AnalyticOnNhd ℂ F B := by
    rw [← hF_nf.divisor_nonneg_iff_analyticOnNhd, hF_div]
    exact fun z => posPart_nonneg (D z)
  -- G = Q * (f + g), in normal form
  let gfun : ℂ → ℂ := fun z => Q.eval z * (f z + g z)
  let G : ℂ → ℂ := toMeromorphicNFOn gfun B
  have hg_mer : MeromorphicOn gfun B :=
    hQan.meromorphicOn.mul hfgB
  have hG_nf : MeromorphicNFOn G B := meromorphicNFOn_toMeromorphicNFOn gfun B
  let D' : Function.locallyFinsuppWithin B ℤ := divisor (f + g) B
  have hD'neg : D'⁻ = Dneg := by
    dsimp [D', Dneg, D]
    exact negPart_divisor_add_of_analyticNhdOn_right (U := B) hfB (hgN.mono (Set.subset_univ B))
  have hG_div : divisor G B = D'⁺ := by
    rw [MeromorphicOn.divisor_of_toMeromorphicNFOn hg_mer]
    change divisor ((fun z => Q.eval z) * (f + g)) B = D'⁺
    rw [divisor_mul hQan.meromorphicOn
      hfgB hQ_nf hfg_nf]
    rw [hQdiv]
    change Dneg + D' = D'⁺
    rw [← hD'neg]
    ext z
    change (D' z)⁻ + D' z = (D' z)⁺
    have := posPart_sub_negPart (D' z)
    omega
  have hG_an : AnalyticOnNhd ℂ G B := by
    rw [← hG_nf.divisor_nonneg_iff_analyticOnNhd, hG_div]
    exact fun z => posPart_nonneg (D' z)
  -- values on the sphere
  have hQ_ne : ∀ z ∈ Metric.sphere 0 R, Q.eval z ≠ 0 := by
    intro z hz hQ
    have hzsupp := hQroot z hQ
    have hDneg : Dneg z ≠ 0 := by simpa [Function.mem_support] using hzsupp
    have hzB : z ∈ B := Metric.sphere_subset_closedBall hz
    have hDz : D z = (meromorphicOrderAt f z).untop₀ := by
      change (divisor f B) z = (meromorphicOrderAt f z).untop₀
      rw [divisor_apply hfB hzB]
    have hneg : D z < 0 := by
      by_contra h
      push_neg at h
      have hzero : Dneg z = 0 := by
        simp [Dneg, negPart_eq_zero.mpr h]
      exact hDneg hzero
    have hord : meromorphicOrderAt f z < 0 := by
      rw [← WithTop.coe_untop₀_of_ne_top (hf_nf z hzB), ← hDz]
      exact_mod_cast hneg
    have hfz : f z = 0 := by
      have hnfz : MeromorphicNFAt f z := hf (mem_univ _)
      rcases (meromorphicNFAt_iff_analyticAt_or.1 hnfz) with ha | ⟨_, _, hzero⟩
      · exact absurd hord (not_lt.mpr ha.meromorphicOrderAt_nonneg)
      · exact hzero
    have := hbound z (mem_sphere_zero_iff_norm.mp hz)
    rw [hfz, norm_zero] at this
    exact not_lt_of_ge (norm_nonneg _) this
  have hf_ne : ∀ z ∈ Metric.sphere 0 R, f z ≠ 0 := by
    intro z hz h
    have := hbound z (mem_sphere_zero_iff_norm.mp hz)
    rw [h, norm_zero] at this
    exact not_lt_of_ge (norm_nonneg _) this
  have hF_val : ∀ z ∈ Metric.sphere 0 R, F z = Q.eval z * f z := by
    intro z hz
    have hzB : z ∈ B := Metric.sphere_subset_closedBall hz
    have hfz_an : AnalyticAt ℂ f z := by
      have hnfz : MeromorphicNFAt f z := hf (mem_univ _)
      have hnot : ¬ meromorphicOrderAt f z < 0 := by
        intro hneg
        have hzero : f z = 0 := by
          rcases (meromorphicNFAt_iff_analyticAt_or.1 hnfz) with ha | ⟨_, _, hzero⟩
          · exact absurd hneg (not_lt.mpr ha.meromorphicOrderAt_nonneg)
          · exact hzero
        exact hf_ne z hz hzero
      exact hnfz.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_not_gt hnot)
    have hh_nf : MeromorphicNFAt hfun z :=
      (hQan z hzB).mul hfz_an |>.meromorphicNFAt
    rw [show F = toMeromorphicNFOn hfun B from rfl,
      toMeromorphicNFOn_eq_toMeromorphicNFAt hh_mer hzB,
      toMeromorphicNFAt_eq_self.2 hh_nf]
  have hG_val : ∀ z ∈ Metric.sphere 0 R, G z = Q.eval z * (f z + g z) := by
    intro z hz
    have hzB : z ∈ B := Metric.sphere_subset_closedBall hz
    have hfz_an : AnalyticAt ℂ f z := by
      have hnfz : MeromorphicNFAt f z := hf (mem_univ _)
      have hnot : ¬ meromorphicOrderAt f z < 0 := by
        intro hneg
        have hzero : f z = 0 := by
          rcases (meromorphicNFAt_iff_analyticAt_or.1 hnfz) with ha | ⟨_, _, hzero⟩
          · exact absurd hneg (not_lt.mpr ha.meromorphicOrderAt_nonneg)
          · exact hzero
        exact hf_ne z hz hzero
      exact hnfz.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_not_gt hnot)
    have hfgz_an : AnalyticAt ℂ (fun z => f z + g z) z :=
      hfz_an.add (hgN _ (mem_univ _))
    have hh_nf : MeromorphicNFAt gfun z :=
      (hQan z hzB).mul hfgz_an |>.meromorphicNFAt
    rw [show G = toMeromorphicNFOn gfun B from rfl,
      toMeromorphicNFOn_eq_toMeromorphicNFAt hg_mer hzB,
      toMeromorphicNFAt_eq_self.2 hh_nf]
  have hF_ne : ∀ z ∈ Metric.sphere 0 R, F z ≠ 0 := by
    intro z hz
    rw [hF_val z hz]
    exact mul_ne_zero (hQ_ne z hz) (hf_ne z hz)
  have hG_ne : ∀ z ∈ Metric.sphere 0 R, G z ≠ 0 := by
    intro z hz
    rw [hG_val z hz]
    refine mul_ne_zero (hQ_ne z hz) ?_
    intro h
    have := hbound z (mem_sphere_zero_iff_norm.mp hz)
    have hle : ‖f z‖ ≤ ‖g z‖ := by
      rw [eq_neg_of_add_eq_zero_left h, norm_neg]
    linarith
  have hsmall : ∀ z ∈ Metric.sphere 0 R, ‖G z - F z‖ < ‖F z‖ := by
    intro z hz
    rw [hG_val z hz, hF_val z hz]
    have hQz : Q.eval z ≠ 0 := hQ_ne z hz
    have hsub : Q.eval z * (f z + g z) - Q.eval z * f z = Q.eval z * g z := by ring
    rw [hsub, norm_mul, norm_mul]
    exact mul_lt_mul_of_pos_left (hbound z (mem_sphere_zero_iff_norm.mp hz))
      (norm_pos_iff.mpr hQz)
  have hRouche := contour_zero_count_eq_of_norm_sub_lt hR hF_an hG_an hsmall
  have hFsum := contourPowerSum_eq_divisor_sum hR hF_an hF_ne
  have hGsum := contourPowerSum_eq_divisor_sum hR hG_an hG_ne
  have hFsumZ : contourPowerSum F R 0 =
      ((∑ᶠ z, ((divisor F B)⁺) z : ℤ) : ℂ) := by
    rw [hFsum]
    exact (map_finsum (Int.castRingHom ℂ)
      (((divisor F B)⁺).finiteSupport (isCompact_closedBall 0 R))).symm
  have hGsumZ : contourPowerSum G R 0 =
      ((∑ᶠ z, ((divisor G B)⁺) z : ℤ) : ℂ) := by
    rw [hGsum]
    exact (map_finsum (Int.castRingHom ℂ)
      (((divisor G B)⁺).finiteSupport (isCompact_closedBall 0 R))).symm
  have hsumC : ((∑ᶠ z, ((divisor F B)⁺) z : ℤ) : ℂ) =
      ((∑ᶠ z, ((divisor G B)⁺) z : ℤ) : ℂ) :=
    hFsumZ.symm.trans (hRouche.trans hGsumZ)
  have hsum : (∑ᶠ z, ((divisor F B)⁺) z : ℤ) =
      (∑ᶠ z, ((divisor G B)⁺) z : ℤ) := by
    exact_mod_cast hsumC
  rw [hF_div] at hsum
  rw [hG_div] at hsum
  have hppD : ∀ z, ((D z)⁺)⁺ = (D z)⁺ := fun z => max_eq_left (posPart_nonneg (D z))
  have hppD' : ∀ z, ((D' z)⁺)⁺ = (D' z)⁺ := fun z => max_eq_left (posPart_nonneg (D' z))
  have hsum' : (∑ᶠ z, (D⁺) z) = (∑ᶠ z, (D'⁺) z) := by
    simpa only [Function.locallyFinsuppWithin.posPart_apply, hppD, hppD'] using hsum
  have hposF : (∑ᶠ z, ((divisor f B)⁺) z) = ∑ᶠ z, (D⁺) z := rfl
  have hposG : (∑ᶠ z, ((divisor (f + g) B)⁺) z) = ∑ᶠ z, (D'⁺) z := rfl
  rw [hposF, hposG]
  exact hsum'.symm

end Submission