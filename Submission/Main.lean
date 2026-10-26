import Mathlib
import Submission.Helpers
import Submission.Rouche

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
