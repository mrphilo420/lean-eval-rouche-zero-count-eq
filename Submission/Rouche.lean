import Mathlib
import Submission.Corpus.ContourPreparation

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
