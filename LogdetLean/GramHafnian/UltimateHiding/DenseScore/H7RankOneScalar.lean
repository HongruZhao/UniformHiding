import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7ScalarBell
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCOEExternal
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

open Function
open scoped Topology
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.UltimateHiding.Dense

/-!
# Exact rank-one scalar likelihood through order four

This module differentiates the literal determinant-lemma bracket and the
literal `q^(-d) B^p` rank-one likelihood through order four.  The public
endpoints identify its third and fourth derivatives with the existing
concrete rank-one density scores.  It uses no external density or H7
declaration.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

set_option maxHeartbeats 1200000

private def q (t : ℝ) : ℝ := Real.exp (2 * t)
private def s (t : ℝ) : ℝ := q t - 1

private theorem hasDerivAt_q (t : ℝ) :
    HasDerivAt q (2 * Real.exp (2 * t)) t := by
  change HasDerivAt (fun y : ℝ => Real.exp (2 * y))
    (2 * Real.exp (2 * t)) t
  convert (hasDerivAt_const_mul (x := t) (2 : ℝ)).exp using 1 <;> ring

private theorem deriv_q : deriv q = fun t => 2 * Real.exp (2 * t) := by
  funext t
  exact (hasDerivAt_q t).deriv

private theorem deriv_two_mul_exp :
    deriv (fun t : ℝ => 2 * Real.exp (2 * t)) =
      fun t => 4 * Real.exp (2 * t) := by
  funext t
  have h := ((hasDerivAt_q t).const_mul 2).deriv
  calc
    deriv (fun y : ℝ => 2 * Real.exp (2 * y)) t =
        2 * (2 * Real.exp (2 * t)) := by simpa only [q] using h
    _ = 4 * Real.exp (2 * t) := by ring

private theorem deriv_four_mul_exp :
    deriv (fun t : ℝ => 4 * Real.exp (2 * t)) =
      fun t => 8 * Real.exp (2 * t) := by
  funext t
  have h := ((hasDerivAt_q t).const_mul 4).deriv
  calc
    deriv (fun y : ℝ => 4 * Real.exp (2 * y)) t =
        4 * (2 * Real.exp (2 * t)) := by simpa only [q] using h
    _ = 8 * Real.exp (2 * t) := by ring

private theorem q_jet_one : iteratedDeriv 1 q 0 = 2 := by
  rw [iteratedDeriv_eq_iterate]
  change deriv q 0 = 2
  rw [deriv_q]
  norm_num

private theorem q_jet_two : iteratedDeriv 2 q 0 = 4 := by
  rw [iteratedDeriv_eq_iterate]
  change deriv (deriv q) 0 = 4
  rw [deriv_q, deriv_two_mul_exp]
  norm_num

private theorem q_jet_three : iteratedDeriv 3 q 0 = 8 := by
  rw [iteratedDeriv_eq_iterate]
  change deriv (deriv (deriv q)) 0 = 8
  rw [deriv_q, deriv_two_mul_exp, deriv_four_mul_exp]
  norm_num

private theorem deriv_s : deriv s = fun t => 2 * Real.exp (2 * t) := by
  funext t
  have h : HasDerivAt s (2 * Real.exp (2 * t)) t := by
    change HasDerivAt (fun y => q y - 1) (2 * Real.exp (2 * t)) t
    exact (hasDerivAt_q t).sub_const 1
  exact h.deriv

private theorem s_zero : s 0 = 0 := by simp [s, q]

private theorem s_jet_one : iteratedDeriv 1 s 0 = 2 := by
  rw [iteratedDeriv_eq_iterate]
  change deriv s 0 = 2
  rw [deriv_s]
  norm_num

private theorem s_jet_two : iteratedDeriv 2 s 0 = 4 := by
  rw [iteratedDeriv_eq_iterate]
  change deriv (deriv s) 0 = 4
  rw [deriv_s, deriv_two_mul_exp]
  norm_num

private theorem s_jet_three : iteratedDeriv 3 s 0 = 8 := by
  rw [iteratedDeriv_eq_iterate]
  change deriv (deriv (deriv s)) 0 = 8
  rw [deriv_s, deriv_two_mul_exp, deriv_four_mul_exp]
  norm_num

private def R (u a z : ℝ) : ℝ := 1 + 2 * u * z + a * z ^ 2

private theorem hasDerivAt_R (u a z : ℝ) :
    HasDerivAt (R u a) (2 * u + 2 * a * z) z := by
  have h := ((hasDerivAt_const z 1).add
      ((hasDerivAt_id z).const_mul (2 * u))).add
        (((hasDerivAt_id z).pow 2).const_mul a)
  refine (h.congr_deriv (by simp [id] <;> ring)).congr_of_eventuallyEq ?_
  filter_upwards with y
  simp [R, id] <;> ring

private theorem deriv_R (u a : ℝ) :
    deriv (R u a) = fun z => 2 * u + 2 * a * z := by
  funext z
  exact (hasDerivAt_R u a z).deriv

private theorem deriv_R_one (u a : ℝ) :
    deriv (fun z : ℝ => 2 * u + 2 * a * z) = fun _ => 2 * a := by
  funext z
  simpa using
    ((hasDerivAt_const z (2 * u)).add
      ((hasDerivAt_id z).const_mul (2 * a))).deriv

private theorem deriv_R_two (a : ℝ) :
    deriv (fun _ : ℝ => 2 * a) = fun _ => 0 := by
  funext z
  exact (hasDerivAt_const z (2 * a)).deriv

private theorem R_zero (u a : ℝ) : R u a 0 = 1 := by simp [R]

private theorem R_jet_one (u a : ℝ) :
    iteratedDeriv 1 (R u a) 0 = 2 * u := by
  rw [iteratedDeriv_eq_iterate]
  change deriv (R u a) 0 = 2 * u
  rw [deriv_R]
  ring

private theorem R_jet_two (u a : ℝ) :
    iteratedDeriv 2 (R u a) 0 = 2 * a := by
  rw [iteratedDeriv_eq_iterate]
  change deriv (deriv (R u a)) 0 = 2 * a
  rw [deriv_R, deriv_R_one]

private theorem R_jet_three (u a : ℝ) :
    iteratedDeriv 3 (R u a) 0 = 0 := by
  rw [iteratedDeriv_eq_iterate]
  change deriv (deriv (deriv (R u a))) 0 = 0
  rw [deriv_R, deriv_R_one, deriv_R_two]

private def B (u w t : ℝ) : ℝ := R u (u ^ 2 - w) (s t)

private theorem B_zero (u w : ℝ) : B u w 0 = 1 := by
  simp [B, R, s_zero]

private theorem B_contDiffAt_three (u w : ℝ) :
    ContDiffAt ℝ 3 (B u w) 0 := by
  unfold B R s q
  fun_prop

private theorem B_contDiffAt_four (u w : ℝ) :
    ContDiffAt ℝ 4 (B u w) 0 := by
  unfold B R s q
  fun_prop

private theorem B_jet_one (u w : ℝ) :
    iteratedDeriv 1 (B u w) 0 = 4 * u := by
  rw [iteratedDeriv_eq_iterate]
  change deriv (B u w) 0 = 4 * u
  have hs : HasDerivAt s 2 0 := by
    change HasDerivAt (fun y => q y - 1) 2 0
    simpa using (hasDerivAt_q 0).sub_const 1
  have hR : HasDerivAt (R u (u ^ 2 - w)) (2 * u) 0 := by
    simpa using hasDerivAt_R u (u ^ 2 - w) 0
  have hR' : HasDerivAt (R u (u ^ 2 - w)) (2 * u) (s 0) := by
    simpa only [s_zero] using hR
  change deriv (R u (u ^ 2 - w) ∘ s) 0 = 4 * u
  calc
    deriv (R u (u ^ 2 - w) ∘ s) 0 = (2 * u) * 2 :=
      (hR'.comp 0 hs).deriv
    _ = 4 * u := by ring

private theorem B_jet_two (u w : ℝ) :
    iteratedDeriv 2 (B u w) 0 = 8 * u + 8 * (u ^ 2 - w) := by
  rw [show B u w = R u (u ^ 2 - w) ∘ s by rfl,
    iteratedDeriv_comp_two]
  · rw [s_zero, deriv_s, s_jet_two, deriv_R, R_jet_two]
    norm_num
    ring
  · simpa [s_zero] using
      (show ContDiffAt ℝ 2 (R u (u ^ 2 - w)) 0 by
        unfold R
        fun_prop)
  · exact (show ContDiffAt ℝ 2 s 0 by
      unfold s q
      fun_prop)

private theorem B_jet_three (u w : ℝ) :
    iteratedDeriv 3 (B u w) 0 = 16 * u + 48 * (u ^ 2 - w) := by
  rw [show B u w = R u (u ^ 2 - w) ∘ s by rfl,
    iteratedDeriv_comp_three]
  · rw [s_zero, deriv_s, s_jet_two, s_jet_three,
      deriv_R, R_jet_two, R_jet_three]
    norm_num
    ring
  · simpa [s_zero] using
      (show ContDiffAt ℝ 3 (R u (u ^ 2 - w)) 0 by
        unfold R
        fun_prop)
  · exact (show ContDiffAt ℝ 3 s 0 by
      unfold s q
      fun_prop)

private theorem B_eq_expansion (u w : ℝ) :
    B u w = fun t ↦
      (1 - 2 * u + (u ^ 2 - w)) +
        ((2 * u - 2 * (u ^ 2 - w)) * Real.exp (2 * t) +
          (u ^ 2 - w) * Real.exp (4 * t)) := by
  funext t
  have hexp : Real.exp (4 * t) = Real.exp (2 * t) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [hexp]
  simp only [B, R, s, q]
  ring

private theorem B_jet_four (u w : ℝ) :
    iteratedDeriv 4 (B u w) 0 = 32 * u + 224 * (u ^ 2 - w) := by
  rw [B_eq_expansion]
  rw [iteratedDeriv_const_add
    (f := fun t : ℝ ↦
      (2 * u - 2 * (u ^ 2 - w)) * Real.exp (2 * t) +
        (u ^ 2 - w) * Real.exp (4 * t))
    (x := (0 : ℝ)) (n := 4) (by norm_num)]
  have hfun :
      (fun t : ℝ ↦ (2 * u - 2 * (u ^ 2 - w)) * Real.exp (2 * t) +
        (u ^ 2 - w) * Real.exp (4 * t)) =
      (fun t : ℝ ↦ (2 * u - 2 * (u ^ 2 - w)) * Real.exp (2 * t)) +
        (fun t : ℝ ↦ (u ^ 2 - w) * Real.exp (4 * t)) := by
    funext t
    simp only [Pi.add_apply]
  rw [hfun, iteratedDeriv_add (by fun_prop) (by fun_prop)]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  rw [congrFun (iteratedDeriv_exp_const_mul 4 2) 0,
    congrFun (iteratedDeriv_exp_const_mul 4 4) 0]
  norm_num
  ring

private def logB (u w t : ℝ) : ℝ := Real.log (B u w t)

private theorem real_log_jet_one :
    iteratedDeriv 1 Real.log 1 = 1 := by
  rw [iteratedDeriv_eq_iterate]
  change deriv Real.log 1 = 1
  rw [Real.deriv_log]
  norm_num

private theorem real_log_jet_two :
    iteratedDeriv 2 Real.log 1 = -1 := by
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ',
    Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]
  norm_num

private theorem real_log_jet_three :
    iteratedDeriv 3 Real.log 1 = 2 := by
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ',
    Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]
  norm_num

private theorem logB_contDiffAt_three (u w : ℝ) :
    ContDiffAt ℝ 3 (logB u w) 0 := by
  unfold logB
  apply ContDiffAt.log (B_contDiffAt_three u w)
  simp only [B_zero]
  norm_num

private theorem logB_contDiffAt_four (u w : ℝ) :
    ContDiffAt ℝ 4 (logB u w) 0 := by
  unfold logB
  apply ContDiffAt.log (B_contDiffAt_four u w)
  simp only [B_zero]
  norm_num

private theorem B_deriv_zero (u w : ℝ) :
    deriv (B u w) 0 = 4 * u := by
  simpa only [iteratedDeriv_eq_iterate, iterate_one] using B_jet_one u w

private theorem logB_jet_one (u w : ℝ) :
    iteratedDeriv 1 (logB u w) 0 = 4 * u := by
  rw [iteratedDeriv_eq_iterate]
  change deriv (logB u w) 0 = 4 * u
  have hB : HasDerivAt (B u w) (4 * u) 0 := by
    exact ((B_contDiffAt_three u w).differentiableAt (by norm_num)).hasDerivAt.congr_deriv
      (B_deriv_zero u w)
  have hlog : HasDerivAt Real.log 1 (B u w 0) := by
    rw [B_zero]
    convert Real.hasDerivAt_log (one_ne_zero : (1 : ℝ) ≠ 0) using 1 <;>
      norm_num
  change deriv (Real.log ∘ B u w) 0 = 4 * u
  simpa using (hlog.comp 0 hB).deriv

private theorem logB_jet_two (u w : ℝ) :
    iteratedDeriv 2 (logB u w) 0 = 8 * (u - u ^ 2 - w) := by
  rw [show logB u w = Real.log ∘ B u w by rfl,
    iteratedDeriv_comp_two]
  · rw [B_zero, real_log_jet_two, B_deriv_zero,
      Real.deriv_log, B_jet_two]
    norm_num
    ring
  · have h : ContDiffAt ℝ 2 Real.log (1 : ℝ) :=
      Real.contDiffAt_log.2 (one_ne_zero : (1 : ℝ) ≠ 0)
    simpa only [B_zero] using h
  · exact (B_contDiffAt_three u w).of_le (by norm_num)

private theorem logB_jet_three (u w : ℝ) :
    iteratedDeriv 3 (logB u w) 0 =
      16 * (2 * u ^ 3 - 3 * u ^ 2 + u + (6 * u - 3) * w) := by
  rw [show logB u w = Real.log ∘ B u w by rfl,
    iteratedDeriv_comp_three]
  · rw [B_zero, real_log_jet_two, real_log_jet_three,
      B_deriv_zero, Real.deriv_log, B_jet_two, B_jet_three]
    norm_num
    ring
  · have h : ContDiffAt ℝ 3 Real.log (1 : ℝ) :=
      Real.contDiffAt_log.2 (one_ne_zero : (1 : ℝ) ≠ 0)
    simpa only [B_zero] using h
  · exact B_contDiffAt_three u w

private theorem logB_jet_four (u w : ℝ) :
    iteratedDeriv 4 (logB u w) 0 =
      -32 *
        ((u - 1) + 7 * (u - 1) ^ 2 + 12 * (u - 1) ^ 3 +
          6 * (u - 1) ^ 4 +
          (7 + 36 * (u - 1) + 36 * (u - 1) ^ 2) * w +
          6 * w ^ 2) := by
  have hbell := iteratedDeriv_four_eq_densityBell_log_of_contDiffAt_one
    (B u w) (B_contDiffAt_four u w) (B_zero u w)
  change iteratedDeriv 4 (B u w) 0 =
    densityBellFour
      (iteratedDeriv 1 (logB u w) 0)
      (iteratedDeriv 2 (logB u w) 0)
      (iteratedDeriv 3 (logB u w) 0)
      (iteratedDeriv 4 (logB u w) 0) at hbell
  rw [B_jet_four, logB_jet_one, logB_jet_two, logB_jet_three] at hbell
  unfold densityBellFour at hbell
  nlinarith

private def rankScalarCore (d p u w t : ℝ) : ℝ :=
  (q t) ^ (-d) * (B u w t) ^ p

private def rankLogModel (d p u w t : ℝ) : ℝ :=
  (-2 * d) * t + p * logB u w t

private theorem rankScalarCore_zero (d p u w : ℝ) :
    rankScalarCore d p u w 0 = 1 := by
  simp [rankScalarCore, q, B_zero]

private theorem rankScalarCore_contDiffAt_three (d p u w : ℝ) :
    ContDiffAt ℝ 3 (rankScalarCore d p u w) 0 := by
  unfold rankScalarCore
  apply ContDiffAt.mul
  · apply ContDiffAt.rpow_const_of_ne
    · unfold q
      fun_prop
    · simp [q]
  · apply ContDiffAt.rpow_const_of_ne
    · exact B_contDiffAt_three u w
    · simp only [B_zero]
      norm_num

private theorem rankScalarCore_contDiffAt_four (d p u w : ℝ) :
    ContDiffAt ℝ 4 (rankScalarCore d p u w) 0 := by
  unfold rankScalarCore
  apply ContDiffAt.mul
  · apply ContDiffAt.rpow_const_of_ne
    · unfold q
      fun_prop
    · simp [q]
  · apply ContDiffAt.rpow_const_of_ne
    · exact B_contDiffAt_four u w
    · simp only [B_zero]
      norm_num

private theorem log_rankScalarCore_eventuallyEq_rankLogModel
    (d p u w : ℝ) :
    (fun t => Real.log (rankScalarCore d p u w t)) =ᶠ[nhds 0]
      rankLogModel d p u w := by
  have hBpos : ∀ᶠ t in nhds 0, 0 < B u w t :=
    continuousAt_const.eventually_lt
      (B_contDiffAt_three u w).continuousAt (by rw [B_zero]; norm_num)
  filter_upwards [hBpos] with t hBt
  have hqt : 0 < q t := by
    unfold q
    exact Real.exp_pos _
  change Real.log ((q t) ^ (-d) * (B u w t) ^ p) = rankLogModel d p u w t
  rw [Real.log_mul
      (ne_of_gt (Real.rpow_pos_of_pos hqt (-d)))
      (ne_of_gt (Real.rpow_pos_of_pos hBt p)),
    Real.log_rpow hqt, Real.log_rpow hBt]
  simp only [rankLogModel, logB, q, Real.log_exp]
  ring

private theorem rankLogModel_contDiffAt_three (d p u w : ℝ) :
    ContDiffAt ℝ 3 (rankLogModel d p u w) 0 := by
  unfold rankLogModel
  exact (by fun_prop : ContDiffAt ℝ 3 (fun t : ℝ => -2 * d * t) 0).add
    ((logB_contDiffAt_three u w).const_smul p)

private theorem rankLogModel_contDiffAt_four (d p u w : ℝ) :
    ContDiffAt ℝ 4 (rankLogModel d p u w) 0 := by
  unfold rankLogModel
  exact (by fun_prop : ContDiffAt ℝ 4 (fun t : ℝ => -2 * d * t) 0).add
    ((logB_contDiffAt_four u w).const_smul p)

private theorem linear_jet_one (c : ℝ) :
    iteratedDeriv 1 (fun t : ℝ => c * t) 0 = c := by
  simpa [iteratedDeriv_id] using
    (iteratedDeriv_const_mul_field (x := (0 : ℝ)) (n := 1) c (id : ℝ → ℝ))

private theorem linear_jet_two (c : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => c * t) 0 = 0 := by
  simpa [iteratedDeriv_id] using
    (iteratedDeriv_const_mul_field (x := (0 : ℝ)) (n := 2) c (id : ℝ → ℝ))

private theorem linear_jet_three (c : ℝ) :
    iteratedDeriv 3 (fun t : ℝ => c * t) 0 = 0 := by
  simpa [iteratedDeriv_id] using
    (iteratedDeriv_const_mul_field (x := (0 : ℝ)) (n := 3) c (id : ℝ → ℝ))

private theorem linear_jet_four (c : ℝ) :
    iteratedDeriv 4 (fun t : ℝ => c * t) 0 = 0 := by
  simpa [iteratedDeriv_id] using
    (iteratedDeriv_const_mul_field (x := (0 : ℝ)) (n := 4) c (id : ℝ → ℝ))

private theorem rankLogModel_jet_one (d p u w : ℝ) :
    iteratedDeriv 1 (rankLogModel d p u w) 0 =
      -2 * d + 4 * p * u := by
  rw [show rankLogModel d p u w =
      (fun t : ℝ => (-2 * d) * t) + (fun t => p * logB u w t) by rfl]
  rw [iteratedDeriv_add (by fun_prop)
    (by simpa only [smul_eq_mul] using
      (logB_contDiffAt_three u w).of_le (by norm_num) |>.const_smul p)]
  rw [linear_jet_one, iteratedDeriv_const_mul_field, logB_jet_one]
  ring

private theorem rankLogModel_jet_two (d p u w : ℝ) :
    iteratedDeriv 2 (rankLogModel d p u w) 0 =
      8 * p * (u - u ^ 2 - w) := by
  rw [show rankLogModel d p u w =
      (fun t : ℝ => (-2 * d) * t) + (fun t => p * logB u w t) by rfl]
  rw [iteratedDeriv_add (by fun_prop)
    (by simpa only [smul_eq_mul] using
      (logB_contDiffAt_three u w).of_le (by norm_num) |>.const_smul p)]
  rw [linear_jet_two, iteratedDeriv_const_mul_field, logB_jet_two]
  ring

private theorem rankLogModel_jet_three (d p u w : ℝ) :
    iteratedDeriv 3 (rankLogModel d p u w) 0 =
      16 * p * (2 * u ^ 3 - 3 * u ^ 2 + u + (6 * u - 3) * w) := by
  rw [show rankLogModel d p u w =
      (fun t : ℝ => (-2 * d) * t) + (fun t => p * logB u w t) by rfl]
  rw [iteratedDeriv_add (by fun_prop)
    (by simpa only [smul_eq_mul] using
      (logB_contDiffAt_three u w).of_le (by norm_num) |>.const_smul p)]
  rw [linear_jet_three, iteratedDeriv_const_mul_field, logB_jet_three]
  ring

private theorem rankLogModel_jet_four (d p u w : ℝ) :
    iteratedDeriv 4 (rankLogModel d p u w) 0 =
      -32 * p *
        ((u - 1) + 7 * (u - 1) ^ 2 + 12 * (u - 1) ^ 3 +
          6 * (u - 1) ^ 4 +
          (7 + 36 * (u - 1) + 36 * (u - 1) ^ 2) * w +
          6 * w ^ 2) := by
  rw [show rankLogModel d p u w =
      (fun t : ℝ => (-2 * d) * t) + (fun t => p * logB u w t) by rfl]
  rw [iteratedDeriv_add (by fun_prop)
    (by simpa only [smul_eq_mul] using
      (logB_contDiffAt_four u w).of_le (by norm_num) |>.const_smul p)]
  rw [linear_jet_four, iteratedDeriv_const_mul_field, logB_jet_four]
  ring

private theorem rankScalarCore_log_jet_one (d p u w : ℝ) :
    iteratedDeriv 1 (fun t => Real.log (rankScalarCore d p u w t)) 0 =
      -2 * d + 4 * p * u := by
  rw [(log_rankScalarCore_eventuallyEq_rankLogModel d p u w).iteratedDeriv_eq 1]
  exact rankLogModel_jet_one d p u w

private theorem rankScalarCore_log_jet_two (d p u w : ℝ) :
    iteratedDeriv 2 (fun t => Real.log (rankScalarCore d p u w t)) 0 =
      8 * p * (u - u ^ 2 - w) := by
  rw [(log_rankScalarCore_eventuallyEq_rankLogModel d p u w).iteratedDeriv_eq 2]
  exact rankLogModel_jet_two d p u w

private theorem rankScalarCore_log_jet_three (d p u w : ℝ) :
    iteratedDeriv 3 (fun t => Real.log (rankScalarCore d p u w t)) 0 =
      16 * p * (2 * u ^ 3 - 3 * u ^ 2 + u + (6 * u - 3) * w) := by
  rw [(log_rankScalarCore_eventuallyEq_rankLogModel d p u w).iteratedDeriv_eq 3]
  exact rankLogModel_jet_three d p u w

private theorem rankScalarCore_log_jet_four (d p u w : ℝ) :
    iteratedDeriv 4 (fun t => Real.log (rankScalarCore d p u w t)) 0 =
      -32 * p *
        ((u - 1) + 7 * (u - 1) ^ 2 + 12 * (u - 1) ^ 3 +
          6 * (u - 1) ^ 4 +
          (7 + 36 * (u - 1) + 36 * (u - 1) ^ 2) * w +
          6 * w ^ 2) := by
  rw [(log_rankScalarCore_eventuallyEq_rankLogModel d p u w).iteratedDeriv_eq 4]
  exact rankLogModel_jet_four d p u w

private theorem rankScalarCore_jet_three (d p u w : ℝ) :
    iteratedDeriv 3 (rankScalarCore d p u w) 0 =
      densityBellThree
        (-2 * d + 4 * p * u)
        (8 * p * (u - u ^ 2 - w))
        (16 * p * (2 * u ^ 3 - 3 * u ^ 2 + u + (6 * u - 3) * w)) := by
  rw [iteratedDeriv_three_eq_densityBell_log_of_contDiffAt_one
    (rankScalarCore d p u w) (rankScalarCore_contDiffAt_three d p u w)
    (rankScalarCore_zero d p u w),
    rankScalarCore_log_jet_one, rankScalarCore_log_jet_two,
    rankScalarCore_log_jet_three]

private theorem rankScalarCore_jet_four (d p u w : ℝ) :
    iteratedDeriv 4 (rankScalarCore d p u w) 0 =
      densityBellFour
        (-2 * d + 4 * p * u)
        (8 * p * (u - u ^ 2 - w))
        (16 * p * (2 * u ^ 3 - 3 * u ^ 2 + u + (6 * u - 3) * w))
        (-32 * p *
          ((u - 1) + 7 * (u - 1) ^ 2 + 12 * (u - 1) ^ 3 +
            6 * (u - 1) ^ 4 +
            (7 + 36 * (u - 1) + 36 * (u - 1) ^ 2) * w +
            6 * w ^ 2)) := by
  rw [iteratedDeriv_four_eq_densityBell_log_of_contDiffAt_one
    (rankScalarCore d p u w) (rankScalarCore_contDiffAt_four d p u w)
    (rankScalarCore_zero d p u w),
    rankScalarCore_log_jet_one, rankScalarCore_log_jet_two,
    rankScalarCore_log_jet_three, rankScalarCore_log_jet_four]

private theorem concreteRankOneLikelihoodBracket_eq_B
    {N K : ℕ} (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) (t : ℝ) :
    concreteRankOneLikelihoodBracket K v t A =
      B (1 + concreteCOEX v K A) (concreteCOEW v K A) t := by
  unfold concreteRankOneLikelihoodBracket B R s q
  ring

private theorem concreteRankOneLikelihoodCore_eq_rankScalarCore
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    (fun t : ℝ => concreteRankOneLikelihoodCore K v t A) =
      rankScalarCore ((K : ℝ) - (N : ℝ)) (coeCornerDensityExponent N K)
        (1 + concreteCOEX v K A) (concreteCOEW v K A) := by
  funext t
  unfold concreteRankOneLikelihoodCore rankScalarCore
  rw [concreteRankOneLikelihoodBracket_eq_B]
  rfl

private theorem rankScalar_log_one_eq_project_score
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    -2 * ((K : ℝ) - (N : ℝ)) +
        4 * coeCornerDensityExponent N K * (1 + concreteCOEX v K A) =
      concreteRankOneLogScoreOne N K v A := by
  unfold concreteRankOneLogScoreOne coeRankOneLogScoreOne
  unfold coeCornerDensityExponent concreteCOEExponent
  ring

private theorem rankScalar_log_two_eq_project_score
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    8 * coeCornerDensityExponent N K *
        ((1 + concreteCOEX v K A) - (1 + concreteCOEX v K A) ^ 2 -
          concreteCOEW v K A) =
      concreteRankOneLogScoreTwo N K v A := by
  unfold concreteRankOneLogScoreTwo coeRankOneLogScoreTwo
  unfold coeCornerDensityExponent concreteCOEExponent
  ring

private theorem rankScalar_log_three_eq_project_score
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    16 * coeCornerDensityExponent N K *
        (2 * (1 + concreteCOEX v K A) ^ 3 -
          3 * (1 + concreteCOEX v K A) ^ 2 +
          (1 + concreteCOEX v K A) +
          (6 * (1 + concreteCOEX v K A) - 3) * concreteCOEW v K A) =
      concreteRankOneLogScoreThree N K v A := by
  unfold concreteRankOneLogScoreThree coeRankOneLogScoreThree
  unfold coeCornerDensityExponent concreteCOEExponent
  ring

private theorem rankScalar_log_four_eq_project_score
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    -32 * coeCornerDensityExponent N K *
        (concreteCOEX v K A + 7 * concreteCOEX v K A ^ 2 +
          12 * concreteCOEX v K A ^ 3 + 6 * concreteCOEX v K A ^ 4 +
          (7 + 36 * concreteCOEX v K A +
            36 * concreteCOEX v K A ^ 2) * concreteCOEW v K A +
          6 * concreteCOEW v K A ^ 2) =
      concreteRankOneLogScoreFour N K v A := by
  unfold concreteRankOneLogScoreFour coeRankOneLogScoreFour
  unfold coeCornerDensityExponent concreteCOEExponent
  ring

/-- The literal rank-one likelihood has the declared fourth logarithmic
score.  This is the checked order-four extension of the scalar H7 line. -/
theorem concreteRankOneLikelihoodCore_log_iteratedDeriv_four_eq_score
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    iteratedDeriv 4
        (fun t : ℝ ↦ Real.log (concreteRankOneLikelihoodCore K v t A)) 0 =
      concreteRankOneLogScoreFour N K v A := by
  rw [show (fun t : ℝ ↦ Real.log (concreteRankOneLikelihoodCore K v t A)) =
      (fun t : ℝ ↦ Real.log
        (rankScalarCore ((K : ℝ) - (N : ℝ))
          (coeCornerDensityExponent N K)
          (1 + concreteCOEX v K A) (concreteCOEW v K A) t)) by
      funext t
      rw [congrFun (concreteRankOneLikelihoodCore_eq_rankScalarCore v A) t],
    rankScalarCore_log_jet_four]
  convert rankScalar_log_four_eq_project_score v A using 1 <;> ring

theorem concreteRankOneLikelihoodCore_iteratedDeriv_three_eq_score
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    iteratedDeriv 3 (fun t : ℝ => concreteRankOneLikelihoodCore K v t A) 0 =
      concreteRankOneDensityScoreThree N K v A := by
  rw [concreteRankOneLikelihoodCore_eq_rankScalarCore,
    rankScalarCore_jet_three]
  unfold concreteRankOneDensityScoreThree
  rw [rankScalar_log_one_eq_project_score,
    rankScalar_log_two_eq_project_score,
    rankScalar_log_three_eq_project_score]

/-- The literal rank-one likelihood has the declared fourth density score. -/
theorem concreteRankOneLikelihoodCore_iteratedDeriv_four_eq_score
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    iteratedDeriv 4 (fun t : ℝ => concreteRankOneLikelihoodCore K v t A) 0 =
      concreteRankOneDensityScoreFour N K v A := by
  rw [concreteRankOneLikelihoodCore_eq_rankScalarCore,
    rankScalarCore_jet_four]
  unfold concreteRankOneDensityScoreFour
  rw [rankScalar_log_one_eq_project_score,
    rankScalar_log_two_eq_project_score,
    rankScalar_log_three_eq_project_score]
  congr 1
  convert rankScalar_log_four_eq_project_score v A using 1 <;> ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
