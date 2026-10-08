import A3.WishartCholeskyBlock

open Matrix
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {K : Type*} [RCLike K]

theorem isOpen_wishartCholeskyDomain : IsOpen (wishartCholeskyDomain n K) := by
  change IsOpen {x : HermitianCoordinates n K | ∀ i, 0 < x.1 i}
  have heq : {x : HermitianCoordinates n K | ∀ i, 0 < x.1 i} =
      ⋂ i : Fin n, {x | 0 < x.1 i} := by ext x; simp
  rw [heq]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (by fun_prop)

theorem contDiffAt_wishartCholeskyMatrix_entry (k : WithTop ℕ∞)
    (x : HermitianCoordinates n K) (hx : x ∈ wishartCholeskyDomain n K) (i j : Fin n) :
    ContDiffAt ℝ k (fun y : HermitianCoordinates n K ↦ wishartCholeskyMatrix y i j) x := by
  unfold wishartCholeskyMatrix
  split_ifs with hij hji
  · have hcoord : ContDiffAt ℝ k (fun x : HermitianCoordinates n K ↦ x.1 i) x := by fun_prop
    exact (RCLike.ofRealCLM : ℝ →L[ℝ] K).contDiff.contDiffAt.comp x (hcoord.sqrt (hx i).ne')
  · have hcoord : ContDiffAt ℝ k (fun x : HermitianCoordinates n K ↦ x.2 ⟨(j, i), hji⟩) x := by
      fun_prop
    simpa only [RCLike.conjCLE_apply, RCLike.star_def, Function.comp_def] using
      (RCLike.conjCLE : K ≃L[ℝ] K).contDiff.contDiffAt.comp x hcoord
  · fun_prop

theorem contDiffAt_wishartGramMatrix_entry (k : WithTop ℕ∞)
    (x : HermitianCoordinates n K) (hx : x ∈ wishartCholeskyDomain n K) (i j : Fin n) :
    ContDiffAt ℝ k (fun y : HermitianCoordinates n K ↦
      (wishartCholeskyMatrix y * (wishartCholeskyMatrix y).conjTranspose) i j) x := by
  have heq : (fun y : HermitianCoordinates n K ↦
      (wishartCholeskyMatrix y * (wishartCholeskyMatrix y).conjTranspose) i j) =
      (fun y ↦ ∑ a : Fin n, wishartCholeskyMatrix y i a * star (wishartCholeskyMatrix y j a)) := by
    funext y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [heq]
  apply ContDiffAt.sum
  intro a _
  have hs : ContDiffAt ℝ k (fun y : HermitianCoordinates n K ↦
      star (wishartCholeskyMatrix y j a)) x := by
    simpa only [RCLike.conjCLE_apply, RCLike.star_def, Function.comp_def] using
      (RCLike.conjCLE : K ≃L[ℝ] K).contDiff.contDiffAt.comp x
        (contDiffAt_wishartCholeskyMatrix_entry k x hx j a)
  exact (contDiffAt_wishartCholeskyMatrix_entry k x hx i a).mul hs

theorem contDiffAt_wishartGramCoordinates (k : WithTop ℕ∞) (x : HermitianCoordinates n K)
    (hx : x ∈ wishartCholeskyDomain n K) :
    ContDiffAt ℝ k wishartGramCoordinates x := by
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro i
    exact (RCLike.reCLM : K →L[ℝ] ℝ).contDiff.contDiffAt.comp x
      (contDiffAt_wishartGramMatrix_entry k x hx i i)
  · apply contDiffAt_pi.mpr
    intro ij
    exact contDiffAt_wishartGramMatrix_entry k x hx ij.1.1 ij.1.2

theorem contDiff_wishartRankOneCoordinates (k : WithTop ℕ∞) :
    ContDiff ℝ k (wishartRankOneCoordinates : (Fin n → K) → HermitianCoordinates n K) := by
  have hc (i : Fin n) : ContDiff ℝ k (fun z : Fin n → K ↦ z i) := by fun_prop
  have hs (i : Fin n) : ContDiff ℝ k (fun z : Fin n → K ↦ star (z i)) := by
    simpa only [RCLike.conjCLE_apply, RCLike.star_def, Function.comp_def] using
      (RCLike.conjCLE : K ≃L[ℝ] K).contDiff.comp (hc i)
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    exact (RCLike.reCLM : K →L[ℝ] ℝ).contDiff.comp ((hs i).mul (hc i))
  · apply contDiff_pi.mpr
    intro ij
    exact (hs ij.1.1).mul (hc ij.1.2)

end A3Research
