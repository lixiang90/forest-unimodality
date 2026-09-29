import ForestUnimodality.SignedGaussianLayerBudget
import ForestUnimodality.SignedGaussianGlobal

/-! The true signed-Gaussian profile and its nonquadratic deficit. A finite
list prices the whole continuous lower-y interval by proved antitonicity. -/
namespace ForestUnimodality.SignedGaussianSlices
open Finset Set SignedGaussianProfile SignedGaussianHermite NegativePowerLayerBudget

noncomputable def envelope (c K y w : ℝ) : ℝ := quadratic c K y-(c/2)*w^2

theorem lower_with_gap {c K y : ℝ} (hc : 0<c) (hy : 0<y) (w : ℝ) :
    envelope c K y w-positiveGap c K y≤SignedGaussianLayerBudget.kernel y w := by
  have h1:=profile_lower hc hy (show 0≤w^2/(2*y) by positivity)
  have he : SignedGaussianMinimum.objective c y (w^2/(2*y))=
      SignedGaussianLayerBudget.kernel y w+(c/2)*w^2 := by
    unfold SignedGaussianMinimum.objective SignedGaussianLayerBudget.kernel
    field_simp
  rw [he] at h1
  have h2 : quadratic c K y-profile c y≤positiveGap c K y := le_max_right _ _
  unfold envelope
  linarith

theorem positiveGap_zero {c beta K y : ℝ} (hc : 0<c) (hc3 : c<3)
    (hb : 0<beta) (hb1 : beta≤1) (hK : K≤coefficient c beta) (hy : beta≤y) :
    positiveGap c K y=0 := by
  unfold positiveGap
  exact max_eq_left (sub_nonpos.mpr (SignedGaussianGlobal.quadratic_le_profile hc hc3 hb hb1 hK hy))

theorem envelope_lower {c beta K y : ℝ} (hc : 0<c) (hc3 : c<3)
    (hb : 0<beta) (hb1 : beta≤1) (hK : K≤coefficient c beta) (hy : beta≤y) (w : ℝ) :
    envelope c K y w≤SignedGaussianLayerBudget.kernel y w := by
  have h:=lower_with_gap (K:=K) hc (hb.trans_le hy) w
  rw [positiveGap_zero hc hc3 hb hb1 hK hy,sub_zero] at h
  exact h

theorem lower_with_slices {c alpha beta K y : ℝ}
    (hc : 0<c) (hc3 : c<3) (ha : 0<alpha) (hab : alpha<beta) (hb1 : beta≤1)
    (hK : K≤coefficient c beta) (cuts U : ℕ→ℝ) (n : ℕ)
    (hstart : cuts 0=alpha) (hend : cuts (n+1)=beta)
    (hsteps : ∀i≤n,cuts i≤cuts (i+1))
    (hU : ∀i≤n,positiveGap c K (cuts i)≤U i) (hy : alpha≤y) (w : ℝ) :
    envelope c K y w-
      ∑i∈range (n+1),U i*(if cuts i≤y ∧ y<cuts (i+1) then 1 else 0)≤
      SignedGaussianLayerBudget.kernel y w := by
  have hUn (i : ℕ) (hi : i≤n) : 0≤U i := (le_max_left _ _).trans (hU i hi)
  have hterm (i : ℕ) (hi : i∈range (n+1)) :
      0≤U i*(if cuts i≤y ∧ y<cuts (i+1) then 1 else 0) :=
    mul_nonneg (hUn i (by have := mem_range.mp hi; omega)) (by split_ifs <;> norm_num)
  have hsum:=sum_nonneg hterm
  by_cases hby : beta≤y
  · have h:=envelope_lower hc hc3 (ha.trans hab) hb1 hK hby w
    linarith
  · have hyb : y<beta := lt_of_not_ge hby
    obtain ⟨i,hi,hiy,hyi⟩:=exists_cut_interval cuts n (hstart ▸ hy) (hend ▸ hyb)
    have hai : alpha≤cuts i := hstart ▸ cut_le_of_steps cuts n hsteps (Nat.zero_le i) (by omega)
    have hib : cuts i≤beta := hend ▸ cut_le_of_steps cuts n hsteps (by omega) le_rfl
    have hg : positiveGap c K y≤U i :=
      ((SignedGaussianGlobal.positiveGap_antitone hc hc3 ha hab.le hb1)
        ⟨hai,hib⟩ ⟨hy,hyb.le⟩ hiy).trans (hU i hi)
    have his : U i≤∑j∈range (n+1),U j*(if cuts j≤y ∧ y<cuts (j+1) then 1 else 0) := by
      simpa only [if_pos (And.intro hiy hyi),mul_one] using
        single_le_sum hterm (mem_range.mpr (by omega : i<n+1))
    have h:=lower_with_gap (K:=K) hc (ha.trans_le hy) w
    linarith

#print axioms lower_with_gap
#print axioms envelope_lower
#print axioms lower_with_slices
end ForestUnimodality.SignedGaussianSlices
