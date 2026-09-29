import ForestUnimodality.KernelBudget
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The finite outward step is bounded using curvature of the same Gaussian
mixture, with its actual joint layer variables kept fixed. -/
namespace ForestUnimodality.GaussianFiniteStep
open Set Finset

/-- Integrate a quadratic curvature bound twice, without dropping the
linear term or changing the distribution midway through the step. -/
theorem finite_step_lower {f f₁ f₂ : ℝ → ℝ} {h G c : ℝ} (hh : 0 ≤ h)
    (hf : ∀ s ∈ Icc 0 h, HasDerivAt f (f₁ s) s)
    (hf₁ : ∀ s ∈ Icc 0 h, HasDerivAt f₁ (f₂ s) s)
    (hcurv : ∀ s ∈ Icc 0 h, G-c*s^2/2 ≤ -f₂ s) :
    G*h^2/2-c*h^4/24 ≤ f 0-f h+h*f₁ 0 := by
  let g₁ := fun s => f₁ s-f₁ 0+G*s-c*s^3/6
  have hd₁ (s : ℝ) (hs : s ∈ Icc 0 h) : HasDerivAt g₁ (f₂ s+G-c*s^2/2) s := by
    apply ((((hf₁ s hs).sub_const (f₁ 0)).add ((hasDerivAt_id s).const_mul G)).sub
      (((hasDerivAt_pow 3 s).const_mul c).div_const 6)).congr_deriv
    norm_num
    ring
  have hmono₁ : AntitoneOn g₁ (Icc 0 h) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro s hs; exact (hd₁ s hs).continuousAt.continuousWithinAt
    · intro s hs; exact (hd₁ s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hd₁ s (interior_subset hs)).deriv]
      linarith [hcurv s (interior_subset hs)]
  have hnonpos (s : ℝ) (hs : s ∈ Icc 0 h) : g₁ s ≤ 0 := by
    have he := hmono₁ ⟨le_rfl,hh⟩ hs hs.1
    simpa [g₁] using he
  let g := fun s => f s-f 0-s*f₁ 0+G*s^2/2-c*s^4/24
  have hd (s : ℝ) (hs : s ∈ Icc 0 h) : HasDerivAt g (g₁ s) s := by
    apply (((((hf s hs).sub_const (f 0)).sub ((hasDerivAt_id s).mul_const (f₁ 0))).add
      (((hasDerivAt_pow 2 s).const_mul G).div_const 2)).sub
      (((hasDerivAt_pow 4 s).const_mul c).div_const 24)).congr_deriv
    dsimp [g₁]
    norm_num
    ring
  have hmono : AntitoneOn g (Icc 0 h) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro s hs; exact (hd s hs).continuousAt.continuousWithinAt
    · intro s hs; exact (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hd s (interior_subset hs)).deriv]
      exact hnonpos s (interior_subset hs)
  have he := hmono ⟨le_rfl,hh⟩ ⟨hh,le_rfl⟩ hh
  dsimp [g] at he
  norm_num at he
  linarith

noncomputable def profile (y x : ℝ) : ℝ := y^(-(1/2 : ℝ))*Real.exp (-x^2/(2*y))
noncomputable def first (y x : ℝ) : ℝ := -(x/y)*profile y x
noncomputable def second (y x : ℝ) : ℝ := (x^2/y^2-1/y)*profile y x

theorem hasDerivAt_profile (y x : ℝ) : HasDerivAt (profile y) (first y x) x := by
  have hd := (((((hasDerivAt_pow 2 x).neg).div_const (2*y)).exp).const_mul (y^(-(1/2 : ℝ))))
  apply hd.congr_deriv
  dsimp only [Pi.neg_apply]
  simp only [first, profile, Nat.cast_ofNat, show (2:ℕ)-1=1 from rfl, pow_one]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem hasDerivAt_first (y x : ℝ) : HasDerivAt (first y) (second y x) x := by
  apply (((hasDerivAt_id x).div_const y).neg.mul (hasDerivAt_profile y x)).congr_deriv
  dsimp [second, first]
  simp only [div_eq_mul_inv]
  ring

noncomputable def mixture {α : Type*} (s : Finset α) (w y x : α → ℝ) (shift : ℝ) : ℝ :=
  KernelBudget.expect s w (fun a => profile (y a) (x a+shift))

theorem mixture_finite_step {α : Type*} (s : Finset α) (w y x : α → ℝ) {h G c : ℝ}
    (hh : 0 ≤ h)
    (hcurv : ∀ t ∈ Icc 0 h,
      G-c*t^2/2 ≤ KernelBudget.expect s w (fun a => -second (y a) (x a+t))) :
    G*h^2/2-c*h^4/24 ≤ KernelBudget.expect s w (fun a =>
      profile (y a) (x a)-profile (y a) (x a+h)+h*first (y a) (x a)) := by
  let f₁ := fun t => KernelBudget.expect s w (fun a => first (y a) (x a+t))
  let f₂ := fun t => KernelBudget.expect s w (fun a => second (y a) (x a+t))
  have hd (t : ℝ) : HasDerivAt (mixture s w y x) (f₁ t) t := by
    apply HasDerivAt.fun_sum
    intro a _
    simpa only [Function.comp_def, mul_one] using
      ((hasDerivAt_profile (y a) (x a+t)).comp t ((hasDerivAt_id t).const_add (x a))).const_mul (w a)
  have hd₁ (t : ℝ) : HasDerivAt f₁ (f₂ t) t := by
    apply HasDerivAt.fun_sum
    intro a _
    simpa only [Function.comp_def, mul_one] using
      ((hasDerivAt_first (y a) (x a+t)).comp t ((hasDerivAt_id t).const_add (x a))).const_mul (w a)
  have hc : ∀ t ∈ Icc 0 h, G-c*t^2/2 ≤ -f₂ t := by
    intro t ht
    simpa only [f₂, KernelBudget.expect, mul_neg, sum_neg_distrib] using hcurv t ht
  have he := finite_step_lower hh (fun t _ => hd t) (fun t _ => hd₁ t) hc
  simpa only [mixture, f₁, KernelBudget.expect_sub, KernelBudget.expect_add,
    KernelBudget.expect_const_mul, add_zero] using he

#print axioms finite_step_lower
#print axioms hasDerivAt_first
#print axioms mixture_finite_step
end ForestUnimodality.GaussianFiniteStep
