import ForestUnimodality.BernsteinCover
import Mathlib.Tactic

/-! Symbolic Bernstein witnesses: exact identities of real polynomials and
nonnegative rational coefficients, avoiding expansion of nested coefficient
lists in one large kernel reduction. -/
namespace ForestUnimodality.BernsteinCertificate

open PolynomialList

noncomputable def value₂ (c : Certificate₂) (x y : ℝ) : ℝ :=
  ((List.finRange (c.degreeX + 1)).map fun i =>
    ((List.finRange (c.degreeY + 1)).map fun j =>
      (c.coeff i j : ℝ) * (c.degreeX.choose i : ℝ) * x ^ (i : ℕ) *
        (1 - x) ^ (c.degreeX - i) * (c.degreeY.choose j : ℝ) *
        y ^ (j : ℕ) * (1 - y) ^ (c.degreeY - j)).sum).sum

theorem value₂_nonneg (c : Certificate₂) (hc : ∀ i j, 0 ≤ c.coeff i j)
    {x y : ℝ} (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    0 ≤ value₂ c x y := by
  unfold value₂
  apply List.sum_nonneg
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  apply List.sum_nonneg
  intro b hb
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
  have hcoeff : (0 : ℝ) ≤ c.coeff i j := Rat.cast_nonneg.mpr (hc i j)
  have hx0 := hx.1
  have hy0 := hy.1
  have hx' : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  have hy' : 0 ≤ 1 - y := sub_nonneg.mpr hy.2
  positivity

theorem box_nonneg_of_identity (p : BiPolynomial) (lx hx ly hy : ℚ) (c : Certificate₂)
    (hxx : lx ≤ hx) (hyy : ly ≤ hy) (hc : ∀ i j, 0 ≤ c.coeff i j)
    (he : ∀ x y : ℝ,
      evalReal₂ p ((lx : ℝ) + ((hx : ℝ) - lx) * x)
        ((ly : ℝ) + ((hy : ℝ) - ly) * y) = value₂ c x y)
    {x y : ℝ} (hX : x ∈ Set.Icc (lx : ℝ) (hx : ℝ))
    (hY : y ∈ Set.Icc (ly : ℝ) (hy : ℝ)) : 0 ≤ evalReal₂ p x y := by
  obtain ⟨u, hu, rfl⟩ := exists_affine_parameter (Rat.cast_le.mpr hxx) hX
  obtain ⟨v, hv, rfl⟩ := exists_affine_parameter (Rat.cast_le.mpr hyy) hY
  rw [he]
  exact value₂_nonneg c hc hu hv

def Cover.Semantic (p : BiPolynomial) (lx hx ly hy : ℚ) : Cover → Prop
  | .leaf _ => ∀ x ∈ Set.Icc (lx : ℝ) (hx : ℝ),
      ∀ y ∈ Set.Icc (ly : ℝ) (hy : ℝ), 0 ≤ evalReal₂ p x y
  | .splitX l r => l.Semantic p lx ((lx + hx) / 2) ly hy ∧
      r.Semantic p ((lx + hx) / 2) hx ly hy
  | .splitY l r => l.Semantic p lx hx ly ((ly + hy) / 2) ∧
      r.Semantic p lx hx ((ly + hy) / 2) hy

theorem Cover.Semantic.sound (tree : Cover) {p : BiPolynomial} {lx hx ly hy : ℚ}
    (hc : tree.Semantic p lx hx ly hy) {x y : ℝ}
    (hxx : x ∈ Set.Icc (lx : ℝ) (hx : ℝ))
    (hyy : y ∈ Set.Icc (ly : ℝ) (hy : ℝ)) : 0 ≤ evalReal₂ p x y := by
  induction tree generalizing lx hx ly hy with
  | leaf c => exact hc x hxx y hyy
  | splitX l r ihl ihr =>
    obtain ⟨hl, hr⟩ := hc
    by_cases hm : x ≤ (((lx + hx) / 2 : ℚ) : ℝ)
    · exact ihl hl ⟨hxx.1, hm⟩ hyy
    · exact ihr hr ⟨(lt_of_not_ge hm).le, hxx.2⟩ hyy
  | splitY l r ihl ihr =>
    obtain ⟨hl, hr⟩ := hc
    by_cases hm : y ≤ (((ly + hy) / 2 : ℚ) : ℝ)
    · exact ihl hl hxx ⟨hyy.1, hm⟩
    · exact ihr hr hxx ⟨(lt_of_not_ge hm).le, hyy.2⟩

#print axioms box_nonneg_of_identity
#print axioms Cover.Semantic.sound
end ForestUnimodality.BernsteinCertificate
