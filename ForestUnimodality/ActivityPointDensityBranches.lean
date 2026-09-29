import ForestUnimodality.ActivityPointDensityPath
import Mathlib.Data.Fintype.Pi

/-! Scalar rooted-branch estimates. The induction below covers unbounded
branch degree, using a certified three- and four-branch base. -/
namespace ForestUnimodality.ActivityPointDensity.Branches
open Finset

structure Branch where
  full : ℝ
  deleted : ℝ
  ratio : ℝ

noncomputable def full (bs : List Branch) : ℝ := (bs.map Branch.full).sum
noncomputable def deleted (bs : List Branch) : ℝ := (bs.map Branch.deleted).sum
noncomputable def product (bs : List Branch) : ℝ := (bs.map Branch.ratio).prod
noncomputable def value (x r : ℝ) (bs : List Branch) : ℝ :=
  (full bs+x*product bs*(1+deleted bs))/(1+x*product bs)-r

def Admissible (x s : ℝ) (b : Branch) : Prop :=
  s≤b.full ∧ 0≤b.full ∧ 0≤b.ratio ∧ b.ratio≤1 ∧ 0≤b.full+x*b.ratio*b.deleted

theorem product_bounds {x s : ℝ} {bs : List Branch}
    (h : ∀b∈bs,Admissible x s b) : 0≤product bs ∧ product bs≤1 := by
  induction bs with
  | nil => norm_num [product]
  | cons b bs ih =>
    have hb:=h b (by simp)
    have ht:=ih (by intro c hc; exact h c (by simp [hc]))
    simp only [product,List.map_cons,List.prod_cons]
    change 0≤b.ratio*product bs ∧ b.ratio*product bs≤1
    exact ⟨mul_nonneg hb.2.2.1 ht.1,(mul_le_mul hb.2.2.2.1 ht.2 ht.1 (by norm_num)).trans (by norm_num)⟩

theorem full_lower {x s : ℝ} {bs : List Branch}
    (h : ∀b∈bs,Admissible x s b) : (bs.length:ℝ)*s≤full bs := by
  induction bs with
  | nil => simp [full]
  | cons b bs ih =>
    have hb: s≤b.full := (h b (by simp)).1
    have ht:=ih (by intro c hc; exact h c (by simp [hc]))
    simp only [full,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    change ((bs.length:ℝ)+1)*s≤b.full+full bs
    linarith

theorem cons_lower {x r s B : ℝ} {b : Branch} {bs : List Branch}
    (hx : 0≤x) (hb : Admissible x s b)
    (ht : ∀c∈bs,Admissible x s c)
    (hv : B≤value x r bs) (hf : B+r≤full bs) : B≤value x r (b::bs) := by
  obtain ⟨hP0,hP1⟩:=product_bounds ht
  have hd0 : 0<1+x*product bs := by positivity
  have hd1 : 0<1+x*b.ratio*product bs := by
    have :=hb.2.2.1
    positivity
  have hnum : (B+r)*(1+x*product bs)≤full bs+x*product bs*(1+deleted bs) := by
    exact (le_div_iff₀ hd0).mp (by simpa [value] using (show B+r≤value x r bs+r by linarith))
  have hgain : 0≤b.full+x*b.ratio*product bs*b.deleted := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hP1) hb.2.1,
      mul_nonneg hP0 hb.2.2.2.2]
  unfold value
  simp only [full,deleted,product,List.map_cons,List.sum_cons,List.prod_cons]
  change B≤(b.full+full bs+x*(b.ratio*product bs)*(1+(b.deleted+deleted bs)))/
    (1+x*(b.ratio*product bs))-r
  apply sub_le_iff_le_add.mp
  apply (le_div_iff₀ (by nlinarith : 0<1+x*(b.ratio*product bs))).mpr
  nlinarith [mul_nonneg hb.2.2.1 (sub_nonneg.mpr hnum),
    mul_nonneg (sub_nonneg.mpr hb.2.2.2.1) (sub_nonneg.mpr hf)]

/-- Three and four branch certificates imply the bound at every larger
branch degree; the number of children is not truncated. -/
theorem all_degrees_lower {x r s B : ℝ} (hx : 0≤x) (hs : 0≤s)
    (hfour : B+r≤4*s) (Allowed : Branch→Prop)
    (hadm : ∀b,Allowed b→Admissible x s b)
    (hbase : ∀bs:List Branch,(bs.length=3 ∨ bs.length=4)→
      (∀b∈bs,Allowed b)→B≤value x r bs)
    (bs : List Branch) (hn : 3≤bs.length) (hb : ∀b∈bs,Allowed b) :
    B≤value x r bs := by
  induction bs with
  | nil => simp at hn
  | cons b bs ih =>
    simp only [List.length_cons] at hn
    by_cases hh : bs.length≤3
    · apply hbase _ (by simp only [List.length_cons]; omega) hb
    · apply cons_lower hx (hadm b (hb b (by simp)))
        (by intro c hc; exact hadm c (hb c (by simp [hc])))
      · exact ih (by omega) (by intro c hc; exact hb c (by simp [hc]))
      · have hf:=full_lower (bs:=bs) (by intro c hc; exact hadm c (hb c (by simp [hc])))
        have hl : (4:ℝ)≤bs.length := by exact_mod_cast (show 4≤bs.length by omega)
        exact hfour.trans ((mul_le_mul_of_nonneg_right hl hs).trans hf)
#print axioms cons_lower
#print axioms all_degrees_lower
end ForestUnimodality.ActivityPointDensity.Branches


