import ForestUnimodality.ActivityPointDensityBranches

/-! Rational five-type branch data, with continuous deletion-ratio bounds.
The finite checker validates the two endpoints of each affine numerator. -/
namespace ForestUnimodality.ActivityPointDensity
open Branches
abbrev Kind := Fin 5
structure Parameters where
  x : ℚ
  r : ℚ
  s : ℚ
  g : ℚ
  B : ℚ
  h : ℚ

def Parameters.full (p : Parameters) : Kind→ℚ
  | ⟨0,_⟩ => p.x/(1+p.x)-p.r
  | ⟨1,_⟩ => 2*p.x/(1+2*p.x)-2*p.r
  | ⟨2,_⟩ => (3*p.x+2*p.x^2)/(1+3*p.x+p.x^2)-3*p.r
  | ⟨3,_⟩ => (3*p.x+2*p.x^2)/(1+3*p.x+p.x^2)-3*p.r
  | ⟨4,_⟩ => p.g

def Parameters.deleted (p : Parameters) : Kind→ℚ
  | ⟨0,_⟩ => -p.r
  | ⟨1,_⟩ => p.x/(1+p.x)-2*p.r
  | ⟨2,_⟩ => 2*p.x/(1+2*p.x)-3*p.r
  | ⟨3,_⟩ => 2*p.x/(1+p.x)-3*p.r
  | ⟨4,_⟩ => p.g-p.r

def Parameters.lo (p : Parameters) : Kind→ℚ
  | ⟨0,_⟩ => 1/(1+p.x)
  | ⟨1,_⟩ => (1+p.x)/(1+2*p.x)
  | ⟨2,_⟩ => (1+2*p.x)/(1+3*p.x+p.x^2)
  | ⟨3,_⟩ => (1+p.x)^2/(1+3*p.x+p.x^2)
  | ⟨4,_⟩ => 1/(1+p.x)

def Parameters.hi (p : Parameters) (i : Kind) : ℚ := if i=4 then 1 else p.lo i

def Parameters.numerator (p : Parameters) (ks : List Kind) (t : ℚ) : ℚ :=
  (ks.map p.full).sum+p.x*t*(1+(ks.map p.deleted).sum)-(p.B+p.r)*(1+p.x*t)

def Parameters.endpoints (p : Parameters) (ks : List Kind) : Prop :=
  0≤p.numerator ks (ks.map p.lo).prod ∧ 0≤p.numerator ks (ks.map p.hi).prod
instance (p : Parameters) (ks : List Kind) : Decidable (p.endpoints ks) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Parameters.Valid (p : Parameters) : Prop :=
  0≤p.x ∧ 0≤p.s ∧ p.B+p.r≤4*p.s ∧
  (∀i:Kind,p.s≤p.full i ∧ 0≤p.lo i ∧ p.lo i≤p.hi i ∧ p.hi i≤1 ∧
    0≤p.full i+p.x*p.hi i*p.deleted i) ∧
  (∀i j k:Kind,p.endpoints [i,j,k]) ∧ (∀i j k l:Kind,p.endpoints [i,j,k,l])
instance (p : Parameters) : Decidable p.Valid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
def Parameters.check (p : Parameters) : Bool := decide p.Valid

theorem Parameters.check_sound {p : Parameters} (h : p.check=true) : p.Valid := of_decide_eq_true h

def Parameters.Allowed (p : Parameters) (b : Branch) : Prop :=
  ∃i:Kind,b.full=(p.full i:ℝ) ∧ b.deleted=(p.deleted i:ℝ) ∧
    (p.lo i:ℝ)≤b.ratio ∧ b.ratio≤(p.hi i:ℝ)

theorem Parameters.admissible {p : Parameters} (h : p.Valid) {b : Branch} (hb : p.Allowed b) :
    Admissible p.x p.s b := by
  obtain ⟨i,hf,hd,hl,hu⟩:=hb
  obtain ⟨hfs,hlo,hlu,hhi,hgain⟩:=h.2.2.2.1 i
  have hx : (0:ℝ)≤p.x := by exact_mod_cast h.1
  have hs : (0:ℝ)≤p.s := by exact_mod_cast h.2.1
  have hf' : (p.s:ℝ)≤p.full i := by exact_mod_cast hfs
  have hl' : (0:ℝ)≤p.lo i := by exact_mod_cast hlo
  have hu' : (p.hi i:ℝ)≤1 := by exact_mod_cast hhi
  have hg' : (0:ℝ)≤(p.full i:ℝ)+p.x*p.hi i*p.deleted i := by exact_mod_cast hgain
  refine ⟨by simpa [hf] using hf',by simpa [hf] using hs.trans hf',hl'.trans hl,hu.trans hu',?_⟩
  rw [hf,hd]
  by_cases hc : 0≤(p.deleted i:ℝ)
  · exact add_nonneg (hs.trans hf') (mul_nonneg (mul_nonneg hx (hl'.trans hl)) hc)
  · have hm:=mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hx (sub_nonneg.mpr hu)) (le_of_not_ge hc)
    nlinarith

theorem Parameters.list_bounds {p : Parameters} (h : p.Valid) (bs : List Branch)
    (hb : ∀b∈bs,p.Allowed b) :
    ∃ks:List Kind,ks.length=bs.length ∧ Branches.full bs=((ks.map p.full).sum:ℚ) ∧
      Branches.deleted bs=((ks.map p.deleted).sum:ℚ) ∧
      (((ks.map p.lo).prod:ℚ):ℝ)≤product bs ∧ product bs≤((ks.map p.hi).prod:ℚ) := by
  induction bs with
  | nil => exact ⟨[],by simp [Branches.full,Branches.deleted,product]⟩
  | cons b bs ih =>
    obtain ⟨i,hf,hd,hl,hu⟩:=hb b (by simp)
    obtain ⟨ks,hlen,hfull,hdel,hlo,hhi⟩:=ih (by intro c hc; exact hb c (by simp [hc]))
    have ha:=p.admissible h (hb b (by simp))
    have hp:=product_bounds (bs:=bs) (by intro c hc; exact p.admissible h (hb c (show c∈b::bs by simp [hc])))
    have hlo0 : (0:ℝ)≤p.lo i := by exact_mod_cast (h.2.2.2.1 i).2.1
    have hlprod0 : (0:ℝ)≤((ks.map p.lo).prod:ℚ) := by
      exact_mod_cast List.prod_nonneg (by intro y hy; obtain ⟨i,_,rfl⟩:=List.mem_map.mp hy; exact (h.2.2.2.1 i).2.1)
    have hhprod0 : (0:ℝ)≤((ks.map p.hi).prod:ℚ) := hp.1.trans hhi
    refine ⟨i::ks,by simpa using hlen,?_,?_,?_,?_⟩
    · simp only [Branches.full,List.map_cons,List.sum_cons,Rat.cast_add]
      exact congrArg₂ (·+·) hf hfull
    · simp only [Branches.deleted,List.map_cons,List.sum_cons,Rat.cast_add]
      exact congrArg₂ (·+·) hd hdel
    · simp only [product,List.map_cons,List.prod_cons,Rat.cast_mul]
      exact mul_le_mul hl hlo hlprod0 ha.2.2.1
    · simp only [product,List.map_cons,List.prod_cons,Rat.cast_mul]
      exact mul_le_mul hu hhi hp.1 (by linarith)

theorem Parameters.endpoints_of_length {p : Parameters} (h : p.Valid) (ks : List Kind)
    (hn : ks.length=3 ∨ ks.length=4) : p.endpoints ks := by
  rcases ks with _|⟨i,ks⟩ <;> simp only [List.length_nil,List.length_cons] at hn
  · omega
  rcases ks with _|⟨j,ks⟩ <;> simp only [List.length_nil,List.length_cons] at hn
  · omega
  rcases ks with _|⟨k,ks⟩ <;> simp only [List.length_nil,List.length_cons] at hn
  · omega
  rcases ks with _|⟨l,ks⟩
  · exact h.2.2.2.2.1 i j k
  · have he : ks=[] := by apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at hn; omega
    subst ks
    exact h.2.2.2.2.2 i j k l

theorem Parameters.small_lower {p : Parameters} (h : p.Valid) (bs : List Branch)
    (hn : bs.length=3 ∨ bs.length=4) (hb : ∀b∈bs,p.Allowed b) :
    (p.B:ℝ)≤value p.x p.r bs := by
  obtain ⟨ks,hlen,hf,hd,hl,hu⟩:=p.list_bounds h bs hb
  obtain ⟨h0,h1⟩:=p.endpoints_of_length h ks (by simpa [hlen] using hn)
  have h0' : (0:ℝ)≤p.numerator ks (ks.map p.lo).prod := by exact_mod_cast h0
  have h1' : (0:ℝ)≤p.numerator ks (ks.map p.hi).prod := by exact_mod_cast h1
  unfold Parameters.numerator at h0' h1'
  simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one] at h0' h1'
  have hnum : 0≤Branches.full bs+(p.x:ℝ)*product bs*(1+Branches.deleted bs)-
      ((p.B:ℝ)+p.r)*(1+p.x*product bs) := by
    rw [hf,hd]
    by_cases hc : 0≤(p.x:ℝ)*(1+((ks.map p.deleted).sum:ℚ))-((p.B:ℝ)+p.r)*p.x
    · nlinarith [mul_nonneg hc (sub_nonneg.mpr hl)]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) (sub_nonneg.mpr hu)]
  have hp:=product_bounds (bs:=bs) (by intro b hb'; exact p.admissible h (hb b hb'))
  have hx : (0:ℝ)≤p.x := by exact_mod_cast h.1
  unfold value
  apply sub_le_iff_le_add.mp
  have hp0:=hp.1
  apply (le_div_iff₀ (by positivity : (0:ℝ)<1+p.x*product bs)).mpr
  linarith

theorem Parameters.all_lower {p : Parameters} (h : p.Valid) (bs : List Branch)
    (hn : 3≤bs.length) (hb : ∀b∈bs,p.Allowed b) : (p.B:ℝ)≤value p.x p.r bs := by
  apply all_degrees_lower (by exact_mod_cast h.1) (by exact_mod_cast h.2.1)
    (by exact_mod_cast h.2.2.1) p.Allowed (fun b hb=>p.admissible h hb) (p.small_lower h) bs hn hb

#print axioms Parameters.admissible
#print axioms Parameters.all_lower
end ForestUnimodality.ActivityPointDensity


