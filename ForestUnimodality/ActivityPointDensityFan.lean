import ForestUnimodality.ActivityPointDensityParameters
import ForestUnimodality.UnitActivityTreeBranches

/-! Arbitrary-activity branch mixture for an actual graph, and soundness of
the rational branch certificate on that same hard-core distribution. -/
namespace ForestUnimodality
open Finset ActivityPointDensity
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

theorem IsRootedFanOn.activity_mean_mixture
    {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι→Finset V} {root : ι→V}
    (h : IsRootedFanOn G S c s B root) {z : ℝ} (hz : 0≤z) :
    let R:=∏i∈s,partitionFunction G ((B i).erase (root i)) (z:ℝ)/partitionFunction G (B i) z
    hardCoreMean G S z=((∑i∈s,hardCoreMean G (B i) z)+
      z*R*(1+∑i∈s,hardCoreMean G ((B i).erase (root i)) z))/(1+z*R) := by
  have ha : 0<∏i∈s,partitionFunction G (B i) z :=
    Finset.prod_pos (fun _ _=>partitionFunction_pos _ _ hz)
  have hb : 0<∏i∈s,partitionFunction G ((B i).erase (root i)) z :=
    Finset.prod_pos (fun _ _=>partitionFunction_pos _ _ hz)
  dsimp only
  rw [Finset.prod_div_distrib]
  change hardCoreMomentNumerator G S 1 z/partitionFunction G S z=_
  rw [h.firstMoment hz,h.partitionFunction_eq G z]
  have hab : (∏i∈s,partitionFunction G (B i) z)+
      z*(∏i∈s,partitionFunction G ((B i).erase (root i)) z)≠0 := by positivity
  field_simp
  ring

/-- The local premises are genuine branch means and deletion ratios; the
finite scalar certificate handles every degree and the whole ratio interval. -/
theorem IsRootedFanOn.activity_density_lower
    {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι→Finset V} {root : ι→V}
    (h : IsRootedFanOn G S c s B root) {p : ActivityPointDensity.Parameters}
    (hp : p.Valid) (hs : 3≤s.card)
    (hbranch : ∀i∈s,∃k:Kind,
      (p.r:ℝ)*(B i).card+p.full k≤hardCoreMean G (B i) p.x ∧
      (p.r:ℝ)*(B i).card+p.deleted k≤hardCoreMean G ((B i).erase (root i)) p.x ∧
      (p.lo k:ℝ)≤partitionFunction G ((B i).erase (root i)) (p.x:ℝ)/partitionFunction G (B i) (p.x:ℝ) ∧
      partitionFunction G ((B i).erase (root i)) (p.x:ℝ)/partitionFunction G (B i) (p.x:ℝ)≤p.hi k) :
    (p.r:ℝ)*S.card+p.B≤hardCoreMean G S p.x := by
  classical
  let K : ι→Kind := fun i=>if hi:i∈s then (hbranch i hi).choose else 0
  let R : ι→ℝ := fun i=>partitionFunction G ((B i).erase (root i)) (p.x:ℝ)/partitionFunction G (B i) (p.x:ℝ)
  let b : ι→Branches.Branch := fun i=>⟨p.full (K i),p.deleted (K i),R i⟩
  have hk : ∀i∈s,
      (p.r:ℝ)*(B i).card+p.full (K i)≤hardCoreMean G (B i) p.x ∧
      (p.r:ℝ)*(B i).card+p.deleted (K i)≤hardCoreMean G ((B i).erase (root i)) p.x ∧
      (p.lo (K i):ℝ)≤R i ∧ R i≤p.hi (K i) := by
    intro i hi
    simpa only [K,dif_pos hi,R] using (hbranch i hi).choose_spec
  have hl:=p.all_lower hp (s.toList.map b) (by simpa using hs) (by
    intro a ha
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
    have hi':i∈s:=by simpa using hi
    exact ⟨K i,rfl,rfl,(hk i hi').2.2⟩)
  simp only [Branches.value,Branches.full,Branches.deleted,Branches.product,List.map_map] at hl
  have hfull : (p.r:ℝ)*(∑i∈s,((B i).card:ℝ))+(∑i∈s,(p.full (K i):ℝ))≤
      ∑i∈s,hardCoreMean G (B i) p.x := by
    simpa [sum_add_distrib,mul_sum] using sum_le_sum (fun i hi=>(hk i hi).1)
  have hdel : (p.r:ℝ)*(∑i∈s,((B i).card:ℝ))+(∑i∈s,(p.deleted (K i):ℝ))≤
      ∑i∈s,hardCoreMean G ((B i).erase (root i)) p.x := by
    simpa [sum_add_distrib,mul_sum] using sum_le_sum (fun i hi=>(hk i hi).2.1)
  have hx : (0:ℝ)≤p.x := by exact_mod_cast hp.1
  have hR : 0≤∏i∈s,R i := by
    apply prod_nonneg
    intro i _
    exact div_nonneg (partitionFunction_pos _ _ hx).le (partitionFunction_pos _ _ hx).le
  have hd : 0<1+(p.x:ℝ)*(∏i∈s,R i) := by positivity
  have hc : (S.card:ℝ)=(∑i∈s,((B i).card:ℝ))+1 := by exact_mod_cast h.card
  have hnum : ((p.B:ℝ)+p.r)*(1+(p.x:ℝ)*(∏i∈s,R i))≤
      (∑i∈s,(p.full (K i):ℝ))+(p.x:ℝ)*(∏i∈s,R i)*(1+∑i∈s,(p.deleted (K i):ℝ)) := by
    apply (le_div_iff₀ hd).mp
    simp [b,Function.comp_def] at hl
    linarith
  rw [h.activity_mean_mixture hx,hc]
  change _≤((∑i∈s,hardCoreMean G (B i) p.x)+(p.x:ℝ)*(∏i∈s,R i)*
    (1+∑i∈s,hardCoreMean G ((B i).erase (root i)) p.x))/(1+(p.x:ℝ)*(∏i∈s,R i))
  apply (le_div_iff₀ hd).mpr
  nlinarith [mul_nonneg (mul_nonneg hx hR) (sub_nonneg.mpr hdel)]

#print axioms IsRootedFanOn.activity_mean_mixture
#print axioms IsRootedFanOn.activity_density_lower
end ForestUnimodality

