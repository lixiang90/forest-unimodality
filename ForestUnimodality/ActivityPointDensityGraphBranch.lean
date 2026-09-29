import ForestUnimodality.ActivityPointDensityFan
import ForestUnimodality.ActivityPointDensitySmall

namespace ForestUnimodality.ActivityPointDensity
open Finset ActivityPointDensitySmall
variable {V : Type*} [DecidableEq V]

theorem deleted_ratio_bounds (G : SimpleGraph V) (S : Finset V) {u : V} (hu : u∈S)
    {z : ℝ} (hz : 0≤z) :
    1/(1+z)≤partitionFunction G (S.erase u) z/partitionFunction G S z ∧
    partitionFunction G (S.erase u) z/partitionFunction G S z≤1 := by
  have hZ:=partitionFunction_pos G S hz
  have hA:=partitionFunction_pos G (S.erase u) hz
  have hh:=partitionFunction_delete_ratio_bounds G S hu hz
  have hl: partitionFunction G (S.erase u) z≤partitionFunction G S z := by
    have :=(le_div_iff₀ hA).mp hh.1
    simpa using this
  have hu': partitionFunction G S z≤(1+z)*partitionFunction G (S.erase u) z :=
    (div_le_iff₀ hA).mp hh.2
  refine ⟨?_,(div_le_one hZ).mpr hl⟩
  apply (div_le_div_iff₀ (by positivity : 0<1+z) hZ).mpr
  nlinarith

theorem branch_estimate {p : Parameters} (hp : p.Valid)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V) (u : V)
    (hu : u∈B) (hBS : B⊆S) (hBl : B.card<S.card)
    (hconn : (G.induce (B:Set V)).Connected)
    (hsmall : ∀T:Finset V,T⊆S→T.card<S.card→3≤T.card→
      (p.r:ℝ)*T.card+p.g≤hardCoreMean G T p.x) :
    ∃k:Kind,(p.r:ℝ)*B.card+p.full k≤hardCoreMean G B p.x ∧
      (p.r:ℝ)*B.card+p.deleted k≤hardCoreMean G (B.erase u) p.x ∧
      (p.lo k:ℝ)≤partitionFunction G (B.erase u) (p.x:ℝ)/partitionFunction G B (p.x:ℝ) ∧
      partitionFunction G (B.erase u) (p.x:ℝ)/partitionFunction G B (p.x:ℝ)≤p.hi k := by
  have hx : (0:ℝ)≤p.x := by exact_mod_cast hp.1
  have hpos : 0<B.card := card_pos.mpr ⟨u,hu⟩
  have hdc :=card_erase_add_one hu
  by_cases h1 : B.card=1
  · have he : B.erase u=∅ := card_eq_zero.mp (by omega)
    obtain ⟨hZ,hM⟩:=statistics_card_one G B h1 p.x
    have hm:hardCoreMean G B p.x=(p.x:ℝ)/(1+p.x) := by rw [hardCoreMean,hZ,hM]
    have hdz:partitionFunction G (B.erase u) (p.x:ℝ)=1 := by simp [he,partitionFunction,independentSubsets_empty_eq_singleton]
    have hdm:hardCoreMean G (B.erase u) p.x=0 := by
      simp [he,hardCoreMean,hardCoreMomentNumerator,independentSubsets_empty_eq_singleton]
    refine ⟨0,?_,?_,?_,?_⟩ <;>
      simp [Parameters.full,Parameters.deleted,Parameters.lo,Parameters.hi,h1,hm,hdm,hdz,hZ]
  by_cases h2 : B.card=2
  · have he : (B.erase u).card=1 := by omega
    have hc:=UnitActivitySmallForest.count_pair_eq_zero_of_connected_card_two G B h2 hconn
    obtain ⟨hZ,hM⟩:=statistics_card_two G B h2 p.x
    simp only [hc,Nat.cast_zero,zero_mul,add_zero] at hZ hM
    obtain ⟨hdz,hdm⟩:=statistics_card_one G (B.erase u) he p.x
    refine ⟨1,?_,?_,?_,?_⟩ <;>
      simp [Parameters.full,Parameters.deleted,Parameters.lo,Parameters.hi,h2,hardCoreMean,hZ,hM,hdz,hdm] <;> ring_nf <;> rfl
  by_cases h3 : B.card=3
  · have hm:=tree_card_three_mean G B hG h3 hconn (p.x:ℝ)
    obtain hd|hd:=deleted_pair_cases G B h3 hu
    · obtain ⟨hmd,hr⟩:=deleted_endpoint_statistics G B hG h3 hconn hu hd (p.x:ℝ)
      refine ⟨2,?_,?_,?_,?_⟩ <;>
        simp [Parameters.full,Parameters.deleted,Parameters.lo,Parameters.hi,h3,hm,hmd,hr] <;> ring_nf <;> rfl
    · obtain ⟨hmd,hr⟩:=deleted_center_statistics G B hG h3 hconn hu hd hx
      refine ⟨3,?_,?_,?_,?_⟩ <;>
        simp [Parameters.full,Parameters.deleted,Parameters.lo,Parameters.hi,h3,hm,hmd,hr] <;> ring_nf <;> rfl
  · have hn4 : 4≤B.card := by omega
    have hfull:=hsmall B hBS hBl (by omega)
    have hdel:=hsmall (B.erase u) ((erase_subset _ _).trans hBS) (by omega) (by omega)
    have hdc' : ((B.erase u).card:ℝ)+1=B.card := by exact_mod_cast hdc
    obtain ⟨hlo,hhi⟩:=deleted_ratio_bounds G B hu hx
    refine ⟨4,?_,?_,?_,?_⟩
    · simpa [Parameters.full] using hfull
    · simp only [Parameters.deleted,Rat.cast_sub]
      rw [←hdc']
      nlinarith
    · simpa [Parameters.lo] using hlo
    · simpa [Parameters.hi] using hhi

variable {ι : Type*} [DecidableEq ι]
theorem fan_density {p : Parameters} (hp : p.Valid)
    {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι→Finset V} {root : ι→V}
    (h : IsRootedFanOn G S c s B root) (hs : 3≤s.card)
    (hconn : ∀i∈s,(G.induce (B i:Set V)).Connected) (hG : G.IsAcyclic)
    (hsmall : ∀T:Finset V,T⊆S→T.card<S.card→3≤T.card→
      (p.r:ℝ)*T.card+p.g≤hardCoreMean G T p.x) :
    (p.r:ℝ)*S.card+p.B≤hardCoreMean G S p.x := by
  apply h.activity_density_lower hp hs
  intro i hi
  have hBS : B i⊆S := by
    intro x hx
    rw [h.vertices]
    exact mem_insert_of_mem (mem_biUnion.mpr ⟨i,hi,hx⟩)
  have hBl : (B i).card<S.card := by
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hBS,?_⟩
    intro he
    exact h.center_not_mem i hi (he ▸ h.center_mem)
  exact branch_estimate hp G hG S (B i) (root i) (h.root_mem i hi) hBS hBl (hconn i hi) hsmall

#print axioms branch_estimate
#print axioms fan_density
end ForestUnimodality.ActivityPointDensity

