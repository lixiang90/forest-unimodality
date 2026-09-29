import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.Stage170Geometry.Data
import ForestUnimodality.Stage350ParentHandoff

/-! Actual parent domains and exact transfer to the refined bridge bands.
The parent mean threshold is supplied explicitly, so no order170 lower bound
is needed when applying the already proved finite rectangle inequalities. -/
namespace ForestUnimodality.IntermediateBridgeCover
universe u v
variable {ι : Type v}
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def ParentRectangleValid (i : Fin 558) : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) (S B : Finset V) (z : ℝ) (k : ℕ),
    IsMaximumMarginalIndependentOn G S B z → G.IsAcyclic → 0<S.card → S.card≤349 →
    0<z → 1≤k → (Stage170Geometry.rectangle i).Contains (z/(1+z)) (hardCoreAvailableMean G S B z) →
    (S.card:ℝ)/4≤hardCoreMean G S z → hardCoreMean G S z=k →
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1))

def ParentComplete (i : Fin 130) : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) (S B : Finset V) (z : ℝ) (k : ℕ),
    IsMaximumMarginalIndependentOn G S B z → G.IsAcyclic → 0<S.card → S.card≤349 →
    0<z → 1≤k → z/(1+z)∈Set.Icc ((Stage170Geometry.strip i).qlo:ℝ) ((Stage170Geometry.strip i).qhi:ℝ) →
    (S.card:ℝ)/4≤hardCoreMean G S z → hardCoreMean G S z=k →
    ((Stage170Geometry.strip i).mlo:ℝ)≤hardCoreAvailableMean G S B z →
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1))

theorem parent_complete_of_rectangles (i : Fin 130)
    (hgeometry : (Stage170Geometry.strip i).check Stage170Geometry.rectangle=true)
    (hsource : (Stage170Geometry.strip i).sourceCheck (Stage170Geometry.window i) 170=true)
    (hrect : ∀r∈(Stage170Geometry.strip i).cells,ParentRectangleValid.{u} r) : ParentComplete.{u} i := by
  intro V _ G S B z k hB hG hS hN hz hk hq hrank hmean hm
  by_cases hhi : hardCoreAvailableMean G S B z≤((Stage170Geometry.strip i).mhi:ℝ)
  · obtain ⟨r,hr,hpoint⟩ := (Stage170Geometry.strip i).check_sound Stage170Geometry.rectangle hgeometry hq ⟨hm,hhi⟩
    exact hrect r hr G S B z k hB hG hS hN hz hk hpoint hrank hmean
  · have hp := (Stage170Geometry.strip i).parent_domain (Stage170Geometry.window i) 170
      (Stage170Geometry.window_valid i) hsource hz hq (le_of_not_ge hhi)
    exact Stage350ParentHandoff.no_weak_valley (Stage170Geometry.window i).parent
      k hB hG hS hp.2 hp.1 hrank hmean hk

def Band.parentCheck (s : Band ι) (i : Fin 130) : Bool :=
  decide (s.parentStrip=i.val ∧ (Stage170Geometry.strip i).qlo≤s.qlo ∧
    s.qhi≤(Stage170Geometry.strip i).qhi ∧ (Stage170Geometry.strip i).mlo≤s.mhi)

theorem Band.parent_of_check (s : Band ι) (i : Fin 130)
    (hc : s.parentCheck i=true) (hp : ParentComplete.{u} i) : Band.ParentValid.{u,v} s := by
  have ht : s.parentStrip=i.val ∧ (Stage170Geometry.strip i).qlo≤s.qlo ∧
      s.qhi≤(Stage170Geometry.strip i).qhi ∧ (Stage170Geometry.strip i).mlo≤s.mhi := by
    exact of_decide_eq_true hc
  intro V _ G S B z k hB hG hS hN hz hk hq hrank hmean hm
  have hlo : ((Stage170Geometry.strip i).qlo:ℝ)≤s.qlo := by exact_mod_cast ht.2.1
  have hhi : (s.qhi:ℝ)≤(Stage170Geometry.strip i).qhi := by exact_mod_cast ht.2.2.1
  have hml : ((Stage170Geometry.strip i).mlo:ℝ)≤s.mhi := by exact_mod_cast ht.2.2.2
  exact hp G S B z k hB hG hS hN hz hk ⟨hlo.trans hq.1,hq.2.trans hhi⟩
    hrank hmean (hml.trans hm)

#print axioms parent_complete_of_rectangles
#print axioms Band.parent_of_check
end ForestUnimodality.IntermediateBridgeCover
