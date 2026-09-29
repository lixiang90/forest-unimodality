import ForestUnimodality.IntermediateBridgeRank

/-! Connect checked interval geometry and integer ranks to actual forest
inequalities. Rectangle and parent proofs remain explicit obligations. -/
namespace ForestUnimodality.IntermediateBridgeCover
universe u v
variable {ι : Type v}
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def Rectangle.ForestValid (r : Rectangle) : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) (S B : Finset V) (z : ℝ) (k : ℕ),
    IsMaximumMarginalIndependentOn G S B z → G.IsAcyclic → 0<z → 1≤k →
    r.Contains S.card (z/(1+z)) (hardCoreAvailableMean G S B z) →
    (S.card:ℝ)/4≤hardCoreMean G S z → hardCoreMean G S z=k → 2*k≤S.card →
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1))

def Band.ParentValid (s : Band ι) : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) (S B : Finset V) (z : ℝ) (k : ℕ),
    IsMaximumMarginalIndependentOn G S B z → G.IsAcyclic → 0<S.card → S.card≤349 →
    0<z → 1≤k → z/(1+z)∈Set.Icc (s.qlo:ℝ) (s.qhi:ℝ) →
    (S.card:ℝ)/4≤hardCoreMean G S z → hardCoreMean G S z=k →
    (s.mhi:ℝ)≤hardCoreAvailableMean G S B z →
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1))

theorem ActivityCover.no_weak_valley (c : ActivityCover ι) (rectangles : ι→Rectangle)
    (hc : c.check rectangles=true)
    (hranks : ∀b∈c.bands,Band.RankValid.{v,u} b)
    (hparents : ∀b∈c.bands,Band.ParentValid.{u,v} b)
    (hcells : ∀b∈c.bands,∀i∈b.cells,Rectangle.ForestValid.{u} (rectangles i))
    {V : Type u} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) (z : ℝ) (k : ℕ)
    (hG : G.IsAcyclic) (hS : 0<S.card) (hN : S.card≤349)
    (hn : c.lowerOrder≤S.card) (hcap : S.card≤c.orderCap) (hz : 0<z) (hk : 1≤k)
    (hq : z/(1+z)∈Set.Icc (c.qlo:ℝ) (c.qhi:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k)
    (hhalf : 2*k≤S.card) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  obtain ⟨B,hB⟩ := exists_maximumWeightedIndependentOn G S (hardCoreVertexMarginal G S z)
  change IsMaximumMarginalIndependentOn G S B z at hB
  have hm := hardCoreAvailableMean_nonneg G S B hz.le
  have hmeanhalf := hB.half_mean hG.isBipartite
  rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz,
    hmean] at hmeanhalf
  have hmass : (k:ℝ)≤2*(z/(1+z))*hardCoreAvailableMean G S B z := by linarith
  have hchecks : FiniteRectangleCover.chainCheck (fun b : Band ι=>(b.qlo,b.qhi)) c.bands c.qlo c.qhi=true ∧
      (∀b∈c.bands,b.lowerOrder≤c.lowerOrder ∧ c.orderCap≤b.orderCap) ∧
      ∀b∈c.bands,b.check rectangles=true := by
    simpa only [ActivityCover.check,Bool.and_eq_true_iff,List.all_eq_true,decide_eq_true_eq] using hc
  have hgeometry := hchecks.2.1
  apply c.property rectangles hc hn hcap hq hm hmass
  · intro b hb hbq
    exact hranks b hb G S z k hG ((hgeometry b hb).1.trans hn) hz hbq hrank hmean
  · intro b hb hbq hbm
    exact hparents b hb G S B z k hB hG hS hN hz hk hbq hrank hmean hbm
  · intro b hb i hi hpoint
    exact hcells b hb i hi G S B z k hB hG hz hk hpoint hrank hmean hhalf

#print axioms ActivityCover.no_weak_valley
end ForestUnimodality.IntermediateBridgeCover
