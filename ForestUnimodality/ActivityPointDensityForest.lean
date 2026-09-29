import ForestUnimodality.ActivityPointDensityGraphBranch
import ForestUnimodality.UnitActivityForestDensity

/-! Complete arbitrary-order forest density from rational local certificates.
All graph branches, disconnected components and paths are derived from the
actual induced forest; no finite-order extrapolation is used. -/
namespace ForestUnimodality.ActivityPointDensity
open Finset

structure Certificate where
  parameters : Parameters
  path : Path.Witness

def Certificate.Valid (c : Certificate) : Prop :=
  c.parameters.Valid ∧ c.parameters.s≤c.parameters.g ∧ c.parameters.g≤c.parameters.B ∧
  c.parameters.g≤2*c.parameters.s ∧ c.parameters.h≤c.parameters.B ∧
  c.parameters.h≤2*c.parameters.s ∧
  c.path.Valid c.parameters.x c.parameters.r c.parameters.s 1 ∧
  c.path.Valid c.parameters.x c.parameters.r c.parameters.g 3 ∧
  c.path.Valid c.parameters.x c.parameters.r c.parameters.h 8
instance (c : Certificate) : Decidable c.Valid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
def Certificate.check (c : Certificate) : Bool := decide c.Valid
theorem Certificate.check_sound {c : Certificate} (h : c.check=true) : c.Valid := of_decide_eq_true h

variable {V : Type*} [DecidableEq V]
theorem path_density_of_degrees {p : Parameters} {w : Path.Witness} {g : ℚ} {low : ℕ}
    (hw : w.Valid p.x p.r g low)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (hS : S.Nonempty)
    (hconn : (G.induce (S:Set V)).Connected)
    (hdegrees : ∀v∈S,degreeOn G S v≤2) (hcard : low≤S.card) :
    (p.r:ℝ)*S.card+g≤hardCoreMean G S p.x := by
  classical
  letI : Nonempty (S:Set V) := ⟨⟨hS.choose,hS.choose_spec⟩⟩
  obtain ⟨v,hv⟩:=exists_degree_le_one_of_isAcyclic (G.induce (S:Set V)) (hG.induce (S:Set V))
  have hd : degreeOn G S v.val≤1 := by rwa [degreeOn_eq_degree_induce G S v.property]
  obtain ⟨u,n,hp⟩:=exists_pendantPath_to_of_connected_degree_le_two G S v.property hconn hdegrees hd
  exact Path.mean_lower_of_path hp hw hcard

theorem Certificate.forest_intercepts {c : Certificate} (hc : c.Valid)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) :
    (0<S.card→(c.parameters.r:ℝ)*S.card+c.parameters.s≤hardCoreMean G S c.parameters.x) ∧
    (3≤S.card→(c.parameters.r:ℝ)*S.card+c.parameters.g≤hardCoreMean G S c.parameters.x) := by
  classical
  have hx : (0:ℝ)≤c.parameters.x := by exact_mod_cast hc.1.1
  have hsg : (c.parameters.s:ℝ)≤c.parameters.g := by exact_mod_cast hc.2.1
  have hgB : (c.parameters.g:ℝ)≤c.parameters.B := by exact_mod_cast hc.2.2.1
  have hgs : (c.parameters.g:ℝ)≤2*c.parameters.s := by exact_mod_cast hc.2.2.2.1
  refine S.strongInductionOn ?_
  intro S ih
  by_cases hpos : 0<S.card
  · have hrec (T:Finset V) (hTS:T⊆S) (hlt:T.card<S.card) :=
      ih T (Finset.ssubset_iff_subset_ne.mpr ⟨hTS,by intro he; subst T; exact (lt_irrefl _ hlt)⟩)
    by_cases hconn : (G.induce (S:Set V)).Connected
    · by_cases hdeg : ∀v∈S,degreeOn G S v≤2
      · exact ⟨fun _=>path_density_of_degrees hc.2.2.2.2.2.2.1 G hG S (card_pos.mp hpos)
            hconn hdeg hpos,
          fun hn=>path_density_of_degrees hc.2.2.2.2.2.2.2.1 G hG S (card_pos.mp hpos) hconn hdeg hn⟩
      · push Not at hdeg
        obtain ⟨v,hv,hd⟩:=hdeg
        obtain ⟨root,hfan⟩:=exists_rootedFan_of_tree G hG S hv hconn
        have hbound:=fan_density hc.1 hfan (by rw [←hfan.unitActivity_degree_center]; omega)
          (by intro i _; exact deletedCenterBranch_connected G S v i) hG
          (by intro T hTS hlt hn; exact (hrec T hTS hlt).2 hn)
        exact ⟨fun _=>by linarith,fun _=>by linarith⟩
    · obtain ⟨A,B,hAS,hBS,hA,hB,ha,hb,hdis,hu,hcross⟩:=
        UnitActivityForestDensity.exists_disconnected_split G S (card_pos.mp hpos) hconn
      have hmuA:=(hrec A hAS ha).1 (card_pos.mpr hA)
      have hmuB:=(hrec B hBS hb).1 (card_pos.mpr hB)
      have hmu:=hardCoreMean_disjoint_union G A B hdis hcross hx
      have hcard : (A.card:ℝ)+B.card=S.card := by
        exact_mod_cast ((card_union_of_disjoint hdis).symm.trans (congrArg Finset.card hu))
      rw [hu] at hmu
      have hstrong : (c.parameters.r:ℝ)*S.card+c.parameters.g≤hardCoreMean G S c.parameters.x := by
        rw [←hcard,hmu]
        nlinarith
      exact ⟨fun _=>by linarith,fun _=>hstrong⟩
  · exact ⟨fun hh=>(hpos hh).elim,fun hh=>(hpos (by omega)).elim⟩

/-- The certified activity-point density holds for every induced forest
with at least eight vertices. -/
theorem Certificate.forest_density {c : Certificate} (hc : c.Valid)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (c.parameters.r:ℝ)*S.card+c.parameters.h≤hardCoreMean G S c.parameters.x := by
  classical
  have hx : (0:ℝ)≤c.parameters.x := by exact_mod_cast hc.1.1
  have hhB : (c.parameters.h:ℝ)≤c.parameters.B := by exact_mod_cast hc.2.2.2.2.1
  have hhs : (c.parameters.h:ℝ)≤2*c.parameters.s := by exact_mod_cast hc.2.2.2.2.2.1
  by_cases hconn : (G.induce (S:Set V)).Connected
  · by_cases hdeg : ∀v∈S,degreeOn G S v≤2
    · exact path_density_of_degrees hc.2.2.2.2.2.2.2.2 G hG S (card_pos.mp (by omega)) hconn hdeg hn
    · push Not at hdeg
      obtain ⟨v,hv,hd⟩:=hdeg
      obtain ⟨root,hfan⟩:=exists_rootedFan_of_tree G hG S hv hconn
      have hh:=fan_density hc.1 hfan (by rw [←hfan.unitActivity_degree_center]; omega)
        (by intro i _; exact deletedCenterBranch_connected G S v i) hG
        (by intro T _ _ ht; exact (Certificate.forest_intercepts hc G hG T).2 ht)
      linarith
  · obtain ⟨A,B,_,_,hA,hB,_,_,hdis,hu,hcross⟩:=
      UnitActivityForestDensity.exists_disconnected_split G S (card_pos.mp (by omega)) hconn
    have hmuA:=(Certificate.forest_intercepts hc G hG A).1 (card_pos.mpr hA)
    have hmuB:=(Certificate.forest_intercepts hc G hG B).1 (card_pos.mpr hB)
    have hmu:=hardCoreMean_disjoint_union G A B hdis hcross hx
    have hcard : (A.card:ℝ)+B.card=S.card := by
      exact_mod_cast ((card_union_of_disjoint hdis).symm.trans (congrArg Finset.card hu))
    rw [hu] at hmu
    rw [←hcard,hmu]
    nlinarith

#print axioms Certificate.forest_intercepts
#print axioms Certificate.forest_density
end ForestUnimodality.ActivityPointDensity

