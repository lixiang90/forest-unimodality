import ForestUnimodality.IntermediateBridgeAssembly
import ForestUnimodality.Stage170Windows.ThroughStrip129

/-! Close the full order range n >= 170 using the complete activity window.
The finite rectangle obligations for smaller forests do not occur as premises. -/
namespace ForestUnimodality
variable {V : Type*} [DecidableEq V]

theorem countIndependent_unimodal_of_card_ge170
    (G : SimpleGraph V) (S : Finset V) (hG : G.IsAcyclic) (hn : 170 ≤ S.card) :
    WeaklyUnimodal (countIndependent G S) := by
  by_cases hlarge : 350 ≤ S.card
  · exact countIndependent_unimodal_of_card_ge350 G S hG hlarge
  obtain ⟨I,hI⟩ := exists_maximumIndependentOn G S
  apply weaklyUnimodal_of_no_central_weak_valley (countIndependent G S)
    ((S.card+3)/4) ((S.card+2*I.card)/6+1)
    (countIndependent_le_succ_of_quarter G hG S)
    (hI.countIndependent_succ_le_of_matching_tail hG)
  intro k hkL hkU hkpos hvalley
  obtain ⟨z,⟨hz,hmean⟩,_⟩ := hI.existsUnique_central_activity hG k hkL hkU hkpos
  have hz0 : 0<z := lt_of_lt_of_le (by norm_num) hz.1
  have hrank : (S.card:ℝ)/4≤hardCoreMean G S z := by
    have hk : S.card≤4*k := by omega
    have hkR : (S.card:ℝ)≤4*(k:ℝ) := by exact_mod_cast hk
    rw [hmean]
    linarith
  have hq : z/(1+z)∈Set.Icc (1/4:ℝ) (9/13:ℝ) := by
    constructor
    · apply (le_div_iff₀ (by positivity : (0:ℝ)<1+z)).mpr
      linarith [hz.1]
    · apply (div_le_iff₀ (by positivity : (0:ℝ)<1+z)).mpr
      linarith [hz.2]
  exact Stage170Windows.ThroughStrip129.no_weak_valley k hG hn (by omega)
    hz0 hq hrank hmean hvalley

theorem independentCount_unimodal_of_card_ge170
    {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.IsAcyclic) (hn : 170 ≤ n) :
    WeaklyUnimodal (independentCount G) := by
  classical
  have h := countIndependent_unimodal_of_card_ge170 G Finset.univ hG (by simpa using hn)
  simpa only [WeaklyUnimodal,countIndependent_univ_eq_independentCount] using h

#print axioms countIndependent_unimodal_of_card_ge170
#print axioms independentCount_unimodal_of_card_ge170
end ForestUnimodality
