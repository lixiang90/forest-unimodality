import ForestUnimodality.BridgeInitialActivity
import ForestUnimodality.BridgeActivityData.Strip002
import ForestUnimodality.BridgeActivityData.Strip003
import ForestUnimodality.BridgeActivityData.Strip004
import ForestUnimodality.BridgeActivityData.Strip005
import ForestUnimodality.BridgeActivityData.Strip006
import ForestUnimodality.BridgeActivityData.Strip007
import ForestUnimodality.BridgeActivityData.Strip008
import ForestUnimodality.BridgeActivityData.Strip009
import ForestUnimodality.BridgeActivityData.Strip010
import ForestUnimodality.BridgeActivityData.Strip011
import ForestUnimodality.BridgeActivityData.Strip012
import ForestUnimodality.BridgeActivityData.Strip013
import ForestUnimodality.BridgeActivityData.Strip014
import ForestUnimodality.BridgeActivityData.Strip015
import ForestUnimodality.BridgeActivityData.Strip016
import ForestUnimodality.BridgeActivityData.Strip017
import ForestUnimodality.BridgeActivityData.Strip018
import ForestUnimodality.BridgeActivityData.Strip019
import ForestUnimodality.BridgeActivityData.Strip020
import ForestUnimodality.BridgeActivityData.Strip021
import ForestUnimodality.BridgeActivityData.Strip022
import ForestUnimodality.BridgeActivityData.Strip023
import ForestUnimodality.BridgeActivityData.Strip024
import ForestUnimodality.BridgeActivityData.Strip025
import ForestUnimodality.BridgeActivityData.Strip026
import ForestUnimodality.BridgeActivityData.Strip027
import ForestUnimodality.BridgeActivityData.Strip028
import ForestUnimodality.BridgeActivityData.Strip029
import ForestUnimodality.BridgeActivityData.Strip030
import ForestUnimodality.BridgeActivityData.Strip031

/-! Consecutive activity coverage for orders59–349; not all-order unimodality. -/
namespace ForestUnimodality.BridgeActivityData.ThroughStrip031
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 59≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (841/1786:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases h1 : z/(1+z)≤(37/140:ℝ)
  · exact BridgeInitialActivity.no_weak_valley k hG hn hN hz ⟨hq.1,h1⟩ hrank hmean
  by_cases h2 : z/(1+z)≤(19/70:ℝ)
  · exact Strip002.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h1).le,h2⟩ hrank hmean
  by_cases h3 : z/(1+z)≤(39/140:ℝ)
  · exact Strip003.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h2).le,h3⟩ hrank hmean
  by_cases h4 : z/(1+z)≤(2/7:ℝ)
  · exact Strip004.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h3).le,h4⟩ hrank hmean
  by_cases h5 : z/(1+z)≤(37/126:ℝ)
  · exact Strip005.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h4).le,h5⟩ hrank hmean
  by_cases h6 : z/(1+z)≤(19/63:ℝ)
  · exact Strip006.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h5).le,h6⟩ hrank hmean
  by_cases h7 : z/(1+z)≤(13/42:ℝ)
  · exact Strip007.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h6).le,h7⟩ hrank hmean
  by_cases h8 : z/(1+z)≤(20/63:ℝ)
  · exact Strip008.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h7).le,h8⟩ hrank hmean
  by_cases h9 : z/(1+z)≤(41/126:ℝ)
  · exact Strip009.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h8).le,h9⟩ hrank hmean
  by_cases h10 : z/(1+z)≤(1/3:ℝ)
  · exact Strip010.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h9).le,h10⟩ hrank hmean
  by_cases h11 : z/(1+z)≤(29/85:ℝ)
  · exact Strip011.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h10).le,h11⟩ hrank hmean
  by_cases h12 : z/(1+z)≤(89/255:ℝ)
  · exact Strip012.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h11).le,h12⟩ hrank hmean
  by_cases h13 : z/(1+z)≤(91/255:ℝ)
  · exact Strip013.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h12).le,h13⟩ hrank hmean
  by_cases h14 : z/(1+z)≤(31/85:ℝ)
  · exact Strip014.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h13).le,h14⟩ hrank hmean
  by_cases h15 : z/(1+z)≤(19/51:ℝ)
  · exact Strip015.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h14).le,h15⟩ hrank hmean
  by_cases h16 : z/(1+z)≤(97/255:ℝ)
  · exact Strip016.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h15).le,h16⟩ hrank hmean
  by_cases h17 : z/(1+z)≤(33/85:ℝ)
  · exact Strip017.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h16).le,h17⟩ hrank hmean
  by_cases h18 : z/(1+z)≤(101/255:ℝ)
  · exact Strip018.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h17).le,h18⟩ hrank hmean
  by_cases h19 : z/(1+z)≤(103/255:ℝ)
  · exact Strip019.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h18).le,h19⟩ hrank hmean
  by_cases h20 : z/(1+z)≤(7/17:ℝ)
  · exact Strip020.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h19).le,h20⟩ hrank hmean
  by_cases h21 : z/(1+z)≤(64/153:ℝ)
  · exact Strip021.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h20).le,h21⟩ hrank hmean
  by_cases h22 : z/(1+z)≤(65/153:ℝ)
  · exact Strip022.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h21).le,h22⟩ hrank hmean
  by_cases h23 : z/(1+z)≤(22/51:ℝ)
  · exact Strip023.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h22).le,h23⟩ hrank hmean
  by_cases h24 : z/(1+z)≤(67/153:ℝ)
  · exact Strip024.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h23).le,h24⟩ hrank hmean
  by_cases h25 : z/(1+z)≤(4/9:ℝ)
  · exact Strip025.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h24).le,h25⟩ hrank hmean
  by_cases h26 : z/(1+z)≤(301/666:ℝ)
  · exact Strip026.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h25).le,h26⟩ hrank hmean
  by_cases h27 : z/(1+z)≤(17/37:ℝ)
  · exact Strip027.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h26).le,h27⟩ hrank hmean
  by_cases h28 : z/(1+z)≤(1613/3478:ℝ)
  · exact Strip028.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h27).le,h28⟩ hrank hmean
  by_cases h29 : z/(1+z)≤(22/47:ℝ)
  · exact Strip029.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h28).le,h29⟩ hrank hmean
  by_cases h30 : z/(1+z)≤(1677/3572:ℝ)
  · exact Strip030.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h29).le,h30⟩ hrank hmean
  exact Strip031.no_weak_valley k hG hn hN hz
    ⟨(lt_of_not_ge h30).le,hq.2⟩ hrank hmean

#print axioms no_weak_valley
end ForestUnimodality.BridgeActivityData.ThroughStrip031
