import ForestUnimodality.Stage170Windows.ThroughStrip004
import ForestUnimodality.Stage170Windows.Strip005.Complete
import ForestUnimodality.Stage170Windows.Strip006.Complete
import ForestUnimodality.Stage170Windows.Strip007.Complete
import ForestUnimodality.Stage170Windows.Strip008.Complete
import ForestUnimodality.Stage170Windows.Strip009.Complete
import ForestUnimodality.Stage170Windows.Strip010.Complete
import ForestUnimodality.Stage170Windows.Strip011.Complete
import ForestUnimodality.Stage170Windows.Strip012.Complete
import ForestUnimodality.Stage170Windows.Strip013.Complete
import ForestUnimodality.Stage170Windows.Strip014.Complete
import ForestUnimodality.Stage170Windows.Strip015.Complete
import ForestUnimodality.Stage170Windows.Strip016.Complete
import ForestUnimodality.Stage170Windows.Strip017.Complete
import ForestUnimodality.Stage170Windows.Strip018.Complete
import ForestUnimodality.Stage170Windows.Strip019.Complete
import ForestUnimodality.Stage170Windows.Strip020.Complete
import ForestUnimodality.Stage170Windows.Strip021.Complete
import ForestUnimodality.Stage170Windows.Strip022.Complete
import ForestUnimodality.Stage170Windows.Strip023.Complete
import ForestUnimodality.Stage170Windows.Strip024.Complete
import ForestUnimodality.Stage170Windows.Strip025.Complete
import ForestUnimodality.Stage170Windows.Strip026.Complete
import ForestUnimodality.Stage170Windows.Strip027.Complete
import ForestUnimodality.Stage170Windows.Strip028.Complete
import ForestUnimodality.Stage170Windows.Strip029.Complete
import ForestUnimodality.Stage170Windows.Strip030.Complete
import ForestUnimodality.Stage170Windows.Strip031.Complete
import ForestUnimodality.Stage170Windows.Strip032.Complete
import ForestUnimodality.Stage170Windows.Strip033.Complete
import ForestUnimodality.Stage170Windows.Strip034.Complete
import ForestUnimodality.Stage170Windows.Strip035.Complete
import ForestUnimodality.Stage170Windows.Strip036.Complete
import ForestUnimodality.Stage170Windows.Strip037.Complete
import ForestUnimodality.Stage170Windows.Strip038.Complete
import ForestUnimodality.Stage170Windows.Strip039.Complete
import ForestUnimodality.Stage170Windows.Strip040.Complete
import ForestUnimodality.Stage170Windows.Strip041.Complete
import ForestUnimodality.Stage170Windows.Strip042.Complete
import ForestUnimodality.Stage170Windows.Strip043.Complete
import ForestUnimodality.Stage170Windows.Strip044.Complete
import ForestUnimodality.Stage170Windows.Strip045.Complete
import ForestUnimodality.Stage170Windows.Strip046.Complete
import ForestUnimodality.Stage170Windows.Strip047.Complete
import ForestUnimodality.Stage170Windows.Strip048.Complete
import ForestUnimodality.Stage170Windows.Strip049.Complete
import ForestUnimodality.Stage170Windows.Strip050.Complete
import ForestUnimodality.Stage170Windows.Strip051.Complete
import ForestUnimodality.Stage170Windows.Strip052.Complete
import ForestUnimodality.Stage170Windows.Strip053.Complete
import ForestUnimodality.Stage170Windows.Strip054.Complete
import ForestUnimodality.Stage170Windows.Strip055.Complete
import ForestUnimodality.Stage170Windows.Strip056.Complete
import ForestUnimodality.Stage170Windows.Strip057.Complete
import ForestUnimodality.Stage170Windows.Strip058.Complete
import ForestUnimodality.Stage170Windows.Strip059.Complete
import ForestUnimodality.Stage170Windows.Strip060.Complete
import ForestUnimodality.Stage170Windows.Strip061.Complete
import ForestUnimodality.Stage170Windows.Strip062.Complete
import ForestUnimodality.Stage170Windows.Strip063.Complete
import ForestUnimodality.Stage170Windows.Strip064.Complete
import ForestUnimodality.Stage170Windows.Strip065.Complete
import ForestUnimodality.Stage170Windows.Strip066.Complete
import ForestUnimodality.Stage170Windows.Strip067.Complete
import ForestUnimodality.Stage170Windows.Strip068.Complete
import ForestUnimodality.Stage170Windows.Strip069.Complete
import ForestUnimodality.Stage170Windows.Strip070.Complete
import ForestUnimodality.Stage170Windows.Strip071.Complete
import ForestUnimodality.Stage170Windows.Strip072.Complete
import ForestUnimodality.Stage170Windows.Strip073.Complete
import ForestUnimodality.Stage170Windows.Strip074.Complete
import ForestUnimodality.Stage170Windows.Strip075.Complete
import ForestUnimodality.Stage170Windows.Strip076.Complete
import ForestUnimodality.Stage170Windows.Strip077.Complete
import ForestUnimodality.Stage170Windows.Strip078.Complete
import ForestUnimodality.Stage170Windows.Strip079.Complete
import ForestUnimodality.Stage170Windows.Strip080.Complete
import ForestUnimodality.Stage170Windows.Strip081.Complete
import ForestUnimodality.Stage170Windows.Strip082.Complete
import ForestUnimodality.Stage170Windows.Strip083.Complete
import ForestUnimodality.Stage170Windows.Strip084.Complete
import ForestUnimodality.Stage170Windows.Strip085.Complete
import ForestUnimodality.Stage170Windows.Strip086.Complete
import ForestUnimodality.Stage170Windows.Strip087.Complete
import ForestUnimodality.Stage170Windows.Strip088.Complete
import ForestUnimodality.Stage170Windows.Strip089.Complete
import ForestUnimodality.Stage170Windows.Strip090.Complete
import ForestUnimodality.Stage170Windows.Strip091.Complete
import ForestUnimodality.Stage170Windows.Strip092.Complete
import ForestUnimodality.Stage170Windows.Strip093.Complete
import ForestUnimodality.Stage170Windows.Strip094.Complete
import ForestUnimodality.Stage170Windows.Strip095.Complete
import ForestUnimodality.Stage170Windows.Strip096.Complete
import ForestUnimodality.Stage170Windows.Strip097.Complete
import ForestUnimodality.Stage170Windows.Strip098.Complete
import ForestUnimodality.Stage170Windows.Strip099.Complete
import ForestUnimodality.Stage170Windows.Strip100.Complete
import ForestUnimodality.Stage170Windows.Strip101.Complete
import ForestUnimodality.Stage170Windows.Strip102.Complete
import ForestUnimodality.Stage170Windows.Strip103.Complete

namespace ForestUnimodality.Stage170Windows.ThroughStrip103
variable {V : Type*} [DecidableEq V]
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem no_weak_valley {G : SimpleGraph V} {S : Finset V} {z : ℝ}
    (k : ℕ) (hG : G.IsAcyclic) (hn : 170≤S.card) (hN : S.card≤349) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (1/4:ℝ) (99/179:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (hmean : hardCoreMean G S z=k) :
    ¬ (countIndependent G S k≤countIndependent G S (k-1) ∧
       countIndependent G S k≤countIndependent G S (k+1)) := by
  by_cases h4 : z/(1+z)≤(2/7:ℝ)
  · exact ThroughStrip004.no_weak_valley k hG hn hN hz ⟨hq.1,h4⟩ hrank hmean
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
  by_cases h31 : z/(1+z)≤(841/1786:ℝ)
  · exact Strip031.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h30).le,h31⟩ hrank hmean
  by_cases h32 : z/(1+z)≤(1687/3572:ℝ)
  · exact Strip032.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h31).le,h32⟩ hrank hmean
  by_cases h33 : z/(1+z)≤(9/19:ℝ)
  · exact Strip033.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h32).le,h33⟩ hrank hmean
  by_cases h34 : z/(1+z)≤(1733/3648:ℝ)
  · exact Strip034.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h33).le,h34⟩ hrank hmean
  by_cases h35 : z/(1+z)≤(869/1824:ℝ)
  · exact Strip035.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h34).le,h35⟩ hrank hmean
  by_cases h36 : z/(1+z)≤(581/1216:ℝ)
  · exact Strip036.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h35).le,h36⟩ hrank hmean
  by_cases h37 : z/(1+z)≤(23/48:ℝ)
  · exact Strip037.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h36).le,h37⟩ hrank hmean
  by_cases h38 : z/(1+z)≤(2983/6208:ℝ)
  · exact Strip038.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h37).le,h38⟩ hrank hmean
  by_cases h39 : z/(1+z)≤(4487/9312:ℝ)
  · exact Strip039.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h38).le,h39⟩ hrank hmean
  by_cases h40 : z/(1+z)≤(8999/18624:ℝ)
  · exact Strip040.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h39).le,h40⟩ hrank hmean
  by_cases h41 : z/(1+z)≤(47/97:ℝ)
  · exact Strip041.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h40).le,h41⟩ hrank hmean
  by_cases h42 : z/(1+z)≤(9237/19012:ℝ)
  · exact Strip042.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h41).le,h42⟩ hrank hmean
  by_cases h43 : z/(1+z)≤(4631/9506:ℝ)
  · exact Strip043.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h42).le,h43⟩ hrank hmean
  by_cases h44 : z/(1+z)≤(9287/19012:ℝ)
  · exact Strip044.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h43).le,h44⟩ hrank hmean
  by_cases h45 : z/(1+z)≤(24/49:ℝ)
  · exact Strip045.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h44).le,h45⟩ hrank hmean
  by_cases h46 : z/(1+z)≤(9529/19404:ℝ)
  · exact Strip046.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h45).le,h46⟩ hrank hmean
  by_cases h47 : z/(1+z)≤(4777/9702:ℝ)
  · exact Strip047.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h46).le,h47⟩ hrank hmean
  by_cases h48 : z/(1+z)≤(3193/6468:ℝ)
  · exact Strip048.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h47).le,h48⟩ hrank hmean
  by_cases h49 : z/(1+z)≤(49/99:ℝ)
  · exact Strip049.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h48).le,h49⟩ hrank hmean
  by_cases h50 : z/(1+z)≤(131/264:ℝ)
  · exact Strip050.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h49).le,h50⟩ hrank hmean
  by_cases h51 : z/(1+z)≤(197/396:ℝ)
  · exact Strip051.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h50).le,h51⟩ hrank hmean
  by_cases h52 : z/(1+z)≤(395/792:ℝ)
  · exact Strip052.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h51).le,h52⟩ hrank hmean
  by_cases h53 : z/(1+z)≤(1/2:ℝ)
  · exact Strip053.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h52).le,h53⟩ hrank hmean
  by_cases h54 : z/(1+z)≤(405/808:ℝ)
  · exact Strip054.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h53).le,h54⟩ hrank hmean
  by_cases h55 : z/(1+z)≤(203/404:ℝ)
  · exact Strip055.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h54).le,h55⟩ hrank hmean
  by_cases h56 : z/(1+z)≤(407/808:ℝ)
  · exact Strip056.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h55).le,h56⟩ hrank hmean
  by_cases h57 : z/(1+z)≤(51/101:ℝ)
  · exact Strip057.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h56).le,h57⟩ hrank hmean
  by_cases h58 : z/(1+z)≤(10429/20604:ℝ)
  · exact Strip058.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h57).le,h58⟩ hrank hmean
  by_cases h59 : z/(1+z)≤(5227/10302:ℝ)
  · exact Strip059.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h58).le,h59⟩ hrank hmean
  by_cases h60 : z/(1+z)≤(3493/6868:ℝ)
  · exact Strip060.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h59).le,h60⟩ hrank hmean
  by_cases h61 : z/(1+z)≤(26/51:ℝ)
  · exact Strip061.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h60).le,h61⟩ hrank hmean
  by_cases h62 : z/(1+z)≤(3579/7004:ℝ)
  · exact Strip062.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h61).le,h62⟩ hrank hmean
  by_cases h63 : z/(1+z)≤(5381/10506:ℝ)
  · exact Strip063.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h62).le,h63⟩ hrank hmean
  by_cases h64 : z/(1+z)≤(10787/21012:ℝ)
  · exact Strip064.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h63).le,h64⟩ hrank hmean
  by_cases h65 : z/(1+z)≤(53/103:ℝ)
  · exact Strip065.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h64).le,h65⟩ hrank hmean
  by_cases h66 : z/(1+z)≤(21967/42642:ℝ)
  · exact Strip066.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h65).le,h66⟩ hrank hmean
  by_cases h67 : z/(1+z)≤(10996/21321:ℝ)
  · exact Strip067.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h66).le,h67⟩ hrank hmean
  by_cases h68 : z/(1+z)≤(7339/14214:ℝ)
  · exact Strip068.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h67).le,h68⟩ hrank hmean
  by_cases h69 : z/(1+z)≤(107/207:ℝ)
  · exact Strip069.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h68).le,h69⟩ hrank hmean
  by_cases h70 : z/(1+z)≤(7427/14352:ℝ)
  · exact Strip070.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h69).le,h70⟩ hrank hmean
  by_cases h71 : z/(1+z)≤(11153/21528:ℝ)
  · exact Strip071.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h70).le,h71⟩ hrank hmean
  by_cases h72 : z/(1+z)≤(22331/43056:ℝ)
  · exact Strip072.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h71).le,h72⟩ hrank hmean
  by_cases h73 : z/(1+z)≤(27/52:ℝ)
  · exact Strip073.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h72).le,h73⟩ hrank hmean
  by_cases h74 : z/(1+z)≤(22597/43472:ℝ)
  · exact Strip074.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h73).le,h74⟩ hrank hmean
  by_cases h75 : z/(1+z)≤(11311/21736:ℝ)
  · exact Strip075.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h74).le,h75⟩ hrank hmean
  by_cases h76 : z/(1+z)≤(22647/43472:ℝ)
  · exact Strip076.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h75).le,h76⟩ hrank hmean
  by_cases h77 : z/(1+z)≤(109/209:ℝ)
  · exact Strip077.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h76).le,h77⟩ hrank hmean
  by_cases h78 : z/(1+z)≤(4583/8778:ℝ)
  · exact Strip078.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h77).le,h78⟩ hrank hmean
  by_cases h79 : z/(1+z)≤(2294/4389:ℝ)
  · exact Strip079.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h78).le,h79⟩ hrank hmean
  by_cases h80 : z/(1+z)≤(1531/2926:ℝ)
  · exact Strip080.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h79).le,h80⟩ hrank hmean
  by_cases h81 : z/(1+z)≤(11/21:ℝ)
  · exact Strip081.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h80).le,h81⟩ hrank hmean
  by_cases h82 : z/(1+z)≤(1549/2954:ℝ)
  · exact Strip082.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h81).le,h82⟩ hrank hmean
  by_cases h83 : z/(1+z)≤(2326/4431:ℝ)
  · exact Strip083.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h82).le,h83⟩ hrank hmean
  by_cases h84 : z/(1+z)≤(4657/8862:ℝ)
  · exact Strip084.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h83).le,h84⟩ hrank hmean
  by_cases h85 : z/(1+z)≤(111/211:ℝ)
  · exact Strip085.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h84).le,h85⟩ hrank hmean
  by_cases h86 : z/(1+z)≤(23557/44732:ℝ)
  · exact Strip086.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h85).le,h86⟩ hrank hmean
  by_cases h87 : z/(1+z)≤(11791/22366:ℝ)
  · exact Strip087.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h86).le,h87⟩ hrank hmean
  by_cases h88 : z/(1+z)≤(23607/44732:ℝ)
  · exact Strip088.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h87).le,h88⟩ hrank hmean
  by_cases h89 : z/(1+z)≤(28/53:ℝ)
  · exact Strip089.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h88).le,h89⟩ hrank hmean
  by_cases h90 : z/(1+z)≤(23881/45156:ℝ)
  · exact Strip090.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h89).le,h90⟩ hrank hmean
  by_cases h91 : z/(1+z)≤(11953/22578:ℝ)
  · exact Strip091.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h90).le,h91⟩ hrank hmean
  by_cases h92 : z/(1+z)≤(7977/15052:ℝ)
  · exact Strip092.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h91).le,h92⟩ hrank hmean
  by_cases h93 : z/(1+z)≤(113/213:ℝ)
  · exact Strip093.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h92).le,h93⟩ hrank hmean
  by_cases h94 : z/(1+z)≤(8069/15194:ℝ)
  · exact Strip094.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h93).le,h94⟩ hrank hmean
  by_cases h95 : z/(1+z)≤(12116/22791:ℝ)
  · exact Strip095.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h94).le,h95⟩ hrank hmean
  by_cases h96 : z/(1+z)≤(24257/45582:ℝ)
  · exact Strip096.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h95).le,h96⟩ hrank hmean
  by_cases h97 : z/(1+z)≤(57/107:ℝ)
  · exact Strip097.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h96).le,h97⟩ hrank hmean
  by_cases h98 : z/(1+z)≤(29/54:ℝ)
  · exact Strip098.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h97).le,h98⟩ hrank hmean
  by_cases h99 : z/(1+z)≤(643/1188:ℝ)
  · exact Strip099.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h98).le,h99⟩ hrank hmean
  by_cases h100 : z/(1+z)≤(6/11:ℝ)
  · exact Strip100.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h99).le,h100⟩ hrank hmean
  by_cases h101 : z/(1+z)≤(97/177:ℝ)
  · exact Strip101.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h100).le,h101⟩ hrank hmean
  by_cases h102 : z/(1+z)≤(49/89:ℝ)
  · exact Strip102.no_weak_valley k hG hn hN hz
      ⟨(lt_of_not_ge h101).le,h102⟩ hrank hmean
  exact Strip103.no_weak_valley k hG hn hN hz
    ⟨(lt_of_not_ge h102).le,hq.2⟩ hrank hmean

#print axioms no_weak_valley
end ForestUnimodality.Stage170Windows.ThroughStrip103
