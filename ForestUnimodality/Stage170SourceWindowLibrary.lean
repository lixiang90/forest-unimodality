import ForestUnimodality.Stage170SourceData.Windows.Batch000_019
import ForestUnimodality.Stage170SourceData.Windows.Batch020_039
import ForestUnimodality.Stage170SourceData.Windows.Batch040_059
import ForestUnimodality.Stage170SourceData.Windows.Batch060_079
import ForestUnimodality.Stage170SourceData.Windows.Batch080_099
import ForestUnimodality.Stage170SourceData.Windows.Batch100_119
import ForestUnimodality.Stage170SourceData.Windows.Batch120_139
import ForestUnimodality.Stage170SourceData.Windows.Batch140_146

/-! Lightweight complete window catalogue. It is independent of rate and
residual data. All windows retain exact frozen rational parameters. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.Stage170SourceLibrary
open FiniteSourceWindow Stage170SourceData

def window (i : Fin 147) : Window :=
  ![Window000.window, Window001.window, Window002.window, Window003.window, Window004.window, Window005.window, Window006.window, Window007.window, Window008.window, Window009.window, Window010.window, Window011.window, Window012.window, Window013.window, Window014.window, Window015.window, Window016.window, Window017.window, Window018.window, Window019.window, Window020.window, Window021.window, Window022.window, Window023.window, Window024.window, Window025.window, Window026.window, Window027.window, Window028.window, Window029.window, Window030.window, Window031.window, Window032.window, Window033.window, Window034.window, Window035.window, Window036.window, Window037.window, Window038.window, Window039.window, Window040.window, Window041.window, Window042.window, Window043.window, Window044.window, Window045.window, Window046.window, Window047.window, Window048.window, Window049.window, Window050.window, Window051.window, Window052.window, Window053.window, Window054.window, Window055.window, Window056.window, Window057.window, Window058.window, Window059.window, Window060.window, Window061.window, Window062.window, Window063.window, Window064.window, Window065.window, Window066.window, Window067.window, Window068.window, Window069.window, Window070.window, Window071.window, Window072.window, Window073.window, Window074.window, Window075.window, Window076.window, Window077.window, Window078.window, Window079.window, Window080.window, Window081.window, Window082.window, Window083.window, Window084.window, Window085.window, Window086.window, Window087.window, Window088.window, Window089.window, Window090.window, Window091.window, Window092.window, Window093.window, Window094.window, Window095.window, Window096.window, Window097.window, Window098.window, Window099.window, Window100.window, Window101.window, Window102.window, Window103.window, Window104.window, Window105.window, Window106.window, Window107.window, Window108.window, Window109.window, Window110.window, Window111.window, Window112.window, Window113.window, Window114.window, Window115.window, Window116.window, Window117.window, Window118.window, Window119.window, Window120.window, Window121.window, Window122.window, Window123.window, Window124.window, Window125.window, Window126.window, Window127.window, Window128.window, Window129.window, Window130.window, Window131.window, Window132.window, Window133.window, Window134.window, Window135.window, Window136.window, Window137.window, Window138.window, Window139.window, Window140.window, Window141.window, Window142.window, Window143.window, Window144.window, Window145.window, Window146.window] i

theorem window_valid (i : Fin 147) : (window i).Valid := by
  fin_cases i
  · exact Window000.valid
  · exact Window001.valid
  · exact Window002.valid
  · exact Window003.valid
  · exact Window004.valid
  · exact Window005.valid
  · exact Window006.valid
  · exact Window007.valid
  · exact Window008.valid
  · exact Window009.valid
  · exact Window010.valid
  · exact Window011.valid
  · exact Window012.valid
  · exact Window013.valid
  · exact Window014.valid
  · exact Window015.valid
  · exact Window016.valid
  · exact Window017.valid
  · exact Window018.valid
  · exact Window019.valid
  · exact Window020.valid
  · exact Window021.valid
  · exact Window022.valid
  · exact Window023.valid
  · exact Window024.valid
  · exact Window025.valid
  · exact Window026.valid
  · exact Window027.valid
  · exact Window028.valid
  · exact Window029.valid
  · exact Window030.valid
  · exact Window031.valid
  · exact Window032.valid
  · exact Window033.valid
  · exact Window034.valid
  · exact Window035.valid
  · exact Window036.valid
  · exact Window037.valid
  · exact Window038.valid
  · exact Window039.valid
  · exact Window040.valid
  · exact Window041.valid
  · exact Window042.valid
  · exact Window043.valid
  · exact Window044.valid
  · exact Window045.valid
  · exact Window046.valid
  · exact Window047.valid
  · exact Window048.valid
  · exact Window049.valid
  · exact Window050.valid
  · exact Window051.valid
  · exact Window052.valid
  · exact Window053.valid
  · exact Window054.valid
  · exact Window055.valid
  · exact Window056.valid
  · exact Window057.valid
  · exact Window058.valid
  · exact Window059.valid
  · exact Window060.valid
  · exact Window061.valid
  · exact Window062.valid
  · exact Window063.valid
  · exact Window064.valid
  · exact Window065.valid
  · exact Window066.valid
  · exact Window067.valid
  · exact Window068.valid
  · exact Window069.valid
  · exact Window070.valid
  · exact Window071.valid
  · exact Window072.valid
  · exact Window073.valid
  · exact Window074.valid
  · exact Window075.valid
  · exact Window076.valid
  · exact Window077.valid
  · exact Window078.valid
  · exact Window079.valid
  · exact Window080.valid
  · exact Window081.valid
  · exact Window082.valid
  · exact Window083.valid
  · exact Window084.valid
  · exact Window085.valid
  · exact Window086.valid
  · exact Window087.valid
  · exact Window088.valid
  · exact Window089.valid
  · exact Window090.valid
  · exact Window091.valid
  · exact Window092.valid
  · exact Window093.valid
  · exact Window094.valid
  · exact Window095.valid
  · exact Window096.valid
  · exact Window097.valid
  · exact Window098.valid
  · exact Window099.valid
  · exact Window100.valid
  · exact Window101.valid
  · exact Window102.valid
  · exact Window103.valid
  · exact Window104.valid
  · exact Window105.valid
  · exact Window106.valid
  · exact Window107.valid
  · exact Window108.valid
  · exact Window109.valid
  · exact Window110.valid
  · exact Window111.valid
  · exact Window112.valid
  · exact Window113.valid
  · exact Window114.valid
  · exact Window115.valid
  · exact Window116.valid
  · exact Window117.valid
  · exact Window118.valid
  · exact Window119.valid
  · exact Window120.valid
  · exact Window121.valid
  · exact Window122.valid
  · exact Window123.valid
  · exact Window124.valid
  · exact Window125.valid
  · exact Window126.valid
  · exact Window127.valid
  · exact Window128.valid
  · exact Window129.valid
  · exact Window130.valid
  · exact Window131.valid
  · exact Window132.valid
  · exact Window133.valid
  · exact Window134.valid
  · exact Window135.valid
  · exact Window136.valid
  · exact Window137.valid
  · exact Window138.valid
  · exact Window139.valid
  · exact Window140.valid
  · exact Window141.valid
  · exact Window142.valid
  · exact Window143.valid
  · exact Window144.valid
  · exact Window145.valid
  · exact Window146.valid

#print axioms window_valid
end ForestUnimodality.Stage170SourceLibrary
