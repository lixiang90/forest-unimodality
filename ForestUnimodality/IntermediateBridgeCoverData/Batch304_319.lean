import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band304 : Band CellKey where
  qlo := (11311/21736)
  qhi := (22647/43472)
  mlo := (8158078332670993950633638009449/500000000000000000000000000000)
  mhi := (23003324035216837722499703430953/500000000000000000000000000000)
  cells := [(59,144),(59,145),(99,104),(99,105),(130,109),(130,110)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 76

theorem band304_checked : band304.check rectangle=true := by decide +kernel
#print axioms band304_checked

def band305 : Band CellKey where
  qlo := (11311/21736)
  qhi := (22647/43472)
  mlo := (22074800194286218925243961672627/1000000000000000000000000000000)
  mhi := (23003324035216837722499703430953/500000000000000000000000000000)
  cells := [(80,115),(80,116),(99,104),(99,105),(130,109),(130,110)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 76

theorem band305_checked : band305.check rectangle=true := by decide +kernel
#print axioms band305_checked

def band306 : Band CellKey where
  qlo := (11311/21736)
  qhi := (22647/43472)
  mlo := (6958360930807612487305161831589/250000000000000000000000000000)
  mhi := (23003324035216837722499703430953/500000000000000000000000000000)
  cells := [(99,104),(99,105),(130,109),(130,110)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 76

theorem band306_checked : band306.check rectangle=true := by decide +kernel
#print axioms band306_checked

def band307 : Band CellKey where
  qlo := (11311/21736)
  qhi := (22647/43472)
  mlo := (35511635095156091314522894864661/1000000000000000000000000000000)
  mhi := (23003324035216837722499703430953/500000000000000000000000000000)
  cells := [(130,109),(130,110)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 76

theorem band307_checked : band307.check rectangle=true := by decide +kernel
#print axioms band307_checked

def band308 : Band CellKey where
  qlo := (22647/43472)
  qhi := (109/209)
  mlo := (16298165137614678899082568807339/1000000000000000000000000000000)
  mhi := (9196260749079419816523436368153/200000000000000000000000000000)
  cells := [(59,146),(59,147),(99,106),(99,107),(130,111),(130,112)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 77

theorem band308_checked : band308.check rectangle=true := by decide +kernel
#print axioms band308_checked

def band309 : Band CellKey where
  qlo := (22647/43472)
  qhi := (109/209)
  mlo := (4410091743119266055045871559633/200000000000000000000000000000)
  mhi := (9196260749079419816523436368153/200000000000000000000000000000)
  cells := [(80,117),(80,118),(99,106),(99,107),(130,111),(130,112)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 77

theorem band309_checked : band309.check rectangle=true := by decide +kernel
#print axioms band309_checked

def band310 : Band CellKey where
  qlo := (22647/43472)
  qhi := (109/209)
  mlo := (2780275229357798165137614678899/100000000000000000000000000000)
  mhi := (9196260749079419816523436368153/200000000000000000000000000000)
  cells := [(99,106),(99,107),(130,111),(130,112)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 77

theorem band310_checked : band310.check rectangle=true := by decide +kernel
#print axioms band310_checked

def band311 : Band CellKey where
  qlo := (22647/43472)
  qhi := (109/209)
  mlo := (35472477064220183486238532110091/1000000000000000000000000000000)
  mhi := (9196260749079419816523436368153/200000000000000000000000000000)
  cells := [(130,111),(130,112)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 77

theorem band311_checked : band311.check rectangle=true := by decide +kernel
#print axioms band311_checked

def band312 : Band CellKey where
  qlo := (109/209)
  qhi := (4583/8778)
  mlo := (2035048003491162993672267073969/125000000000000000000000000000)
  mhi := (45956483350563251027080466620827/1000000000000000000000000000000)
  cells := [(59,148),(59,149),(99,108),(99,109),(130,113),(130,114)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 78

theorem band312_checked : band312.check rectangle=true := by decide +kernel
#print axioms band312_checked

def band313 : Band CellKey where
  qlo := (109/209)
  qhi := (4583/8778)
  mlo := (11013200960069823259873445341479/500000000000000000000000000000)
  mhi := (45956483350563251027080466620827/1000000000000000000000000000000)
  cells := [(80,119),(80,120),(99,108),(99,109),(130,113),(130,114)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 78

theorem band313_checked : band313.check rectangle=true := by decide +kernel
#print axioms band313_checked

def band314 : Band CellKey where
  qlo := (109/209)
  qhi := (4583/8778)
  mlo := (5554483962469997818023128954833/200000000000000000000000000000)
  mhi := (45956483350563251027080466620827/1000000000000000000000000000000)
  cells := [(99,108),(99,109),(130,113),(130,114)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 78

theorem band314_checked : band314.check rectangle=true := by decide +kernel
#print axioms band314_checked

def band315 : Band CellKey where
  qlo := (109/209)
  qhi := (4583/8778)
  mlo := (35433777001963779183940650229107/1000000000000000000000000000000)
  mhi := (45956483350563251027080466620827/1000000000000000000000000000000)
  cells := [(130,113),(130,114)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 78

theorem band315_checked : band315.check rectangle=true := by decide +kernel
#print axioms band315_checked

def band316 : Band CellKey where
  qlo := (4583/8778)
  qhi := (2294/4389)
  mlo := (4065660418482999128160418482999/250000000000000000000000000000)
  mhi := (45931462183586076924937248603351/1000000000000000000000000000000)
  cells := [(59,150),(59,151),(99,110),(99,111),(130,115),(130,116)]
  lowerOrder := 59
  orderCap := 79
  rank := 17
  parentStrip := 79

theorem band316_checked : band316.check rectangle=true := by decide +kernel
#print axioms band316_checked

def band317 : Band CellKey where
  qlo := (4583/8778)
  qhi := (2294/4389)
  mlo := (22002397558849171752397558849171/1000000000000000000000000000000)
  mhi := (45931462183586076924937248603351/1000000000000000000000000000000)
  cells := [(80,121),(80,122),(99,110),(99,111),(130,115),(130,116)]
  lowerOrder := 80
  orderCap := 98
  rank := 23
  parentStrip := 79

theorem band317_checked : band317.check rectangle=true := by decide +kernel
#print axioms band317_checked

def band318 : Band CellKey where
  qlo := (4583/8778)
  qhi := (2294/4389)
  mlo := (13871076721883173496076721883173/500000000000000000000000000000)
  mhi := (45931462183586076924937248603351/1000000000000000000000000000000)
  cells := [(99,110),(99,111),(130,115),(130,116)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 79

theorem band318_checked : band318.check rectangle=true := by decide +kernel
#print axioms band318_checked

def band319 : Band CellKey where
  qlo := (4583/8778)
  qhi := (2294/4389)
  mlo := (1769758064516129032258064516129/50000000000000000000000000000)
  mhi := (45931462183586076924937248603351/1000000000000000000000000000000)
  cells := [(130,115),(130,116)]
  lowerOrder := 130
  orderCap := 169
  rank := 37
  parentStrip := 79

theorem band319_checked : band319.check rectangle=true := by decide +kernel
#print axioms band319_checked

end ForestUnimodality.IntermediateBridgeCoverData

