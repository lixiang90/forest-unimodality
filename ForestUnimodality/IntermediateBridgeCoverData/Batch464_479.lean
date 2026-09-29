import ForestUnimodality.IntermediateBridgeCoverData.Rectangles



namespace ForestUnimodality.IntermediateBridgeCoverData
open IntermediateBridgeCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0


def band464 : Band CellKey where
  qlo := (57/107)
  qhi := (29/54)
  mlo := (670344827586206896551724137931/40000000000000000000000000000)
  mhi := (9030925506363262813840774608633/200000000000000000000000000000)
  cells := [(59,193),(99,156),(130,211)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 98

theorem band464_checked : band464.check rectangle=true := by decide +kernel
#print axioms band464_checked

def band465 : Band CellKey where
  qlo := (57/107)
  qhi := (29/54)
  mlo := (11172413793103448275862068965517/500000000000000000000000000000)
  mhi := (9030925506363262813840774608633/200000000000000000000000000000)
  cells := [(80,173),(80,174),(80,175),(80,176),(99,156),(130,211)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 98

theorem band465_checked : band465.check rectangle=true := by decide +kernel
#print axioms band465_checked

def band466 : Band CellKey where
  qlo := (57/107)
  qhi := (29/54)
  mlo := (27/1)
  mhi := (9030925506363262813840774608633/200000000000000000000000000000)
  cells := [(99,156),(130,211)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 98

theorem band466_checked : band466.check rectangle=true := by decide +kernel
#print axioms band466_checked

def band467 : Band CellKey where
  qlo := (57/107)
  qhi := (29/54)
  mlo := (35379310344827586206896551724137/1000000000000000000000000000000)
  mhi := (9030925506363262813840774608633/200000000000000000000000000000)
  cells := [(130,211)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 98

theorem band467_checked : band467.check rectangle=true := by decide +kernel
#print axioms band467_checked

def band468 : Band CellKey where
  qlo := (29/54)
  qhi := (2557/4752)
  mlo := (8362925303089558075870160344153/500000000000000000000000000000)
  mhi := (44985085483857897875987910014081/1000000000000000000000000000000)
  cells := [(59,194),(99,157),(130,212)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 99

theorem band468_checked : band468.check rectangle=true := by decide +kernel
#print axioms band468_checked

def band469 : Band CellKey where
  qlo := (29/54)
  qhi := (2557/4752)
  mlo := (892045365662886194759483770043/40000000000000000000000000000)
  mhi := (44985085483857897875987910014081/1000000000000000000000000000000)
  cells := [(80,177),(80,178),(80,179),(80,180),(80,181),(99,157),(130,212)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 99

theorem band469_checked : band469.check rectangle=true := by decide +kernel
#print axioms band469_checked

def band470 : Band CellKey where
  qlo := (29/54)
  qhi := (2557/4752)
  mlo := (1339502332814930015552099533437/50000000000000000000000000000)
  mhi := (44985085483857897875987910014081/1000000000000000000000000000000)
  cells := [(99,157),(130,212)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 99

theorem band470_checked : band470.check rectangle=true := by decide +kernel
#print axioms band470_checked

def band471 : Band CellKey where
  qlo := (29/54)
  qhi := (2557/4752)
  mlo := (280833592534992223950233281493/8000000000000000000000000000)
  mhi := (44985085483857897875987910014081/1000000000000000000000000000000)
  cells := [(130,212)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 99

theorem band471_checked : band471.check rectangle=true := by decide +kernel
#print axioms band471_checked

def band472 : Band CellKey where
  qlo := (2557/4752)
  qhi := (427/792)
  mlo := (16693208430913348946135831381733/1000000000000000000000000000000)
  mhi := (44985085483857897875987910014081/1000000000000000000000000000000)
  cells := [(59,195),(99,157),(130,212)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 99

theorem band472_checked : band472.check rectangle=true := by decide +kernel
#print axioms band472_checked

def band473 : Band CellKey where
  qlo := (2557/4752)
  qhi := (427/792)
  mlo := (5564402810304449648711943793911/250000000000000000000000000000)
  mhi := (44985085483857897875987910014081/1000000000000000000000000000000)
  cells := [(80,182),(80,183),(80,184),(80,185),(99,157),(130,212)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 99

theorem band473_checked : band473.check rectangle=true := by decide +kernel
#print axioms band473_checked

def band474 : Band CellKey where
  qlo := (2557/4752)
  qhi := (427/792)
  mlo := (1339502332814930015552099533437/50000000000000000000000000000)
  mhi := (44985085483857897875987910014081/1000000000000000000000000000000)
  cells := [(99,157),(130,212)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 99

theorem band474_checked : band474.check rectangle=true := by decide +kernel
#print axioms band474_checked

def band475 : Band CellKey where
  qlo := (2557/4752)
  qhi := (427/792)
  mlo := (280833592534992223950233281493/8000000000000000000000000000)
  mhi := (44985085483857897875987910014081/1000000000000000000000000000000)
  cells := [(130,212)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 99

theorem band475_checked : band475.check rectangle=true := by decide +kernel
#print axioms band475_checked

def band476 : Band CellKey where
  qlo := (427/792)
  qhi := (2567/4752)
  mlo := (16660693416439423451499805220101/1000000000000000000000000000000)
  mhi := (44985085483857897875987910014081/1000000000000000000000000000000)
  cells := [(59,196),(99,157),(130,212)]
  lowerOrder := 59
  orderCap := 79
  rank := 18
  parentStrip := 99

theorem band476_checked : band476.check rectangle=true := by decide +kernel
#print axioms band476_checked

def band477 : Band CellKey where
  qlo := (427/792)
  qhi := (2567/4752)
  mlo := (22214257888585897935333073626801/1000000000000000000000000000000)
  mhi := (44985085483857897875987910014081/1000000000000000000000000000000)
  cells := [(80,186),(99,157),(130,212)]
  lowerOrder := 80
  orderCap := 98
  rank := 24
  parentStrip := 99

theorem band477_checked : band477.check rectangle=true := by decide +kernel
#print axioms band477_checked

def band478 : Band CellKey where
  qlo := (427/792)
  qhi := (2567/4752)
  mlo := (1339502332814930015552099533437/50000000000000000000000000000)
  mhi := (44985085483857897875987910014081/1000000000000000000000000000000)
  cells := [(99,157),(130,212)]
  lowerOrder := 99
  orderCap := 129
  rank := 29
  parentStrip := 99

theorem band478_checked : band478.check rectangle=true := by decide +kernel
#print axioms band478_checked

def band479 : Band CellKey where
  qlo := (427/792)
  qhi := (2567/4752)
  mlo := (280833592534992223950233281493/8000000000000000000000000000)
  mhi := (44985085483857897875987910014081/1000000000000000000000000000000)
  cells := [(130,212)]
  lowerOrder := 130
  orderCap := 169
  rank := 38
  parentStrip := 99

theorem band479_checked : band479.check rectangle=true := by decide +kernel
#print axioms band479_checked

end ForestUnimodality.IntermediateBridgeCoverData

